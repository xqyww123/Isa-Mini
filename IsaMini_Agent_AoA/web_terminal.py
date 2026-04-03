"""
Web terminal server for interactive proof sessions.

Serves xterm.js frontends that attach to existing tmux sessions.
Multiple browser tabs can attach to the same tmux session (shared display).
Started lazily as a singleton by the driver via ``WebTerminalServer.get_or_create()``.

Routes:
    GET  /{session_name}     — terminal HTML page
    GET  /{session_name}/ws  — WebSocket (attaches to tmux session)
"""

import asyncio
import fcntl
import json
import os
import pty
import signal
import struct
import subprocess
import sys
import termios

from aiohttp import web

# ============================================================================
# HTML Template
# ============================================================================

HTML_TEMPLATE = """<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<title>Terminal — {session_name}</title>
<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/@xterm/xterm@5.5.0/css/xterm.min.css">
<style>
  html, body {{ margin: 0; padding: 0; height: 100%; background: #1e1e1e; overflow: hidden; }}
  #terminal {{ height: 100%; width: 100%; }}
</style>
</head>
<body>
<div id="terminal"></div>
<script src="https://cdn.jsdelivr.net/npm/@xterm/xterm@5.5.0/lib/xterm.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/@xterm/addon-fit@0.10.0/lib/addon-fit.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/@xterm/addon-webgl@0.18.0/lib/addon-webgl.min.js"></script>
<script>
const term = new Terminal({{
  cursorBlink: true,
  fontSize: 14,
  fontFamily: "'JetBrains Mono', 'Fira Code', 'Cascadia Code', Menlo, monospace",
  theme: {{ background: '#1e1e1e', foreground: '#d4d4d4', cursor: '#d4d4d4' }},
}});

const fitAddon = new FitAddon.FitAddon();
term.loadAddon(fitAddon);
try {{
  const webglAddon = new WebglAddon.WebglAddon();
  webglAddon.onContextLoss(() => {{ webglAddon.dispose(); }});
  term.loadAddon(webglAddon);
}} catch (e) {{
  console.warn('WebGL addon failed, falling back to canvas:', e);
}}

term.open(document.getElementById('terminal'));
fitAddon.fit();

const proto = location.protocol === 'https:' ? 'wss:' : 'ws:';
const wsPath = location.pathname.replace(/\\/$/, '') + '/ws';
const ws = new WebSocket(`${{proto}}//${{location.host}}${{wsPath}}`);

ws.onopen = () => {{
  ws.send(JSON.stringify({{type: 'resize', cols: term.cols, rows: term.rows}}));
}};
ws.onmessage = (e) => {{ term.write(e.data); }};
ws.onclose = () => {{ term.write('\\r\\n[Connection closed]\\r\\n'); }};
term.onData((data) => {{ ws.readyState === 1 && ws.send(data); }});

const sendResize = () => {{
  fitAddon.fit();
  ws.readyState === 1 && ws.send(JSON.stringify({{type: 'resize', cols: term.cols, rows: term.rows}}));
}};
window.addEventListener('resize', sendResize);
new ResizeObserver(sendResize).observe(document.getElementById('terminal'));
</script>
</body>
</html>"""


# ============================================================================
# Route Handlers
# ============================================================================

async def _tmux_session_exists(name: str) -> bool:
    proc = await asyncio.create_subprocess_exec(
        'tmux', 'has-session', '-t', name,
        stdout=asyncio.subprocess.DEVNULL, stderr=asyncio.subprocess.DEVNULL)
    return (await proc.wait()) == 0


async def terminal_page(request: web.Request) -> web.Response:
    session_name = request.match_info['session_name']
    if not await _tmux_session_exists(session_name):
        return web.Response(
            text=f"Session '{session_name}' not found. Waiting for it to start...",
            status=404,
            content_type="text/plain")
    html = HTML_TEMPLATE.format(session_name=session_name)
    return web.Response(text=html, content_type="text/html")


async def websocket_handler(request: web.Request) -> web.WebSocketResponse:
    session_name = request.match_info['session_name']
    ws = web.WebSocketResponse()
    await ws.prepare(request)

    if not await _tmux_session_exists(session_name):
        await ws.send_str(f"\r\n[tmux session '{session_name}' not found]\r\n")
        await ws.close()
        return ws

    await _attach_tmux(ws, session_name)
    return ws


# ============================================================================
# tmux PTY Attachment
# ============================================================================

async def _attach_tmux(ws: web.WebSocketResponse, session_name: str):
    """Attach to an existing tmux session via a PTY and bridge to WebSocket."""
    master_fd, slave_fd = pty.openpty()

    env = os.environ.copy()
    env["TERM"] = "xterm-256color"
    env["COLORTERM"] = "truecolor"

    proc = subprocess.Popen(
        ['tmux', 'attach', '-t', session_name],
        stdin=slave_fd,
        stdout=slave_fd,
        stderr=slave_fd,
        preexec_fn=os.setsid,
        env=env,
    )
    os.close(slave_fd)

    loop = asyncio.get_event_loop()

    async def read_pty():
        try:
            while True:
                await asyncio.sleep(0)
                try:
                    data = await loop.run_in_executor(None, os.read, master_fd, 4096)
                except OSError:
                    break
                if not data:
                    break
                await ws.send_str(data.decode("utf-8", errors="replace"))
        except asyncio.CancelledError:
            pass

    reader_task = asyncio.ensure_future(read_pty())

    try:
        async for msg in ws:
            if msg.type == web.WSMsgType.TEXT:
                text = msg.data
                if text.startswith("{"):
                    try:
                        parsed = json.loads(text)
                        if parsed.get("type") == "resize":
                            winsize = struct.pack("HHHH", parsed["rows"], parsed["cols"], 0, 0)
                            fcntl.ioctl(master_fd, termios.TIOCSWINSZ, winsize)
                            continue
                    except (json.JSONDecodeError, KeyError):
                        pass
                os.write(master_fd, text.encode("utf-8"))
            elif msg.type in (web.WSMsgType.ERROR, web.WSMsgType.CLOSE):
                break
    finally:
        reader_task.cancel()
        try:
            os.close(master_fd)
        except OSError:
            pass
        try:
            os.kill(proc.pid, signal.SIGTERM)
            proc.wait(timeout=2)
        except (OSError, subprocess.TimeoutExpired):
            try:
                os.kill(proc.pid, signal.SIGKILL)
            except OSError:
                pass


# ============================================================================
# Application
# ============================================================================

def create_app() -> web.Application:
    app = web.Application()
    app.router.add_get('/{session_name}', terminal_page)
    app.router.add_get('/{session_name}/ws', websocket_handler)
    return app


# ============================================================================
# Singleton Server (for programmatic use from driver)
# ============================================================================

class WebTerminalServer:
    """Singleton web terminal server, started lazily with a random available port."""

    _instance: 'WebTerminalServer | None' = None
    _lock: asyncio.Lock = asyncio.Lock()

    def __init__(self, host: str = "127.0.0.1", port: int = 0):
        self._host = host
        self._port = port or self._find_free_port()
        self._runner: web.AppRunner | None = None

    @classmethod
    async def get_or_create(cls, host: str = "127.0.0.1", port: int = 0) -> 'WebTerminalServer':
        async with cls._lock:
            if cls._instance is None:
                cls._instance = cls(host, port)
                await cls._instance._start()
        return cls._instance

    @staticmethod
    def _find_free_port() -> int:
        import socket
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.bind(('127.0.0.1', 0))
            return s.getsockname()[1]

    @property
    def port(self) -> int:
        return self._port

    def session_url(self, session_name: str) -> str:
        return f"http://{self._host}:{self._port}/{session_name}"

    async def _start(self):
        app = create_app()
        self._runner = web.AppRunner(app)
        await self._runner.setup()
        site = web.TCPSite(self._runner, self._host, self._port)
        await site.start()

    async def shutdown(self):
        if self._runner is not None:
            await self._runner.cleanup()
            self._runner = None
        WebTerminalServer._instance = None


