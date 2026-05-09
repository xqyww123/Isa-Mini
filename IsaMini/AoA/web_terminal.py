"""
Web terminal server for interactive proof sessions.

Serves a split-view page: left is an xterm.js terminal (attached to tmux),
right is a live-updating proof.yaml viewer with YAML syntax highlighting
and folding at ``- step id:`` lines.  Updates are pushed via WebSocket
whenever the proof tree changes (no polling).

Started lazily as a singleton by the driver via ``WebTerminalServer.get_or_create()``.

Routes:
    GET  /{session_name}         — split-view HTML page
    GET  /{session_name}/ws      — WebSocket (attaches to tmux session)
    GET  /{session_name}/yaml    — current proof.yaml content (initial load)
    GET  /{session_name}/yaml-ws — WebSocket (receives YAML push updates)
"""

import asyncio
import fcntl
import json
import os
import pty
import signal
import struct
import subprocess
import termios

from aiohttp import web

# ============================================================================
# HTML Template — split view: terminal (left) + YAML viewer (right)
# ============================================================================

HTML_TEMPLATE = """<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<title>Proof — {session_name}</title>
<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/@xterm/xterm@5.5.0/css/xterm.min.css">
<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/codemirror@5.65.18/lib/codemirror.min.css">
<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/codemirror@5.65.18/addon/fold/foldgutter.min.css">
<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/codemirror@5.65.18/theme/material-darker.min.css">
<style>
  html, body {{ margin: 0; padding: 0; height: 100%; background: #1e1e1e; overflow: hidden; }}
  #container {{ display: flex; height: 100%; }}
  #terminal-pane {{ flex: 1; min-width: 0; height: 100%; }}
  #divider {{
    width: 5px; background: #333; cursor: col-resize; flex-shrink: 0;
  }}
  #divider:hover {{ background: #555; }}
  #yaml-pane {{
    flex: 1; min-width: 0; height: 100%;
    display: flex; flex-direction: column;
  }}
  .pane-header {{
    background: #252526; color: #888; font-size: 16px; padding: 4px 10px;
    font-family: 'JetBrains Mono', monospace; border-bottom: 1px solid #333;
    display: flex; justify-content: space-between; align-items: center;
    flex-shrink: 0;
  }}
  .pane-header .status {{ color: #4ec9b0; }}
  #top-editors {{ flex: 7; min-height: 0; position: relative; }}
  .editor-panel {{ position: absolute; top: 0; left: 0; right: 0; bottom: 0; display: none; }}
  .editor-panel.active {{ display: block; }}
  #h-divider {{
    height: 5px; background: #333; cursor: row-resize; flex-shrink: 0;
  }}
  #h-divider:hover {{ background: #555; }}
  #bottom-pane {{
    flex: 3; min-height: 0; display: flex; flex-direction: column;
  }}
  .tab-bar {{
    display: flex; background: #252526; border-top: 1px solid #333;
    flex-shrink: 0;
  }}
  .tab-bar .tab {{
    padding: 4px 14px; font-size: 16px; color: #888; cursor: pointer;
    font-family: 'JetBrains Mono', monospace; border-right: 1px solid #333;
  }}
  .tab-bar .tab.active {{ color: #ddd; background: #1a1a1a; }}
  .tab-bar .tab:hover {{ color: #ccc; }}
  .tab-content {{
    flex: 1; min-height: 0; overflow-y: auto; padding: 6px 10px;
    font-family: 'JetBrains Mono', monospace; font-size: 17px;
    color: #ccc; background: #1a1a1a; display: none;
  }}
  .tab-content.active {{ display: block; }}
  .tab-content .status-line {{ margin: 2px 0; }}
  .tab-content .running {{ color: #dcdcaa; }}
  .tab-content .success {{ color: #4ec9b0; }}
  .tab-content .failure {{ color: #f44747; }}
  .tab-content .log-line {{ margin: 1px 0; color: #999; white-space: pre-wrap; word-break: break-all; }}
  .tab-content .log-MODEL_OUTPUT {{ color: #d4d4d4; }}
  .tab-content .log-MODEL_THINKING {{ color: #9cdcfe; font-style: italic; }}
  .tab-content .log-TOOL_CALL {{ color: #dcdcaa; }}
  .tab-content .log-TOOL_RESPONSE {{ color: #4ec9b0; }}
  .tab-content .log-PROOF_OPERATION {{ color: #c586c0; }}
  .tab-content .log-OPERATION_ERROR {{ color: #f44747; }}
  .tab-content .log-DEBUG {{ color: #666; }}
  .tab-content .log-INTERACTION {{ color: #ce9178; }}
  .tab-content .log-PROMPT {{ color: #d7ba7d; }}
  .tab-content .retrieval-entry {{ margin: 6px 0; }}
  .tab-content .retrieval-query {{ color: #dcdcaa; font-weight: bold; }}
  .tab-content .retrieval-result {{ color: #4ec9b0; margin-left: 16px; }}
  #proof-result {{
    display: none; align-items: center; justify-content: center;
    height: 100%; font-size: 28px; font-weight: bold;
  }}
  #proof-result.show {{ display: flex; }}
  #proof-result.success {{ color: #4ec9b0; }}
  #proof-result.failure {{ color: #f44747; }}
  .CodeMirror {{
    height: 100% !important; font-size: 18px;
    font-family: 'JetBrains Mono', 'Fira Code', monospace;
  }}
  .yaml-flash {{
    animation: flash-fade 4s ease-out;
  }}
  @keyframes flash-fade {{
    0% {{ background: rgba(78, 201, 176, 0.4); }}
    30% {{ background: rgba(78, 201, 176, 0.3); }}
    100% {{ background: transparent; }}
  }}
  #readonly-toast {{
    position: fixed; top: 20px; left: 50%; transform: translateX(-50%);
    background: #333; color: #ddd; padding: 10px 20px; border-radius: 6px;
    font-family: 'JetBrains Mono', monospace; font-size: 17px;
    opacity: 0; transition: opacity 0.3s; pointer-events: none; z-index: 1000;
    max-width: 500px; text-align: center;
  }}
  #readonly-toast.show {{ opacity: 1; }}
  .terminal-flash {{
    animation: border-flash 1.5s ease-out;
  }}
  @keyframes border-flash {{
    from {{ box-shadow: inset 0 0 0 3px rgba(78, 201, 176, 0.8); }}
    to {{ box-shadow: inset 0 0 0 3px transparent; }}
  }}
</style>
</head>
<body>
<div id="readonly-toast">proof.yaml is read-only and can only be modified by the agent. If you want to guide the proof, interrupt Claude in the terminal on the left and type your instructions.</div>
<div id="container">
  <div id="terminal-pane"></div>
  <div id="divider"></div>
  <div id="yaml-pane">
    <div class="pane-header">
      <div class="tab-bar" id="top-tab-bar" style="background:transparent;border:none;">
        <div class="tab active" data-tab="yaml-editor">proof.yaml</div>
        <div class="tab" data-tab="quickview-editor">Quick Overview</div>
      </div>
      <span id="yaml-status" class="status">connecting...</span>
    </div>
    <div id="top-editors">
      <div id="yaml-editor" class="editor-panel active"></div>
      <div id="quickview-editor" class="editor-panel"></div>
    </div>
    <div id="h-divider"></div>
    <div id="bottom-pane">
      <div class="tab-bar" id="bottom-tab-bar">
        <div class="tab active" data-tab="status">Minilang Operation Execution</div>
        <div class="tab" data-tab="retrieval">Retrieval</div>
        <div class="tab" data-tab="logs">Logs</div>
      </div>
      <div id="status-panel" class="tab-content active">
        <div id="proof-result"></div>
      </div>
      <div id="retrieval-panel" class="tab-content"></div>
      <div id="logs-panel" class="tab-content"></div>
    </div>
  </div>
</div>

<script src="https://cdn.jsdelivr.net/npm/@xterm/xterm@5.5.0/lib/xterm.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/@xterm/addon-fit@0.10.0/lib/addon-fit.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/@xterm/addon-webgl@0.18.0/lib/addon-webgl.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/codemirror@5.65.18/lib/codemirror.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/codemirror@5.65.18/mode/yaml/yaml.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/codemirror@5.65.18/addon/fold/foldcode.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/codemirror@5.65.18/addon/fold/foldgutter.min.js"></script>
<script>
// ================================================================
// Terminal (left pane)
// ================================================================
const term = new Terminal({{
  cursorBlink: true, fontSize: 18,
  fontFamily: "'JetBrains Mono', 'Fira Code', 'Cascadia Code', Menlo, monospace",
  theme: {{ background: '#1e1e1e', foreground: '#d4d4d4', cursor: '#d4d4d4' }},
}});
const fitAddon = new FitAddon.FitAddon();
term.loadAddon(fitAddon);
try {{
  const wa = new WebglAddon.WebglAddon();
  wa.onContextLoss(() => wa.dispose());
  term.loadAddon(wa);
}} catch (e) {{}}

term.open(document.getElementById('terminal-pane'));
fitAddon.fit();

const proto = location.protocol === 'https:' ? 'wss:' : 'ws:';
const basePath = location.pathname.replace(/\\/$/, '');
const termWs = new WebSocket(`${{proto}}//${{location.host}}${{basePath}}/ws`);
termWs.onopen = () => {{
  termWs.send(JSON.stringify({{type: 'resize', cols: term.cols, rows: term.rows}}));
}};
termWs.onmessage = (e) => term.write(e.data);
termWs.onclose = () => term.write('\\r\\n[Connection closed]\\r\\n');
term.onData((data) => {{ termWs.readyState === 1 && termWs.send(data); }});

// ================================================================
// YAML viewer (right pane) — CodeMirror with step-based folding
// ================================================================
function stepFoldRangeFinder(cm, start) {{
  const line = cm.getLine(start.line);
  const match = line.match(/^(\\s*)- step id:/);
  if (!match) return null;
  const baseIndent = match[1].length;
  const lastLine = cm.lastLine();
  let end = start.line;
  for (let i = start.line + 1; i <= lastLine; i++) {{
    const next = cm.getLine(i);
    if (next.trim() === '') {{ end = i; continue; }}
    const nextIndent = next.match(/^(\\s*)/)[1].length;
    if (nextIndent <= baseIndent) break;
    end = i;
  }}
  if (end > start.line)
    return {{ from: CodeMirror.Pos(start.line, line.length),
              to: CodeMirror.Pos(end, cm.getLine(end).length) }};
  return null;
}}

const cmOpts = {{
  mode: 'yaml',
  theme: 'material-darker',
  readOnly: true,
  lineNumbers: true,
  foldGutter: {{ rangeFinder: stepFoldRangeFinder }},
  gutters: ['CodeMirror-linenumbers', 'CodeMirror-foldgutter'],
}};
const editor = CodeMirror(document.getElementById('yaml-editor'), cmOpts);
const qvEditor = CodeMirror(document.getElementById('quickview-editor'), cmOpts);

// Top tab switching
document.querySelectorAll('#top-tab-bar .tab').forEach(tab => {{
  tab.addEventListener('click', () => {{
    document.querySelectorAll('#top-tab-bar .tab').forEach(t => t.classList.remove('active'));
    document.querySelectorAll('.editor-panel').forEach(p => p.classList.remove('active'));
    tab.classList.add('active');
    document.getElementById(tab.dataset.tab).classList.add('active');
    // Refresh the now-visible editor so it renders correctly
    if (tab.dataset.tab === 'yaml-editor') editor.refresh();
    else qvEditor.refresh();
  }});
}});

// Read-only hint: show toast and flash terminal when user tries to type
let toastTimer = null;
function showReadonlyToast() {{
  const toast = document.getElementById('readonly-toast');
  toast.classList.add('show');
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => toast.classList.remove('show'), 4000);
  const tp = document.getElementById('terminal-pane');
  tp.classList.remove('terminal-flash');
  void tp.offsetWidth;
  tp.classList.add('terminal-flash');
}}
[editor, qvEditor].forEach(ed => {{
  ed.getWrapperElement().addEventListener('keydown', (e) => {{
    if (e.ctrlKey || e.metaKey || e.altKey) return;
    const nav = ['ArrowUp','ArrowDown','ArrowLeft','ArrowRight',
                 'Home','End','PageUp','PageDown','Escape','Tab',
                 'Shift','Control','Alt','Meta','CapsLock'];
    if (nav.includes(e.key)) return;
    showReadonlyToast();
  }});
}});

// ================================================================
// Live YAML updates via WebSocket + flash-highlight
// ================================================================

function findStepBlock(lines, lineIdx) {{
  // Walk up to find the enclosing "- step id:" line
  const lineIndent = (lines[lineIdx].match(/^(\\s*)/)||['',''])[1].length;
  let stepLine = lineIdx;
  for (let i = lineIdx; i >= 0; i--) {{
    if (/^\\s*- step id:/.test(lines[i])) {{
      const si = (lines[i].match(/^(\\s*)/)||['',''])[1].length;
      if (si <= lineIndent) {{ stepLine = i; break; }}
    }}
  }}
  // Walk down to find the end of this step block
  const baseIndent = (lines[stepLine].match(/^(\\s*)/)||['',''])[1].length;
  let endLine = stepLine;
  for (let i = stepLine + 1; i < lines.length; i++) {{
    if (lines[i].trim() === '') {{ endLine = i; continue; }}
    const ni = (lines[i].match(/^(\\s*)/)||['',''])[1].length;
    if (ni <= baseIndent) break;
    endLine = i;
  }}
  return [stepLine, endLine];
}}

function applyFlashHighlight(cm, oldText, newText) {{
  const oldLines = oldText.split('\\n');
  const newLines = newText.split('\\n');
  const changedLines = new Set();
  const maxLen = Math.max(oldLines.length, newLines.length);
  for (let i = 0; i < maxLen; i++) {{
    if ((oldLines[i] || '') !== (newLines[i] || '')) changedLines.add(i);
  }}
  if (changedLines.size === 0) return;
  const flashLines = new Set();
  for (const idx of changedLines) {{
    const [start, end] = findStepBlock(newLines, Math.min(idx, newLines.length - 1));
    for (let i = start; i <= end; i++) flashLines.add(i);
  }}
  for (const ln of flashLines) {{
    if (ln < cm.lineCount()) cm.addLineClass(ln, 'wrap', 'yaml-flash');
  }}
  setTimeout(() => {{
    for (const ln of flashLines) {{
      if (ln < cm.lineCount()) cm.removeLineClass(ln, 'wrap', 'yaml-flash');
    }}
  }}, 4200);
}}

function updateEditor(cm, lastRef, newText) {{
  if (newText === lastRef.val) return;
  const foldedLines = [];
  for (let i = 0; i < cm.lineCount(); i++) {{
    const marks = cm.findMarksAt(CodeMirror.Pos(i, 0));
    if (marks.some(m => m.__isFold)) foldedLines.push(i);
  }}
  const scroll = cm.getScrollInfo();
  const oldText = lastRef.val;
  cm.setValue(newText);
  lastRef.val = newText;
  applyFlashHighlight(cm, oldText, newText);
  for (const ln of foldedLines) {{
    if (ln < cm.lineCount()) {{
      const range = stepFoldRangeFinder(cm, CodeMirror.Pos(ln, 0));
      if (range) cm.foldCode(CodeMirror.Pos(ln, 0), {{ rangeFinder: stepFoldRangeFinder }});
    }}
  }}
  cm.scrollTo(scroll.left, scroll.top);
  document.getElementById('yaml-status').textContent = new Date().toLocaleTimeString();
}}

const lastYaml = {{ val: '' }};
const lastQv = {{ val: '' }};
function updateYaml(text) {{ updateEditor(editor, lastYaml, text); }}
function updateQuickview(text) {{ updateEditor(qvEditor, lastQv, text); }}

// ================================================================
// Tab switching (bottom)
// ================================================================
document.querySelectorAll('#bottom-tab-bar .tab').forEach(tab => {{
  tab.addEventListener('click', () => {{
    document.querySelectorAll('#bottom-tab-bar .tab').forEach(t => t.classList.remove('active'));
    document.querySelectorAll('#bottom-pane > .tab-content').forEach(c => c.classList.remove('active'));
    tab.classList.add('active');
    document.getElementById(tab.dataset.tab + '-panel').classList.add('active');
  }});
}});

// ================================================================
// Status panel + Logs panel
// ================================================================
const statusPanel = document.getElementById('status-panel');
const logsPanel = document.getElementById('logs-panel');
const retrievalPanel = document.getElementById('retrieval-panel');
const proofResult = document.getElementById('proof-result');

function appendStatus(msg) {{
  const div = document.createElement('div');
  const argsStr = msg.args != null ? ` ${{typeof msg.args === 'string' ? msg.args : JSON.stringify(msg.args)}}` : '';
  div.className = 'status-line';
  if (msg.state === 'running') {{
    div.className += ' running';
    div.id = `status-${{msg.step}}`;
    div.textContent = `\u25cb Running ${{msg.operation}}${{argsStr}} on step ${{msg.step}}...`;
  }} else {{
    const existing = document.getElementById(`status-${{msg.step}}`);
    const time = msg.time != null ? ` (${{msg.time.toFixed(1)}}s)` : '';
    if (msg.success) {{
      div.className += ' success';
      div.textContent = `\u2713 ${{msg.operation}}${{argsStr}}${{time}}`;
    }} else {{
      div.className += ' failure';
      div.textContent = `\u2717 ${{msg.operation}}${{argsStr}}${{time}}`;
    }}
    if (existing) existing.replaceWith(div);
    else statusPanel.insertBefore(div, proofResult);
    statusPanel.scrollTop = statusPanel.scrollHeight;
    return;
  }}
  statusPanel.insertBefore(div, proofResult);
  statusPanel.scrollTop = statusPanel.scrollHeight;
}}

const LOG_BUFFER_MAX = 2000;
function appendLog(msg) {{
  const div = document.createElement('div');
  const event = msg.event || '?';
  div.className = `log-line log-${{event}}`;
  const rest = Object.keys(msg).filter(k => k !== 'type' && k !== 'event')
    .map(k => `${{k}}=${{JSON.stringify(msg[k])}}`)
    .join(' ');
  div.textContent = `[${{event}}] ${{rest}}`;
  logsPanel.appendChild(div);
  // Trim old entries if buffer exceeds limit
  while (logsPanel.children.length > LOG_BUFFER_MAX) {{
    logsPanel.removeChild(logsPanel.firstChild);
  }}
  logsPanel.scrollTop = logsPanel.scrollHeight;
}}

function appendRetrieval(msg) {{
  const entry = document.createElement('div');
  entry.className = 'retrieval-entry';
  const q = document.createElement('div');
  q.className = 'retrieval-query';
  q.textContent = `Query: ${{msg.query}}`;
  entry.appendChild(q);
  for (const r of (msg.results || [])) {{
    const d = document.createElement('div');
    d.className = 'retrieval-result';
    d.textContent = r;
    entry.appendChild(d);
  }}
  retrievalPanel.appendChild(entry);
  retrievalPanel.scrollTop = retrievalPanel.scrollHeight;
}}

function showProofResult(success) {{
  proofResult.className = 'show ' + (success ? 'success' : 'failure');
  proofResult.textContent = success
    ? 'Proof completed successfully'
    : 'Proof incomplete';
  statusPanel.scrollTop = statusPanel.scrollHeight;
}}

// Initial load via HTTP, then switch to WebSocket for push updates
fetch(`${{basePath}}/yaml`).then(r => r.text()).then(updateYaml).catch(() => {{}});

const yamlWs = new WebSocket(`${{proto}}//${{location.host}}${{basePath}}/yaml-ws`);
yamlWs.onmessage = (e) => {{
  const msg = JSON.parse(e.data);
  switch (msg.type) {{
    case 'yaml': updateYaml(msg.content); break;
    case 'quickview': updateQuickview(msg.content); break;
    case 'status': appendStatus(msg); break;
    case 'retrieval': appendRetrieval(msg); break;
    case 'log': appendLog(msg); break;
    case 'proof_complete': showProofResult(msg.success); break;
  }}
}};
yamlWs.onopen = () => {{
  document.getElementById('yaml-status').textContent = 'connected';
}};
yamlWs.onclose = () => {{
  document.getElementById('yaml-status').textContent = 'disconnected';
}};

// ================================================================
// Resizable divider
// ================================================================
const divider = document.getElementById('divider');
const termPane = document.getElementById('terminal-pane');
const yamlPane = document.getElementById('yaml-pane');
let dragging = false;
divider.addEventListener('mousedown', (e) => {{ dragging = true; e.preventDefault(); }});

const hDivider = document.getElementById('h-divider');
const topEditors = document.getElementById('top-editors');
const bottomPane = document.getElementById('bottom-pane');
let hDragging = false;
hDivider.addEventListener('mousedown', (e) => {{ hDragging = true; e.preventDefault(); }});

document.addEventListener('mousemove', (e) => {{
  if (dragging) {{
    const cw = document.getElementById('container').clientWidth;
    const ratio = Math.max(0.15, Math.min(0.85, e.clientX / cw));
    termPane.style.flex = `${{ratio}}`;
    yamlPane.style.flex = `${{1 - ratio}}`;
    fitAddon.fit();
    editor.refresh();
    qvEditor.refresh();
  }}
  if (hDragging) {{
    const paneRect = yamlPane.getBoundingClientRect();
    const offset = e.clientY - paneRect.top;
    const paneHeight = paneRect.height;
    const ratio = Math.max(0.2, Math.min(0.9, offset / paneHeight));
    topEditors.style.flex = `${{ratio}}`;
    bottomPane.style.flex = `${{1 - ratio}}`;
    editor.refresh();
    qvEditor.refresh();
  }}
}});
document.addEventListener('mouseup', () => {{ dragging = false; hDragging = false; }});

// ================================================================
// Resize handling
// ================================================================
const sendResize = () => {{
  fitAddon.fit();
  termWs.readyState === 1 && termWs.send(
    JSON.stringify({{type: 'resize', cols: term.cols, rows: term.rows}}));
  editor.refresh();
  qvEditor.refresh();
}};
window.addEventListener('resize', sendResize);
new ResizeObserver(sendResize).observe(document.getElementById('terminal-pane'));
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
    # Always serve the HTML page — even after session ends, cached content is available
    html = HTML_TEMPLATE.format(session_name=session_name)
    return web.Response(text=html, content_type="text/html")


async def yaml_handler(request: web.Request) -> web.Response:
    """Return current proof.yaml content (used for initial load)."""
    session_name = request.match_info['session_name']
    path = request.app['yaml_paths'].get(session_name)
    if path and os.path.exists(path):
        with open(path, "r", encoding="utf-8") as f:
            return web.Response(text=f.read(), content_type="text/plain")
    # Fall back to cache (session may have ended but content preserved)
    cached = request.app['yaml_cache'].get(session_name)
    if cached:
        return web.Response(text=cached, content_type="text/plain")
    return web.Response(text="# proof.yaml not available yet\n",
                        content_type="text/plain")


async def yaml_ws_handler(request: web.Request) -> web.WebSocketResponse:
    """WebSocket that receives YAML push updates."""
    session_name = request.match_info['session_name']
    ws = web.WebSocketResponse()
    await ws.prepare(request)

    subscribers: dict[str, set[web.WebSocketResponse]] = request.app['yaml_subscribers']
    if session_name not in subscribers:
        subscribers[session_name] = set()
    subscribers[session_name].add(ws)

    try:
        # Send current content immediately as JSON (try file first, fall back to cache)
        yaml_content = None
        yaml_path = request.app['yaml_paths'].get(session_name)
        if yaml_path and os.path.exists(yaml_path):
            with open(yaml_path, "r", encoding="utf-8") as f:
                yaml_content = f.read()
        else:
            yaml_content = request.app['yaml_cache'].get(session_name)
        if yaml_content:
            await ws.send_str(json.dumps({"type": "yaml", "content": yaml_content}))

        qv_content = request.app['quickview_cache'].get(session_name)
        if qv_content:
            await ws.send_str(json.dumps({"type": "quickview", "content": qv_content}))

        # Keep connection alive until client disconnects
        async for msg in ws:
            pass  # client doesn't send anything; just wait for close
    finally:
        subscribers.get(session_name, set()).discard(ws)

    return ws


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
    app['yaml_paths'] = {}          # session_name → yaml file path
    app['yaml_subscribers'] = {}    # session_name → set[WebSocketResponse]
    app['yaml_cache'] = {}          # session_name → last yaml content (persists after session ends)
    app['quickview_cache'] = {}     # session_name → last quickview content (persists after session ends)
    app.router.add_get('/{session_name}', terminal_page)
    app.router.add_get('/{session_name}/ws', websocket_handler)
    app.router.add_get('/{session_name}/yaml', yaml_handler)
    app.router.add_get('/{session_name}/yaml-ws', yaml_ws_handler)
    return app


# ============================================================================
# Singleton Server
# ============================================================================

class WebTerminalServer:
    """Singleton web terminal server, started lazily with a random available port."""

    _instance: 'WebTerminalServer | None' = None
    _lock: asyncio.Lock = asyncio.Lock()

    def __init__(self, host: str = "127.0.0.1", port: int = 0):
        self._host = host
        self._port = port or self._find_free_port()
        self._runner: web.AppRunner | None = None
        self._app: web.Application | None = None

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

    def register_yaml(self, session_name: str, yaml_path: str):
        """Register the proof.yaml path for a session."""
        if self._app is not None:
            self._app['yaml_paths'][session_name] = yaml_path

    def unregister_yaml(self, session_name: str):
        """Unregister paths and close any YAML WebSocket subscribers."""
        if self._app is not None:
            self._app['yaml_paths'].pop(session_name, None)
            self._app['yaml_subscribers'].pop(session_name, None)

    async def _broadcast(self, session_name: str, message: str):
        """Send a message to all YAML WebSocket subscribers for a session."""
        if self._app is None:
            return
        subscribers = self._app['yaml_subscribers'].get(session_name, set())
        dead: list[web.WebSocketResponse] = []
        for ws in subscribers:
            try:
                await ws.send_str(message)
            except (ConnectionError, RuntimeError):
                dead.append(ws)
        for ws in dead:
            subscribers.discard(ws)

    async def notify_yaml_update(self, session_name: str, quickview: str = ""):
        """Read proof.yaml and push it with quickview to all WebSocket subscribers."""
        if self._app is None:
            return
        yaml_path = self._app['yaml_paths'].get(session_name)
        if yaml_path and os.path.exists(yaml_path):
            with open(yaml_path, "r", encoding="utf-8") as f:
                content = f.read()
            self._app['yaml_cache'][session_name] = content
            await self._broadcast(session_name, json.dumps({"type": "yaml", "content": content}))
        if quickview:
            self._app['quickview_cache'][session_name] = quickview
            await self._broadcast(session_name, json.dumps({"type": "quickview", "content": quickview}))

    async def notify_status(self, session_name: str, msg: dict):
        """Push a status message (operation start/end, proof_complete) to subscribers."""
        await self._broadcast(session_name, json.dumps(msg))

    async def _start(self):
        self._app = create_app()
        self._runner = web.AppRunner(self._app)
        await self._runner.setup()
        site = web.TCPSite(self._runner, self._host, self._port)
        await site.start()

    async def shutdown(self):
        if self._runner is not None:
            await self._runner.cleanup()
            self._runner = None
        self._app = None
        WebTerminalServer._instance = None
