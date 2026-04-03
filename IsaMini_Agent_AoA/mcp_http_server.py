"""
Singleton multi-session MCP HTTP server for proof tools.

Architecture:
- One HTTP server, one port, multiple proof sessions on different URL paths
- Each session (including forks) gets its own endpoint: /mcp/<session_id>
- Each endpoint has its own low-level mcp.server.Server with hand-written schemas
- Tool handlers close over their Session instance and set _session_var per-request
- Both embedded (Agent SDK) and standalone (CLI in tmux) modes connect via HTTP URL

Usage:
    server = await ProofMCPHTTPServer.get_or_create()
    url = await server.register_session("my_session_id", session)
    # Claude Code connects to url via --mcp-config
    await server.unregister_session("my_session_id")
"""

from __future__ import annotations

import asyncio
import os
import socket
from io import StringIO
from typing import Any, NamedTuple

import jsoncomment
import uvicorn
from mcp.server.lowlevel import Server as MCPServer
from mcp.server.streamable_http_manager import StreamableHTTPSessionManager
from mcp.types import Tool, TextContent

from .model import (
    the_session, _session_var, Session, MyIO,
    RaiseInteraction, Working_Interactions, Interaction,
    AoA_Error, InternalError, ArgumentError, IsabelleError,
    Parse_Node, gen_node, normalize_answer, Interaction_BadAnswer,
    EntityKind,
)
from . import prompts as P


# ============================================================================
# Schema Loading
# ============================================================================

_current_dir = os.path.dirname(os.path.abspath(__file__))
_json = jsoncomment.JsonComment()

def _load_schema(filename: str) -> dict:
    with open(os.path.join(_current_dir, "tools", filename), "r", encoding="utf-8") as f:
        return _json.load(f)

_cc_edit_schema = _load_schema("cc_edit.jsonc")
_cc_answer_schema = _load_schema("cc_answer.jsonc")
_cc_delete_schema = _load_schema("cc_delete.jsonc")
_cc_semantic_search_schema = _load_schema("cc_semantic_search.jsonc")


# ============================================================================
# Tool Logic Helpers
# ============================================================================

class _Prompt(NamedTuple):
    """A prompt string to return to the LLM."""
    text: str

class _Result(NamedTuple):
    """A resolved result (gen_node or Any)."""
    value: Any


async def _handle_raise_interaction(
    session: Session,
    e: RaiseInteraction,
    tool_name: str,
) -> '_Prompt | _Result':
    """Dispatch a RaiseInteraction. Returns _Prompt (for LLM) or _Result (all done)."""
    wi = Working_Interactions(
        interactions=e.interactions,
        results=[None] * len(e.interactions),
        result_set=[False] * len(e.interactions),
        kontinuation=e.kontinuation,
    )
    session.working_interactions.append(wi)
    n_forking = sum(1 for inter in e.interactions if inter.forking)
    n_inline = len(e.interactions) - n_forking
    session.log_interaction(tool_name,
        f"{len(e.interactions)} interactions ({n_forking} forking, {n_inline} inline)")

    # 1. Launch forking interactions as background tasks (don't await yet)
    forking = [(i, inter) for i, inter in enumerate(e.interactions) if inter.forking]
    if forking:
        session._launch_forks(forking, wi)

    # 2. Find first unfinished non-forking interaction
    for i, inter in enumerate(wi.interactions):
        if wi.result_set[i] is False:
            buffer = StringIO()
            inter.prompt(0, MyIO(buffer))
            session.log_tool_response(tool_name, f"[INTERACTION PROMPT]\n{buffer.getvalue()}")
            return _Prompt(buffer.getvalue())

    # 3. All non-forking done — await forks and call continuation
    session.log_interaction("continuation", "all interactions resolved")
    try:
        result = await wi.run_continuation()
    except RaiseInteraction as nested:
        session.working_interactions.pop()
        return await _handle_raise_interaction(session, nested, tool_name)
    session.working_interactions.pop()
    session.log_tool_response(tool_name, f"[INTERACTION RESOLVED] {result}")
    return _Result(result)


async def _execute_proof_action(
    session: Session,
    action: str,
    step: str,
    gn: gen_node,
    tool_name: str,
    log_prefix: str,
) -> str:
    """Execute a proof action with complete error handling."""
    session.root.session.age += 1
    if not callable(gn):
        raise TypeError(f"gen_node must be callable, got {type(gn)}")

    try:
        match action:
            case "fill":
                node = await session.root.fill(step, gn)
                session.refresh_YAML()
                response = await P.filled_step_message(step, session.root, node, session)
            case "insert_before":
                node = await session.root.insert_before(step, gn)
                session.refresh_YAML()
                response = await P.inserted_before_step_message(step, session.root, node, session)
            case "amend":
                node = await session.root.amend(step, gn)
                session.refresh_YAML()
                response = await P.amended_step_message(step, session.root, node, session)
            case _:
                raise ArgumentError({"action": action}, P.invalid_action_error(action))

        session.log_tool_response(tool_name, response)
        session.log_proof_tree_snapshot(f"{log_prefix}_step_{step}")
        return response

    except RaiseInteraction as e:
        original_kont = e.kontinuation
        async def wrapped_kont(results: list[Any]) -> Any:
            result_gn = await original_kont(results)
            assert callable(result_gn), \
                "Continuation from _execute_proof_action must return gen_node (callable)"
            return await _execute_proof_action(
                session, action, step, result_gn, tool_name, log_prefix) # type: ignore[arg-type]
        wrapped_e = RaiseInteraction(e.interactions, wrapped_kont)
        result = await _handle_raise_interaction(session, wrapped_e, tool_name)
        if isinstance(result, _Prompt):
            return result.text
        return result.value

    except AoA_Error as e:
        error_msg = str(e)
        session.log_tool_response(tool_name, f"ERROR: {error_msg}")
        return error_msg


# ============================================================================
# Permission Check (both modes)
# ============================================================================

def _check_tool_permission(session: Session, tool_name: str) -> str | None:
    """Check interaction state. Returns error message or None."""
    if session.working_interactions:
        if tool_name != "answer":
            return "Pending interaction — use the answer tool first."
    elif tool_name == "answer":
        return "No pending interaction."
    return None


# ============================================================================
# Tool Logic Functions (shared, no framework dependency)
# ============================================================================

async def _edit_tool_logic(session: Session, args: dict) -> str:
    session.log_tool_call("mcp__proof__edit", args)
    try:
        step = args["target_step"]
        try:
            gn = Parse_Node(args["proof_operation"])
        except AoA_Error as e:
            error_msg = str(e)
            session.log_tool_response("mcp__proof__edit", f"ERROR: {error_msg}")
            return error_msg
        return await _execute_proof_action(
            session, args["action"], step, gn,
            "mcp__proof__edit", "after_fill")
    except Exception as e:
        session.log_tool_response("mcp__proof__edit", f"UNEXPECTED ERROR: {type(e).__name__}: {e}")
        os._exit(1)


async def _delete_tool_logic(session: Session, args: dict) -> str:
    session.log_tool_call("mcp__proof__delete", args)
    try:
        session.root.session.age += 1
        steps = args["target_steps"]
        try:
            not_found = await session.root.delete(steps)
            session.refresh_YAML()
            response = await P.deleted_steps_message(steps, session.root, session)
            if not_found:
                noun = "step" if len(not_found) == 1 else "steps"
                response += f"\nWarning: {noun} {', '.join(not_found)} not found and skipped."
        except AoA_Error as e:
            error_msg = str(e)
            session.log_tool_response("mcp__proof__delete", f"ERROR: {error_msg}")
            return error_msg
        session.log_tool_response("mcp__proof__delete", response)
        session.log_proof_tree_snapshot("after_delete")
        return response
    except Exception as e:
        session.log_tool_response("mcp__proof__delete", f"UNEXPECTED ERROR: {type(e).__name__}: {e}")
        os._exit(1)


async def _answer_tool_logic(session: Session, args: dict) -> str:
    session.log_tool_call("mcp__proof__answer", args)
    try:
        if not session.working_interactions:
            error_msg = "No pending interaction to answer"
            session.log_tool_response("mcp__proof__answer", f"ERROR: {error_msg}")
            return error_msg
        wi = session.working_interactions[-1]

        current_idx = None
        for i, inter in enumerate(wi.interactions):
            if wi.result_set[i] is False:
                current_idx = i
                break

        if current_idx is None:
            error_msg = "No pending interaction to answer"
            session.log_tool_response("mcp__proof__answer", f"ERROR: {error_msg}")
            return error_msg

        current_inter = wi.interactions[current_idx]
        normalized = normalize_answer(args.get("indexes"), args.get("text"))

        try:
            result = await current_inter.answer(normalized)
        except Interaction_BadAnswer as e:
            error_msg = str(e)
            session.log_tool_response("mcp__proof__answer", f"BAD ANSWER: {error_msg}")
            return error_msg
        except RaiseInteraction as e:
            r = await _handle_raise_interaction(session, e, "mcp__proof__answer")
            if isinstance(r, _Prompt):
                return r.text
            result = r.value

        wi.results[current_idx] = result
        wi.result_set[current_idx] = True
        n_done = sum(1 for f in wi.result_set if f is True)
        session.log_interaction("mcp__proof__answer",
            f"answered interaction {current_idx} ({n_done}/{len(wi.interactions)} done)")

        for i, inter in enumerate(wi.interactions):
            if wi.result_set[i] is False:
                buffer = StringIO()
                inter.prompt(0, MyIO(buffer))
                session.log_tool_response("mcp__proof__answer", f"[INTERACTION PROMPT]\n{buffer.getvalue()}")
                return buffer.getvalue()

        session.log_interaction("continuation", "all interactions resolved")
        final = await wi.run_continuation()
        session.working_interactions.pop()
        session.log_tool_response("mcp__proof__answer", f"[INTERACTION RESOLVED] {final}")
        if not session.is_major:
            await session.interrupt()
        return str(final)
    except Exception as e:
        session.log_tool_response("mcp__proof__answer", f"UNEXPECTED ERROR: {type(e).__name__}: {e}")
        os._exit(1)


async def _semantic_search_tool_logic(session: Session, args: dict) -> str:
    session.log_tool_call("mcp__proof__semantic_search", args)
    try:
        query = args.get("query", None)
        k = args.get("k", 10)
        try:
            kinds = [EntityKind.from_label(label) for label in args["kinds"]]
        except KeyError as e:
            return f"Invalid entity kind: {e}"

        term_patterns = args.get("term_patterns", [])
        type_patterns = args.get("type_patterns", [])
        theories_include = args.get("theories_include", [])
        name_contains = args.get("name_contains", [])

        ml_state = session.root.ml_state
        fetch_k = max(k, 50)
        results, warnings = await ml_state.semantic_knn(
            query, fetch_k, kinds,
            term_patterns=term_patterns,
            type_patterns=type_patterns,
            theories_include=theories_include,
            name_contains=name_contains)

        lines: list[str] = []
        for w in warnings:
            lines.append(f"Warning: {w}")
        if not results:
            lines.append("No matching entities found.")
            return "\n".join(lines)

        if len(results) >= 50:
            n_above_07 = sum(1 for s, _ in results if s > 0.7)
            n_above_06 = sum(1 for s, _ in results if s > 0.6)
            last_score = results[-1][0]
            if last_score > 0.5 or n_above_06 > 20 or n_above_07 > 10:
                session.log_interaction("mcp__proof__semantic_search",
                    f"not distinctive: last_score={last_score:.2f}, n_above_06={n_above_06}, n_above_07={n_above_07}")
                lines.append("Hint: Results not distinctive enough \u2014 too many high-similarity hits. "
                             "Try narrowing with term_patterns, type_patterns, or theories_include.")
        for score, rec in results[:k]:
            lines.append(f"- [{score:.2f}] {rec.pretty_print}")
            if rec.interpretation:
                lines.append(f"  {rec.interpretation}")
        return "\n".join(lines)
    except IsabelleError as e:
        error_msg = "\n".join(e.errors)
        session.log_tool_response("mcp__proof__semantic_search", f"ERROR: {error_msg}")
        return error_msg
    except Exception as e:
        session.log_tool_response("mcp__proof__semantic_search", f"UNEXPECTED ERROR: {type(e).__name__}: {e}")
        os._exit(1)


# ============================================================================
# Per-Session MCP Server Creation
# ============================================================================

def _create_mcp_server(session: Session, extra_sdk_tools: list | None = None) -> MCPServer:
    """Create a low-level MCP Server with tools bound to ``session`` via closure.

    ``extra_sdk_tools`` can carry ``SdkMcpTool`` instances (e.g. from
    Isabelle_Semantic_Embedding) whose schemas and handlers are extracted
    and registered alongside the built-in proof tools.
    """
    server = MCPServer(f"proof-{id(session)}")
    tool_lock = asyncio.Lock()  # serialize tool calls per session

    # Build tool list: built-in + extras
    tools: list[Tool] = [
        Tool(name="edit",
             description="Edit the proof.yaml file",
             inputSchema=_cc_edit_schema),
        Tool(name="delete",
             description="Delete proof steps",
             inputSchema=_cc_delete_schema),
        Tool(name="answer",
             description="Answer a pending question",
             inputSchema=_cc_answer_schema),
        Tool(name="semantic_search",
             description="Search for Isabelle entities by English description.",
             inputSchema=_cc_semantic_search_schema),
    ]

    # Extract schema/handler from SdkMcpTool extras
    extra_handlers: dict[str, Any] = {}
    if extra_sdk_tools:
        for sdk_tool in extra_sdk_tools:
            schema = sdk_tool.input_schema if isinstance(sdk_tool.input_schema, dict) else {}
            tools.append(Tool(
                name=sdk_tool.name,
                description=sdk_tool.description,
                inputSchema=schema,
            ))
            extra_handlers[sdk_tool.name] = sdk_tool.handler

    @server.list_tools()
    async def list_tools() -> list[Tool]:
        return tools

    @server.call_tool()
    async def call_tool(name: str, arguments: dict) -> list[TextContent]:
        _session_var.set(session)

        # Permission check (both modes)
        perm_error = _check_tool_permission(session, name)
        if perm_error:
            return [TextContent(type="text", text=perm_error)]

        match name:
            case "edit":
                async with tool_lock:
                    result = await _edit_tool_logic(session, arguments)
            case "delete":
                async with tool_lock:
                    result = await _delete_tool_logic(session, arguments)
            case "answer":
                async with tool_lock:
                    result = await _answer_tool_logic(session, arguments)
            case "semantic_search":
                result = await _semantic_search_tool_logic(session, arguments)
            case _:
                handler = extra_handlers.get(name)
                if handler is not None:
                    ret = await handler(arguments)
                    content = ret.get("content", [])
                    return [TextContent(type="text", text=c.get("text", "")) for c in content]
                return [TextContent(type="text", text=f"Unknown tool: {name}")]

        return [TextContent(type="text", text=result)]

    return server


# ============================================================================
# Streamable HTTP App from Low-Level Server
# ============================================================================

class _ManagedMCPApp:
    """ASGI app wrapping a low-level MCP Server with StreamableHTTPSessionManager.

    The manager's ``run()`` context uses anyio task groups internally, so its
    lifecycle must stay within a single asyncio task.  We spawn a dedicated
    background task that keeps the manager alive.
    """

    def __init__(self, mcp_server: MCPServer):
        self._manager = StreamableHTTPSessionManager(app=mcp_server, stateless=False)
        self._task: asyncio.Task | None = None
        self._ready = asyncio.Event()
        self._stop_event = asyncio.Event()

    async def start(self):
        self._start_error: BaseException | None = None

        async def _run():
            try:
                async with self._manager.run():
                    self._ready.set()
                    await self._stop_event.wait()
            except BaseException as e:
                self._start_error = e
                self._ready.set()  # unblock start() so it can raise
                raise

        self._task = asyncio.create_task(_run())
        await self._ready.wait()
        if self._start_error is not None:
            raise self._start_error

    async def stop(self):
        if self._task is not None:
            self._stop_event.set()
            try:
                await self._task
            except Exception:
                pass
            self._task = None

    async def __call__(self, scope, receive, send):
        """ASGI interface — delegates to StreamableHTTPSessionManager.handle_request."""
        if scope["type"] in ("http", "websocket"):
            await self._manager.handle_request(scope, receive, send)


# ============================================================================
# ASGI Session Router
# ============================================================================

class _SessionRouter:
    """ASGI middleware that dispatches /mcp/<session_id>/... to per-session apps."""

    def __init__(self):
        self.apps: dict[str, _ManagedMCPApp] = {}

    async def __call__(self, scope, receive, send):
        if scope["type"] not in ("http", "websocket"):
            return

        path: str = scope["path"]
        for session_id, app in list(self.apps.items()):
            prefix = f"/mcp/{session_id}"
            if path == prefix or path.startswith(prefix + "/"):
                inner_scope = dict(scope)
                inner_scope["path"] = path[len(prefix):] or "/"
                inner_scope["root_path"] = scope.get("root_path", "") + prefix
                await app(inner_scope, receive, send)
                return

        # 404
        if scope["type"] == "http":
            await send({
                "type": "http.response.start",
                "status": 404,
                "headers": [(b"content-type", b"text/plain")],
            })
            await send({
                "type": "http.response.body",
                "body": b"Session not found",
            })


# ============================================================================
# Singleton Multi-Session HTTP Server
# ============================================================================

class ProofMCPHTTPServer:
    """Singleton HTTP server hosting multiple proof sessions on different endpoints."""

    _instance: 'ProofMCPHTTPServer | None' = None
    _lock: asyncio.Lock = asyncio.Lock()

    def __init__(self, port: int = 0):
        self._port = port or self._find_free_port()
        self._router = _SessionRouter()
        self._server: uvicorn.Server | None = None
        self._serve_task: asyncio.Task | None = None
        self._next_id = 0

    def allocate_session_id(self) -> str:
        """Return a short, unique session ID (for HTTP routing, not Claude --session-id)."""
        self._next_id += 1
        return str(self._next_id)

    @classmethod
    async def get_or_create(cls, port: int = 0) -> 'ProofMCPHTTPServer':
        async with cls._lock:
            if cls._instance is None:
                cls._instance = cls(port)
            await cls._instance._ensure_serving()
        return cls._instance

    @staticmethod
    def _find_free_port() -> int:
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.bind(('127.0.0.1', 0))
            return s.getsockname()[1]

    @property
    def port(self) -> int:
        return self._port

    async def register_session(self, session_id: str, session: Session,
                               extra_sdk_tools: list | None = None) -> str:
        """Register a proof session. Returns its MCP endpoint URL."""
        mcp_server = _create_mcp_server(session, extra_sdk_tools=extra_sdk_tools)
        app = _ManagedMCPApp(mcp_server)
        await app.start()
        self._router.apps[session_id] = app
        return f"http://127.0.0.1:{self._port}/mcp/{session_id}"

    async def unregister_session(self, session_id: str):
        app = self._router.apps.pop(session_id, None)
        if app is not None:
            await app.stop()

    def mcp_config_json(self, session_id: str) -> dict:
        """Return JSON config suitable for Claude CLI --mcp-config."""
        return {
            "mcpServers": {
                "proof": {
                    "type": "http",
                    "url": f"http://127.0.0.1:{self._port}/mcp/{session_id}",
                }
            }
        }

    async def _ensure_serving(self):
        """Start the HTTP server if not already running."""
        if self._serve_task is not None:
            if self._serve_task.done():
                # Previous attempt failed — reset and retry
                self._serve_task = None
                self._server = None
            else:
                return
        config = uvicorn.Config(
            self._router,
            host="127.0.0.1",
            port=self._port,
            log_level="warning",
        )
        self._server = uvicorn.Server(config)
        self._serve_task = asyncio.create_task(self._server.serve())
        # Give uvicorn a moment to bind
        await asyncio.sleep(0.5)
        # Check if server failed to start
        if self._serve_task.done():
            exc = self._serve_task.exception()
            self._serve_task = None
            self._server = None
            if exc is not None:
                raise exc

    async def shutdown(self):
        """Shut down the HTTP server."""
        if self._server is not None:
            self._server.should_exit = True
        if self._serve_task is not None:
            await self._serve_task
        self._serve_task = None
        self._server = None
        ProofMCPHTTPServer._instance = None
