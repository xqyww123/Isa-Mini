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
import sys
import socket
from io import StringIO
from time import time
from typing import Any

import jsoncomment
import uvicorn
from mcp.server.lowlevel import Server as MCPServer
from mcp.server.streamable_http_manager import StreamableHTTPSessionManager
from mcp.types import Tool, ToolAnnotations, TextContent, CallToolResult

from .model import (
    the_session, _session_var, Session, MyIO,
    ImmediateAnswer, RaiseInteraction, Interaction,
    AoA_Error, InternalError, ArgumentError, IsabelleError,
    Parse_Node, parsing_node, _trivial_parsing, normalize_answer, Interaction_BadAnswer, ForkingMode,
    _Prompt, _Result, _handle_raise_interaction,
)
from .retrieval import (
    BATCHED_SEMANTIC_SEARCH,
    _query_tool_logic,
    _cc_query_schema,
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


# ============================================================================
# Tool Logic Helpers
# ============================================================================

async def _execute_proof_action(
    session: Session,
    action: str,
    step: str,
    pn: parsing_node,
    tool_name: str,
    log_prefix: str,
) -> tuple[str, bool]:
    """Execute a proof action with complete error handling.
    Returns (response_text, is_error) where is_error is True when the
    inserted/amended node's evaluation failed."""
    session.root.session.age += 1
    if not callable(pn):
        raise TypeError(f"parsing_node must be callable, got {type(pn)}")

    try:
        match action:
            case "fill":
                node, is_error, failure_reason = await session.root.fill(step, pn)
                session.refresh_YAML()
                if failure_reason is not None:
                    response = failure_reason.reason
                else:
                    response = await P.filled_step_message(step, session.root, node, session)
            case "insert_before":
                node, is_error, failure_reason = await session.root.insert_before(step, pn)
                session.refresh_YAML()
                if failure_reason is not None:
                    response = failure_reason.reason
                else:
                    response = await P.inserted_before_step_message(step, session.root, node, session)
            case "amend":
                node, is_error, failure_reason = await session.root.amend(step, pn)
                session.refresh_YAML()
                if failure_reason is not None:
                    response = failure_reason.reason
                else:
                    response = await P.amended_step_message(step, session.root, node, session)
            case _:
                raise ArgumentError({"action": action}, P.invalid_action_error(action))

        session.log_tool_response(tool_name, response)
        session.log_proof_tree_snapshot(f"{log_prefix}_step_{step}")
        return response, is_error

    except RaiseInteraction as e:
        original_kont = e.kontinuation
        async def wrapped_kont(results: list[Any]) -> tuple[str, bool]:
            result_gn = await original_kont(results)
            assert callable(result_gn), \
                "Continuation from _execute_proof_action must return gen_node (callable)"
            return await _execute_proof_action(
                session, action, step, _trivial_parsing(result_gn), tool_name, log_prefix) # type: ignore[arg-type]
        wrapped_e = RaiseInteraction(e.interactions, wrapped_kont)
        result = await _handle_raise_interaction(session, wrapped_e, tool_name)
        if isinstance(result, _Prompt):
            return result.text, False
        return result.value

    except AoA_Error as e:
        error_msg = str(e)
        session.log_tool_response(tool_name, f"ERROR: {error_msg}")
        return error_msg, True


# ============================================================================
# Permission Check (both modes)
# ============================================================================

_BLOCKED_DURING_INTERACTION = {"edit", "delete"}

def _check_tool_permission(session: Session, tool_name: str) -> str | None:
    """Check interaction state. Returns error message or None."""
    if session.working_interactions:
        if tool_name in _BLOCKED_DURING_INTERACTION:
            return "Pending interaction — use the answer tool first."
    elif tool_name == "answer":
        return "No pending interaction."
    return None


# ============================================================================
# Tool Logic Functions (shared, no framework dependency)
# ============================================================================

async def _edit_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    session.log_tool_call("mcp__proof__edit", args)
    try:
        step = args["target_step"]
        try:
            gn = Parse_Node(args["proof_operation"])
        except AoA_Error as e:
            error_msg = str(e)
            session.log_tool_response("mcp__proof__edit", f"ERROR: {error_msg}")
            return (error_msg, True)
        result, is_error = await _execute_proof_action(
            session, args["action"], step, gn,
            "mcp__proof__edit", "after_fill")
        return (result, is_error)
    except IsabelleError as e:
        error_msg = f"Isabelle error: {'; '.join(e.errors)}"
        session.log_tool_response("mcp__proof__edit", f"ERROR: {error_msg}")
        return (error_msg, True)
    except Exception as e:
        session.log_tool_response("mcp__proof__edit", f"UNEXPECTED ERROR: {type(e).__name__}: {e}")
        sys.exit(1)


async def _delete_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    session.log_tool_call("mcp__proof__delete", args)
    try:
        session.root.session.age += 1
        steps = args["target_steps"]
        try:
            not_found = await session.root.delete(steps)
            if len(not_found) == len(steps):
                noun = "step" if len(not_found) == 1 else "steps"
                error_msg = f"Error: {noun} {', '.join(not_found)} not found."
                session.log_tool_response("mcp__proof__delete", f"ERROR: {error_msg}")
                return (error_msg, True)
            deleted = [s for s in steps if s not in not_found]
            session.refresh_YAML()
            response = await P.deleted_steps_message(deleted, session.root, session)
            if not_found:
                noun = "step" if len(not_found) == 1 else "steps"
                response += f"\nWarning: {noun} {', '.join(not_found)} not found and skipped."
        except AoA_Error as e:
            error_msg = str(e)
            session.log_tool_response("mcp__proof__delete", f"ERROR: {error_msg}")
            return (error_msg, True)
        session.log_tool_response("mcp__proof__delete", response)
        session.log_proof_tree_snapshot("after_delete")
        return (response, False)
    except IsabelleError as e:
        error_msg = f"Isabelle error: {'; '.join(e.errors)}"
        session.log_tool_response("mcp__proof__delete", f"ERROR: {error_msg}")
        return (error_msg, True)
    except Exception as e:
        session.log_tool_response("mcp__proof__delete", f"UNEXPECTED ERROR: {type(e).__name__}: {e}")
        sys.exit(1)


async def _answer_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    session.log_tool_call("mcp__proof__answer", args)
    try:
        if not session.working_interactions:
            error_msg = "No pending interaction to answer"
            session.log_tool_response("mcp__proof__answer", f"ERROR: {error_msg}")
            return (error_msg, True)
        wi = session.working_interactions[-1]

        current_idx = None
        for i, inter in enumerate(wi.interactions):
            if wi.result_set[i] is False:
                current_idx = i
                break

        if current_idx is None:
            error_msg = "No pending interaction to answer"
            session.log_tool_response("mcp__proof__answer", f"ERROR: {error_msg}")
            return (error_msg, True)

        current_inter = wi.interactions[current_idx]
        normalized = normalize_answer(args.get("indexes"), args.get("text"))

        try:
            result = await current_inter.answer(normalized)
        except Interaction_BadAnswer as e:
            error_msg = str(e)
            session.log_tool_response("mcp__proof__answer", f"BAD ANSWER: {error_msg}")
            return (error_msg, True)
        except RaiseInteraction as e:
            r = await _handle_raise_interaction(session, e, "mcp__proof__answer")
            if isinstance(r, _Prompt):
                return (r.text, False)
            result = r.value

        wi.results[current_idx] = result
        wi.result_set[current_idx] = True
        n_done = sum(1 for f in wi.result_set if f is True)
        session.log_interaction("mcp__proof__answer",
            f"answered interaction {current_idx} ({n_done}/{len(wi.interactions)} done)")

        for i, inter in enumerate(wi.interactions):
            if wi.result_set[i] is False:
                buffer = StringIO()
                try:
                    await inter.prompt(0, MyIO(buffer))
                except ImmediateAnswer as imm:
                    wi.results[i] = imm.answer
                    wi.result_set[i] = True
                    continue
                session.log_tool_response("mcp__proof__answer", f"[INTERACTION PROMPT]\n{buffer.getvalue()}")
                return (buffer.getvalue(), False)

        session.log_interaction("continuation", "all interactions resolved")
        final = await wi.run_continuation()
        session.working_interactions.pop()
        session.log_tool_response("mcp__proof__answer", f"[INTERACTION RESOLVED] {final}")
        if not session.is_major:
            await session.interrupt()
        return (str(final), False)
    except IsabelleError as e:
        error_msg = f"Isabelle error: {'; '.join(e.errors)}"
        session.log_tool_response("mcp__proof__answer", f"ERROR: {error_msg}")
        return (error_msg, True)
    except Exception as e:
        session.log_tool_response("mcp__proof__answer", f"UNEXPECTED ERROR: {type(e).__name__}: {e}")
        sys.exit(1)


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
    _last_mutate_fail_time: float = 0.0

    # Build tool list: built-in + extras
    tools: list[Tool] = [
        Tool(name="edit",
             description="Edit the proof.yaml file",
             inputSchema=_cc_edit_schema,
             annotations=ToolAnnotations(readOnlyHint=False, destructiveHint=True, openWorldHint=False)),
        Tool(name="delete",
             description="Delete proof steps",
             inputSchema=_cc_delete_schema,
             annotations=ToolAnnotations(readOnlyHint=False, destructiveHint=True, openWorldHint=False)),
        Tool(name="answer",
             description="Answer a pending question",
             inputSchema=_cc_answer_schema,
             annotations=ToolAnnotations(readOnlyHint=False, destructiveHint=False, openWorldHint=False)),
        Tool(name="query",
             description="Search for Isabelle entities by semantic similarity, patterns, or exact name. Use exact_name to look up definitions; use long_description and filters for discovery.",
             inputSchema=_cc_query_schema,
             annotations=ToolAnnotations(readOnlyHint=True, destructiveHint=False, openWorldHint=False)),
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

    _SEARCH_HINT = (
        "\n\n---\n"
        "Hint: You've spent a while searching. What you need might not be "
        "in the library. Consider shifting focus to writing the proof."
    )
    _SEARCH_HINT_THRESHOLD = 180  # seconds

    @server.call_tool()
    async def call_tool(name: str, arguments: dict) -> CallToolResult:
        nonlocal _last_mutate_fail_time
        _session_var.set(session)

        # Permission check (both modes)
        perm_error = _check_tool_permission(session, name)
        if perm_error:
            return CallToolResult(
                content=[TextContent(type="text", text=perm_error)], isError=True)

        is_error = False
        _BATCH_CANCEL_MSG = "Cancelled: a prior edit/delete in this batch failed. Review the error before continuing."
        match name:
            case "edit":
                async with tool_lock:
                    if time() - _last_mutate_fail_time < 0.7:
                        result, is_error = _BATCH_CANCEL_MSG, True
                    else:
                        result, is_error = await _edit_tool_logic(session, arguments)
                        if is_error:
                            _last_mutate_fail_time = time()
                session.last_proof_op_time = time()
            case "delete":
                async with tool_lock:
                    if time() - _last_mutate_fail_time < 0.7:
                        result, is_error = _BATCH_CANCEL_MSG, True
                    else:
                        result, is_error = await _delete_tool_logic(session, arguments)
                        if is_error:
                            _last_mutate_fail_time = time()
                session.last_proof_op_time = time()
            case "answer":
                async with tool_lock:
                    result, is_error = await _answer_tool_logic(session, arguments)
            case "query":
                result, is_error = await _query_tool_logic(session, arguments)
            case _:
                handler = extra_handlers.get(name)
                if handler is not None:
                    ret = await handler(arguments)
                    content = ret.get("content", [])
                    return CallToolResult(
                        content=[TextContent(type="text", text=c.get("text", "")) for c in content])
                return CallToolResult(
                    content=[TextContent(type="text", text=f"Unknown tool: {name}")], isError=True)

        # Append search hint if agent has been searching without proof progress
        if name == "query" and not is_error:
            if time() - session.last_proof_op_time >= _SEARCH_HINT_THRESHOLD:
                result += _SEARCH_HINT

        return CallToolResult(
            content=[TextContent(type="text", text=result)], isError=is_error)

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
        self.sessions: dict[str, Session] = {}

    async def __call__(self, scope, receive, send):
        if scope["type"] not in ("http", "websocket"):
            return

        path: str = scope["path"]

        # Handle /reset_cache/<session_id> — clears view caches on context compaction
        if scope["type"] == "http" and path.startswith("/reset_cache/"):
            session_id = path[len("/reset_cache/"):]
            session = self.sessions.get(session_id)
            if session is not None:
                session.seen_commands.clear()
                session.seen_entities.clear()
                session.seen_opaque_note = False
                session.root.session.showed_suffices_notice = False
            await send({
                "type": "http.response.start",
                "status": 200,
                "headers": [(b"content-type", b"text/plain")],
            })
            await send({
                "type": "http.response.body",
                "body": b"OK",
            })
            return

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
        self._router.sessions[session_id] = session
        return f"http://127.0.0.1:{self._port}/mcp/{session_id}"

    async def unregister_session(self, session_id: str):
        app = self._router.apps.pop(session_id, None)
        self._router.sessions.pop(session_id, None)
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
