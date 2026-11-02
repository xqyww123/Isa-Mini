"""AoA's MCP server over HTTP (`ProofMCPHTTPServer`, `_create_mcp_server`),
driven by the `mcp` client in both MCP eras: the handshake (`initialize`)
and 2026-07-28 (`server/discover`).  Results are read in the wire form.
No Isabelle, no REPL, no model: the tools' work is a stand-in.
Run: python -m pytest IsaMini/AoA/test_mcp_transport.py
"""

import asyncio
from types import SimpleNamespace

import jsonschema
import pytest
from mcp import ClientSession
from mcp.client.streamable_http import streamable_http_client

from IsaMini.AoA.mcp_http_server import ProofMCPHTTPServer, ToolExecutor, _tool_schemas_for
from IsaMini.AoA.model import Role_Major, Runtime, Session

ERAS = ["handshake", "2026-07-28"]


def main_session() -> Session:
    """A main agent's session with only what the server reads of it."""
    session = Session.__new__(Session)
    session.runtime = Runtime()
    session.role = Role_Major()
    session.parent = None
    session._nf_pending_interaction = None
    return session


def wire(model) -> dict:
    return model.model_dump(by_alias=True, mode="json", exclude_none=True)


async def served(session: Session, era: str, calls):
    """`session` registered on a server of its own, a client opened on its
    endpoint in `era`; `calls(client)`'s value, the session unregistered
    and the server shut down after."""
    server = ProofMCPHTTPServer()
    await server._ensure_serving()
    try:
        url = await server.register_session("1", session)
        assert url == f"http://127.0.0.1:{server.port}/mcp/1"
        try:
            async with streamable_http_client(url) as (read, write, *_), \
                    ClientSession(read, write) as client:
                await (client.initialize() if era == "handshake" else client.discover())
                return await calls(client)
        finally:
            await server.unregister_session("1")
    finally:
        await server.shutdown()


@pytest.fixture
def executed(monkeypatch):
    """The executor's work stood in for: `recall_removed` raises, every
    other tool answers two lines; every call is recorded."""
    seen = []

    async def execute(self, name, arguments):
        seen.append((name, arguments))
        if name == "recall_removed":
            raise RuntimeError("the tool broke")
        return f"done {name}\nsecond line", False
    monkeypatch.setattr(ToolExecutor, "execute", execute)
    return seen


@pytest.mark.parametrize("era", ERAS)
def test_tools_list_is_what_the_session_is_advertised(era):
    """Each tool `_tool_schemas_for` advertises, with its description,
    schema and annotations as they are — none rewritten on the way."""
    session = main_session()

    async def listed(client):
        return [wire(tool) for tool in (await client.list_tools()).tools]
    tools = asyncio.run(served(session, era, listed))
    advertised = _tool_schemas_for(session)
    assert [t["name"] for t in tools] == list(advertised)
    for t in tools:
        a = advertised[t["name"]]
        assert (t["description"], t["inputSchema"], t["annotations"]) == (
            a["description"], a["schema"], wire(a["annotations"]))


@pytest.mark.parametrize("era", ERAS)
def test_a_call_is_answered_its_tools_text_or_its_error(era, executed):
    """A valid call is answered the tool's text, `isError` false; invalid
    arguments the SDK's `Input validation error: …`, the executor not
    reached; a tool that raises its exception's text, `isError` true."""
    session = main_session()
    schema = _tool_schemas_for(session)["recall"]["schema"]
    invalid = {"no such argument": 1}
    with pytest.raises(jsonschema.ValidationError) as caught:
        jsonschema.validate(invalid, schema)

    async def calls(client):
        return [wire(await client.call_tool("recall", {})),
                wire(await client.call_tool("recall", invalid)),
                wire(await client.call_tool("recall_removed", {}))]
    valid, refused, broken = asyncio.run(served(session, era, calls))
    assert (valid["content"], valid.get("isError", False)) == (
        [{"type": "text", "text": "done recall\nsecond line"}], False)
    assert (refused["content"], refused["isError"]) == (
        [{"type": "text", "text": f"Input validation error: {caught.value.message}"}], True)
    assert (broken["content"], broken["isError"]) == ([{"type": "text", "text": "the tool broke"}], True)
    assert executed == [("recall", {}), ("recall_removed", {})]


@pytest.mark.parametrize("era", ERAS)
def test_a_listed_tool_the_session_may_not_call_is_refused(era, executed):
    """A call `_check_tool_permission` refuses — here another answer tool
    than the pending question's — is answered its refusal, `isError` true,
    and never reaches the executor."""
    session = main_session()
    session._nf_pending_interaction = SimpleNamespace(  # type: ignore[assignment]
        answer_tool_name="answer_index", fork_allowed_tools=())

    async def calls(client):
        return wire(await client.call_tool("answer_refutation", {"accept": True, "reason": "a stand-in"}))
    refused = asyncio.run(served(session, era, calls))
    assert (refused["content"], refused["isError"]) == (
        [{"type": "text", "text": "Wrong answer tool. Use `answer_index` to answer the current question."}], True)
    assert executed == []
