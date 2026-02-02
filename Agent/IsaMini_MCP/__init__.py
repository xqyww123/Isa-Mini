from __future__ import annotations

import asyncio
from typing import Any
import os
import json

import mcp.types as types
import mcp.server.stdio
from mcp.server.lowlevel import NotificationOptions, Server
from mcp.server.models import InitializationOptions

server = Server("IsaMini_MCP")

@server.list_tools()
async def list_tools() -> list[types.Tool]:
    this_dir = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(this_dir, "tools", "edit.json"), "r") as f:
        edit_json = json.load(f)
    return [
        types.Tool(
            name="edit",
            description="Edit the proof tree",
            inputSchema=edit_json
        ),
        # TODO: show types & sorts, show defs
    ]


@server.call_tool()
async def call_tool(name: str, arguments: dict[str, Any]) -> list[types.ContentBlock] | dict[str, Any]:
    if name != "my_command":
        raise ValueError(f"Unknown tool: {name}")

    query = arguments["query"]
    top_k = arguments.get("top_k", 5)

    # 返回文本
    return [types.TextContent(type="text", text=f"query={query}, top_k={top_k}")]

    # 或返回结构化 dict（如果你还定义了 outputSchema 的话）
    # return {"ok": True, "query": query, "top_k": top_k}


async def run() -> None:
    async with mcp.server.stdio.stdio_server() as (read_stream, write_stream):
        await server.run(
            read_stream,
            write_stream,
            InitializationOptions(
                server_name="IsaMini_MCP",
                server_version="0.1.0",
                capabilities=server.get_capabilities(
                    notification_options=NotificationOptions(),
                    experimental_capabilities={},
                ),
            ),
        )


if __name__ == "__main__":
    asyncio.run(run())
