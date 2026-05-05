"""Integration test: verify that a forked agent session reuses the main session's prompt cache.

This test checks that after our system_prompt fix, the fork's first API call shows
cache_read_input_tokens > 0 (hitting the main session's cached prefix) rather than
cache_read_input_tokens == 0 (full cache miss, which was the bug).

Requirements:
  - Valid Claude API credentials (ANTHROPIC_API_KEY or OAuth)
  - Network access to Claude API

Usage:
  python -m IsaMini_AoA.test_cache_reuse
"""

import asyncio
import os
import sys
import tempfile
import uuid
from dataclasses import dataclass

from claude_agent_sdk import ClaudeAgentOptions, ClaudeSDKClient, HookMatcher, ResultMessage
from claude_agent_sdk.types import HookInput, HookContext, HookJSONOutput



@dataclass
class CacheMetrics:
    input_tokens: int = 0
    cache_creation_input_tokens: int = 0
    cache_read_input_tokens: int = 0
    output_tokens: int = 0


async def _allow_all(hook_input: HookInput, tool_use_id: str | None, context: HookContext) -> HookJSONOutput:
    return {"continue_": True}


@dataclass
class SessionResult:
    metrics: CacheMetrics
    session_id: str | None = None


async def _run_session(client: ClaudeSDKClient, query: str) -> SessionResult:
    """Send a query and collect metrics + session_id from the ResultMessage."""
    result = SessionResult(metrics=CacheMetrics())
    await client.query(query)
    async for message in client.receive_response():
        if isinstance(message, ResultMessage):
            result.session_id = message.session_id
            if message.usage:
                result.metrics.input_tokens += message.usage.get("input_tokens", 0)
                result.metrics.cache_creation_input_tokens += message.usage.get("cache_creation_input_tokens", 0)
                result.metrics.cache_read_input_tokens += message.usage.get("cache_read_input_tokens", 0)
                result.metrics.output_tokens += message.usage.get("output_tokens", 0)
    return result


async def run_test():
    """Run main session, then fork and check cache reuse."""
    work_dir = tempfile.mkdtemp(prefix="cache_test_")
    proof_yaml = os.path.join(work_dir, "proof.yaml")
    with open(proof_yaml, "w") as f:
        f.write("goal: \"1 + 1 = (2::nat)\"\nproof:\n  - step_1: _\n")

    print(f"Working directory: {work_dir}")
    base_system_prompt = "You are a formal theorem proving agent. Complete the proof."
    print(f"System prompt length: {len(base_system_prompt)} chars")
    print()

    # Pad system prompt to exceed 1024-token minimum for prompt caching.
    # Claude requires the cacheable prefix to be at least 1024 tokens.
    padding = "\n# Reference\n" + ("Isabelle/HOL is a generic proof assistant. " * 200)
    test_system_prompt = base_system_prompt + padding

    # --- Phase 1: Main session (build up cache) ---
    print("=== Phase 1: Main session ===")
    print(f"  Padded system prompt length: {len(test_system_prompt)} chars")
    main_options = ClaudeAgentOptions(
        model="claude-opus-4-6[1m]",
        thinking={"type": "disabled"},
        system_prompt=test_system_prompt,
        cwd=work_dir,
        permission_mode="default",
        allowed_tools=["Read"],
        max_turns=2,
        hooks={
            "PreToolUse": [HookMatcher(matcher="*", hooks=[_allow_all])],
        },
    )

    async with ClaudeSDKClient(options=main_options) as client:
        main_result = await _run_session(client, "Read ./proof.yaml and tell me what the goal is.")

    main_session_id = main_result.session_id
    main_metrics = main_result.metrics

    print(f"  Session ID: {main_session_id}")
    print(f"  Input tokens: {main_metrics.input_tokens}")
    print(f"  Cache creation: {main_metrics.cache_creation_input_tokens}")
    print(f"  Cache read: {main_metrics.cache_read_input_tokens}")
    print(f"  Output tokens: {main_metrics.output_tokens}")
    print()

    if main_session_id is None:
        print("ERROR: Could not obtain main session ID. Cannot test fork.")
        return False

    # --- Phase 2: Fork session (should reuse cache) ---
    print("=== Phase 2: Fork session (--resume --fork-session) ===")
    fork_options = ClaudeAgentOptions(
        model="claude-opus-4-6[1m]",
        thinking={"type": "disabled"},
        system_prompt=test_system_prompt,
        resume=main_session_id,
        fork_session=True,
        cwd=work_dir,
        permission_mode="default",
        allowed_tools=["Read"],
        max_turns=1,
        hooks={
            "PreToolUse": [HookMatcher(matcher="*", hooks=[_allow_all])],
        },
    )

    async with ClaudeSDKClient(options=fork_options) as client:
        fork_result = await _run_session(client, "What is 1+1? Answer in one word.")
    fork_metrics = fork_result.metrics

    print(f"  Input tokens: {fork_metrics.input_tokens}")
    print(f"  Cache creation: {fork_metrics.cache_creation_input_tokens}")
    print(f"  Cache read: {fork_metrics.cache_read_input_tokens}")
    print(f"  Output tokens: {fork_metrics.output_tokens}")
    print()

    # --- Phase 3: Control — fork WITHOUT shared system_prompt ---
    print("=== Phase 3: Control (different system_prompt, should NOT reuse cache) ===")
    control_options = ClaudeAgentOptions(
        model="claude-opus-4-6[1m]",
        thinking={"type": "disabled"},
        system_prompt=test_system_prompt + "\n# Timestamp: this-breaks-cache-" + str(uuid.uuid4()),
        resume=main_session_id,
        fork_session=True,
        cwd=work_dir,
        permission_mode="default",
        allowed_tools=["Read"],
        max_turns=1,
        hooks={
            "PreToolUse": [HookMatcher(matcher="*", hooks=[_allow_all])],
        },
    )

    async with ClaudeSDKClient(options=control_options) as client:
        control_result = await _run_session(client, "What is 1+1? Answer in one word.")
    control_metrics = control_result.metrics

    print(f"  Input tokens: {control_metrics.input_tokens}")
    print(f"  Cache creation: {control_metrics.cache_creation_input_tokens}")
    print(f"  Cache read: {control_metrics.cache_read_input_tokens}")
    print(f"  Output tokens: {control_metrics.output_tokens}")
    print()

    # --- Verdict ---
    print("=== Verdict ===")
    fork_cache_ratio = (
        fork_metrics.cache_read_input_tokens /
        max(1, fork_metrics.cache_read_input_tokens + fork_metrics.cache_creation_input_tokens + fork_metrics.input_tokens)
    )
    control_cache_ratio = (
        control_metrics.cache_read_input_tokens /
        max(1, control_metrics.cache_read_input_tokens + control_metrics.cache_creation_input_tokens + control_metrics.input_tokens)
    )

    print(f"  Fork cache read ratio: {fork_cache_ratio:.1%}")
    print(f"  Control cache read ratio: {control_cache_ratio:.1%}")
    print()

    if fork_metrics.cache_read_input_tokens > 0:
        print("  ✓ PASS: Fork reused cache from main session")
        if fork_cache_ratio > control_cache_ratio:
            print(f"  ✓ PASS: Fork cache ratio ({fork_cache_ratio:.1%}) > control ({control_cache_ratio:.1%})")
        success = True
    else:
        print("  ✗ FAIL: Fork did NOT reuse cache (cache_read_input_tokens == 0)")
        print("    The system_prompt fix did not resolve the cache reuse issue.")
        print("    Possible causes:")
        print("    - Tool definitions differ between main and fork")
        print("    - CLI injects additional dynamic content not controlled by system_prompt")
        success = False

    # Cleanup
    import shutil
    shutil.rmtree(work_dir, ignore_errors=True)
    return success


def main():
    success = asyncio.run(run_test())
    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()
