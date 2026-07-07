"""Task abstraction for an AoA proof session.

A `Task` captures *what kind of job* a proof session is doing, orthogonally to
*how* it is driven (the driver / LLM) and *what* proof tree it operates on. It is
the single override point for the system prompt and for extra material injected
into the initial user message.

- `UsualTask` — the ordinary `by aoa` / eval proof. Its `system_prompt` delegates
  straight back to `Session._build_system_prompt("")`, so the emitted bytes are
  identical to the pre-Task behaviour.
- `LearningTask` — the AoA-learning job: the session is handed the goal's original
  Isar proof for reference and is asked to reconstruct it with proof operations
  (so it can distil reusable experience). Only the **major** agent sees the Isar
  proof (workers/interaction forks do not).

The Task lives on the `Runtime` (one per proof tree, shared by planner + workers +
interaction forks); `Session.task` is a forwarding property. A driver that wants
to override the prompt just overrides `Session.system_prompt` (drivers are Session
subclasses) — Task is only the default.
"""

from abc import ABC, abstractmethod
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from .model import Session


class Task(ABC):
    """Abstract job description for a proof session."""

    @abstractmethod
    def system_prompt(self, session: 'Session') -> str | None:
        """The session's system prompt (or None if the driver folds it into the
        initial message). Receives the session because the prompt depends on
        session/driver state (`is_major`/`is_worker`, `tool_name`, the global-lemma
        gate, config)."""
        ...

    def initial_prompt_extra(self, session: 'Session') -> str:
        """Extra text appended to the initial user message. Default: nothing."""
        return ""


class UsualTask(Task):
    """The ordinary proof task — byte-for-byte the legacy behaviour."""

    def system_prompt(self, session: 'Session') -> str | None:
        return session._build_system_prompt("")


class LearningTask(Task):
    """The AoA-learning task: reconstruct a goal from its original Isar proof and
    distil reusable experience. The original Isar proof is shown to the major agent
    only (as a reference note in the system prompt and a block in the initial
    message)."""

    def __init__(self, original_isar: str):
        self.original_isar = original_isar

    def system_prompt(self, session: 'Session') -> str | None:
        # [T1] appended (major only) — the reference note is injected inside
        # `_build_system_prompt`, which gates it to the major branch.
        return session._build_system_prompt(
            "You are also given the original Isar proof of the goal, for reference.\n")

    def initial_prompt_extra(self, session: 'Session') -> str:
        # [T2] injected into the initial user message — major only.
        if not session.is_major:
            return ""
        return (
            "\n\n## Original Isar proof (for reference)\n"
            "```isabelle\n"
            f"{self.original_isar}\n"
            "```\n"
        )
