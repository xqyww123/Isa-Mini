"""Task abstraction for an AoA proof session.

A `Task` captures *what kind of job* a proof session is doing, orthogonally to
*how* it is driven (the driver / LLM) and *what* proof tree it operates on. It
builds the session's two prompts, the system prompt and the initial message.

- `StdTask` — the framework's prompts, with the task's own words at a fixed place
  in each (`task_system`, `task_initial`).
- `UsualTask` — the ordinary `by aoa` / eval proof: `StdTask` with no words of its
  own.
- `LearningTask` — the AoA-learning job: the session is handed the goal's original
  Isar proof for reference and is asked to reconstruct it with proof operations
  (so it can distil reusable experience). The Isar proof opens the major's initial
  message, so the major's interaction forks see it when they have context and not
  otherwise; workers do not see it.

The Task lives on the `Runtime` (one per proof tree, shared by planner + workers +
interaction forks); `Session.task` is a forwarding property.

Every task, built-in or a plugin's, is registered by name with `@aoa_task`
(docs/USER_OPERATIONS.md, section 4.2); its constructor takes the payload the ML
caller sent, already decoded.  The call's task is `TASK_REGISTRY[name](payload)`.
"""

from abc import ABC, abstractmethod
from typing import Any

from . import config
from .helper import check_name_and_abstractness
from .model import (Session, Role_Major, Role_Worker, Have,
                    TOOL_EDIT, TOOL_DELETE, TOOL_SEARCH, TOOL_READ, TOOL_RECALL_REMOVED,
                    TOOL_REQUEST_LEMMAS, TOOL_REFRESH, TOOL_REPORT, TOOL_SUBAGENT,
                    TOOL_CLOSE_SUBAGENT, TOOL_WRITE_MEMORY)


class Task(ABC):
    """Abstract job description for a proof session.  role, in every hook, is the
    role of the session the prompt is built for, the major's or a worker's (Session
    passes its own role).  An interaction fork has no system prompt or initial
    message of its own: it is sent the system prompt of the session that launched
    it, and sees that session's initial message only inside a copied conversation."""

    def __init__(self, payload: Any) -> None:
        """Receives the payload the ML caller sent, already decoded (section 4.2)."""

    @abstractmethod
    async def system_prompt(self, role: Role_Major | Role_Worker, session: Session) -> str | None:
        """The whole system prompt, or None to send none.  Session appends the tactic
        block to it, or, when it is None, to the initial message; nothing else moves
        there, so whatever the agent must know goes into initial_prompt.  Do not
        include the tactic block.  Session may call this again at any time (for
        example when an interaction fork starts and is sent a fresh copy), and every
        call must return the same text: it may depend only on the task, the role and
        the session's configuration."""

    @abstractmethod
    async def initial_prompt(self, role: Role_Major | Role_Worker, session: Session, has_system: bool) -> str:
        """The whole initial message; has_system says whether a system prompt is
        sent.  Session appends the tactic block when it is not; do not include it.
        Session memoizes the result and resends it at compaction and restart, so do
        not count on text that changes during the proof being refreshed.  A Task
        implementing this directly does not fill the nodes' .line values (Session
        does, before calling it)."""


TASK_REGISTRY: 'dict[str, type[Task]]' = {}


def aoa_task(name: str):
    """Class decorator registering a `Task` subclass under `name`, with the
    refusals of `check_name_and_abstractness`."""
    def decorator[T: type[Task]](cls: T) -> T:
        check_name_and_abstractness("Task", name, TASK_REGISTRY.get(name), cls)
        TASK_REGISTRY[name] = cls
        return cls
    return decorator


class StdTask(Task):
    """The framework's prompts, with the task's own words at a fixed place in each;
    the contract for those words is in task_system and task_initial."""

    async def system_prompt(self, role: Role_Major | Role_Worker, session: Session) -> str | None:
        # annotated wider than the body: a subclass may return None
        return self._build_system_prompt(role, session)

    async def initial_prompt(self, role: Role_Major | Role_Worker, session: Session, has_system: bool) -> str:
        return self.task_initial(role, has_system) + await self._compute_initial_prompt_base(role, session, has_system)

    def task_system(self, role: Role_Major | Role_Worker) -> str:
        """The task's words in the system prompt, continuing the first paragraph of the
        role's body: whole lines, each ending in "\\n", no blank line at the end (the
        framework's paragraph break follows).  Default: nothing."""
        return ""

    def task_initial(self, role: Role_Major | Role_Worker, has_system: bool) -> str:
        """The task's words opening the initial message: whole lines, each ending in
        "\\n"; the framework's text follows directly, so a text that forms a section
        of its own ends with a blank line.  Default: nothing."""
        return ""

    def _lemma_guidance(self, role: Role_Major | Role_Worker, session: Session) -> str:
        """The "if a needed lemma doesn't exist, ..." guidance clause:
        ``_build_system_prompt`` uses it in the worker's body,
        ``_compute_initial_prompt_base`` in the major's initial message when no system
        prompt is sent.  The major's body words the same advice itself (``lemma_step``).
        When the global-lemma gate is active for the major, steer to
        declare-then-delegate; a worker is steered to prove inline or `request`;
        otherwise keep the legacy "prove it" wording so flag-off planner output is
        byte-identical."""
        if isinstance(role, Role_Worker):
            # A worker can prove a needed fact inline as a LOCAL `Have` (cheap), or
            # — for a general lemma it cannot prove inline — raise a `request` (the
            # worker→planner channel, which dispatches a prover sub-agent; the cost
            # caution lives on the `request` tool itself). The planner branches below
            # deliberately do NOT mention `request`: the planner is the RECIPIENT
            # of requests, not a caller. When general-lemma requests are disabled,
            # drop the `request` option and steer to proving the special case inline.
            if config.DISABLE_REQUEST_GENERAL_LEMMAS:
                return ("if a needed lemma truly does not exist, prove the specific "
                        "instance you need inline as a `Have`.\n")
            return ("if a needed lemma truly does not exist, prove it inline as a "
                    "`Have`, or raise a `request`.\n")
        if session.gate_global_lemma_proofs:
            return ("if a needed lemma truly does not exist, declare it as a `Have` node "
                    "under `global`, then dispatch a sub-agent to prove it.\n")
        return "if a needed lemma truly does not exist, prove it as a `Have` node under `global`.\n"

    def _build_system_prompt(self, role: Role_Major | Role_Worker, session: Session) -> str:
        """The system prompt for the role: its body, with task_system's words after
        the body's first paragraph, then the tool list."""
        report_line = (
            "If the goal itself looks flawed or unprovable, or you have exhausted "
            f"your strategies — report it with `{session.tool_name(TOOL_REPORT)}`.\n"
            if isinstance(role, Role_Worker) else
            "A proof goal can be buggy and thus unprovable — "
            f"call `{session.tool_name(TOOL_REPORT)}` with your analysis if you believe so.\n"
        )
        report_line += (
            "Many Isabelle functions are partially specified (example: `x / 0`, "
            "`hd []`, `inverse 0`). If contextual premises cannot constrain operands "
            "into the domain, the goal is unprovable — refute it.\n"
        )
        # Declarative-style guidance, shared verbatim by the major's and the worker's
        # bodies so the two cannot drift.
        declarative_style = (
            "Prove like a mathematician, not a machine:\n"
            "- Write the proof as you would on paper: use `Have` to state intermediate "
            "results, `Obtain` to introduce the objects you need, and `Suffices` or case "
            "splits to break the goal down.\n"
            "- Typically, decompose until each subgoal is simple enough for `Obvious` to close.\n"
            "- Some trivial facts (e.g. `prime 7`) may not be found by `query` — declare them "
            "with `Have` and prove them with `Obvious`.\n"
            "- Treat the low-level single-step ops (`Rewrite`, `Derive`) as an escape hatch, "
            "not the default — reach for them only on rare occasions when you genuinely need "
            "to spell out a fine-grained inference step.\n"
        )
        # Experience retrieval is gated by AoA_enable_read_memory (see Runtime); when
        # off, the "experience" kind is absent from the `query` schema, so the prompt
        # must not point at it either.
        experience_hint = (
            f'You can also `{session.tool_name(TOOL_SEARCH)}` with `kinds: ["experience"]` to '
            "retrieve saved proof experiences (strategies) relevant to your goal.\n"
            if session.enable_read_memory else "")
        t = self.task_system(role)
        if isinstance(role, Role_Major):
            # The main agent's job is to formalize a PLAN (BFS skeleton + delegate),
            # not to prove stepwise. The worker gets its own structured body (intro +
            # shared declarative-style guidance + points). Gate-aware lemma step: when
            # the global-lemma gate is on, steer to declare-then-delegate; otherwise
            # keep the legacy prove-under-global.
            lemma_step = ("declare it as a `Have` under `global`, then dispatch a "
                          "sub-agent to prove it"
                          if session.gate_global_lemma_proofs
                          else "prove it as a `Have` under `global`")
            body = (
                "You are a formal theorem-proving agent. Your first job is not to prove the "
                "goal step by step — it is to formalize a *plan* for the proof. The MCP tools "
                "below are the medium in which you write that plan; the goal and the current "
                "(incomplete) plan are in `./proof.yaml`.\n"
                + t +
                "\n"
                "Work breadth-first:\n"
                "1. Formalize the top-level structure first — decompose the goal into a few "
                "subgoals / intermediate lemmas (`Have`, `Suffices`, case splits), leaving each "
                "proof as a hole. Don't dive into any single branch.\n"
                "2. Refine one layer at a time, leaving deeper holes as you go.\n"
                f"3. Delegate — call `{session.tool_name(TOOL_SUBAGENT)}` on each non-trivial "
                "subgoal or lemma instead of working it out yourself.\n"
                f"4. If you need a background lemma, `{session.tool_name(TOOL_SEARCH)}` for it "
                f"first; if it truly doesn't exist, {lemma_step}.\n"
                "\n"
                + (experience_hint + "\n" if experience_hint else "")
                + declarative_style +
                "\n"
                "Holes are expected:\n"
                "- Declaring structure and leaving holes is good — move on, don't grind.\n"
                "- An unproved goal shows as `Unfinished Proof`, not an error — that's expected; "
                "don't rush to close holes depth-first.\n"
                "\n"
                "Also:\n"
                "- " + report_line +
                "- Be concise in text output.\n"
                "- Done when every hole is discharged (by you or your sub-agents) and no errors remain.\n"
            )
        else:
            # The worker is handed one specific goal to prove (the planner already laid
            # out the surrounding skeleton). Structured as intro + the shared
            # declarative-style guidance + the remaining points concatenated directly.
            body = (
                "You are a formal theorem-proving agent. You have been handed a specific "
                "goal to prove; it and the current (incomplete) proof are in `./proof.yaml`.\n"
                + t +
                "\n"
                + declarative_style +
                "\n"
                "If a sub-part would derail your main line of reasoning, hand it to a "
                f"sub-agent with `{session.tool_name(TOOL_SUBAGENT)}` rather than proving it inline.\n"
                "The goal may rely on background lemmas that are not yet available. "
                f"Search for them with `{session.tool_name(TOOL_SEARCH)}` first; "
                + self._lemma_guidance(role, session)
                + experience_hint
                + report_line +
                "Be concise in text output.\n"
                "Continue until the goal is fully proved and no errors remain.\n"
            )
        PROMPT = (
                body +
                "\n"
                "## Tools\n"
                f"- {session.tool_name(TOOL_EDIT)}: Fill, insert, or amend proof steps (your primary tool)\n"
                f"- {session.tool_name(TOOL_DELETE)}: Delete proof steps\n"
                f"- {session.tool_name(TOOL_SEARCH)}: Search for theorems, constants, types, rules"
                + (", and saved experiences (proof strategies)" if session.enable_read_memory else "")
                + "; also help you understand unfamiliar terms\n"
                f"- {session.tool_name(TOOL_READ)}: Recall proof state from `proof.yaml`. Use only when you have lost track.\n"
                f"- {session.tool_name(TOOL_RECALL_REMOVED)}: Browse deleted proof steps that were archived before removal.\n"
                f"- {session.tool_name(TOOL_REQUEST_LEMMAS)}: {config.request_tool_description()}\n"
                f"- {session.tool_name(TOOL_REFRESH)}: Reset the conversation and start over (the proof tree is kept). "
                "Write a briefing for your future self in `briefing` — it becomes your only memory. "
                "Use when your edits keep failing.\n"
            )
        parts = [PROMPT]
        # report: listed in the workers' prompts only.
        if isinstance(role, Role_Worker):
            parts.append(
                f"- {session.tool_name(TOOL_REPORT)}: Report that the goal is unprovable (refute) or that you give up (surrender)\n"
            )
        # subagent/cancel_subagent are dispatch tools: the major and the workers (which
        # may delegate nested sub-goals) both dispatch.
        parts.append(
            f"- {session.tool_name(TOOL_SUBAGENT)}: Launch a sub-agent to prove a subgoal whose proof would derail your main line of reasoning.{config.subagent_cost_caution()}\n"
            f"- {session.tool_name(TOOL_CLOSE_SUBAGENT)}: Cancel and remove a sub-agent you dispatched (the sub-agent is terminated; to resume it instead, call `subagent` again).\n"
        )
        # write_memory is gated by AoA_enable_write_memory (see Runtime); when
        # off it is absent from the advertised tools, so it must not be listed
        # here either.
        if session.enable_write_memory:
            parts.append(
                f"- {session.tool_name(TOOL_WRITE_MEMORY)}: Save a reusable proof experience or a strategy for a general class of goals, so future proofs can retrieve it using the `{session.tool_name(TOOL_SEARCH)}` tool.\n"
            )
        return "".join(parts)

    async def _compute_initial_prompt_base(self, role: Role_Major | Role_Worker, session: Session, has_system: bool) -> str:
        """The framework's initial message for the role; has_system as in initial_prompt."""
        if isinstance(role, Role_Worker):
            target = role.target
            if isinstance(target, Have):
                header = f"Prove the lemma `{target.name}`: {target.statement['english']}\n"  # type: ignore[attr-defined]  — isinstance(target, Have) narrowing is erased by @proof_operation's type[Any] return
            else:
                # The worker's whole target IS its scope, so it has no short id
                # to name (relativizing to itself is empty) — name it in prose.
                header = "Prove the following goal.\n"
            guidance = ""
            g = []
            sugg = role.suggestions.strip()
            if sugg:
                g.append(sugg)
            block = await session._render_useful_lemmas()
            if block:
                g.append(block)
            if g:
                guidance = "\n" + "\n\n".join(g) + "\n\n"
            if has_system:
                return (
                    header + guidance
                    + "Complete the proof using the MCP proof tools.\n"
                    "The proof state is in `proof.yaml` — read it to see the goal and current proof."
                )
            else:
                return (
                    header + guidance
                    + "The proof state is in `proof.yaml` — read it to see the goal and current proof.\n"
                    f"Analyze the proof goal, plan a proof, and complete it using tools `{session.tool_name(TOOL_EDIT)}` and `{session.tool_name(TOOL_DELETE)}`.\n"
                    "Continue building the proof until no error remains.\n"
                    "If the goal itself looks flawed or unprovable, or you want to "
                    f"give up — report it with `{session.tool_name(TOOL_REPORT)}`."
                )
        elif has_system:
            return (
                "Complete the proof using the MCP proof tools.\n"
                "The proof state is in `proof.yaml` — read it to see the goal and current proof."
            )
        else:
            # No system prompt: fold the major-only lemma hint into the initial
            # message, mirroring the major's body of _build_system_prompt.
            planner_hint = (
                "The goal may rely on background lemmas that are not yet available. "
                f"Search for them with `{session.tool_name(TOOL_SEARCH)}` first; "
                + self._lemma_guidance(role, session)
            )
            return (
                "An incomplete proof is provided in `proof.yaml` — read it to see the goal and current proof.\n"
                f"Analyze the proof goal, plan a proof, and complete it using tools `{session.tool_name(TOOL_EDIT)}` and `{session.tool_name(TOOL_DELETE)}`.\n"
                "Continue building the proof until no error remains.\n"
                f"{planner_hint}"
                "A proof goal can be buggy and thus unprovable — "
                f"call `{session.tool_name(TOOL_REPORT)}` with your analysis if you believe so."
            )


@aoa_task("usual")
class UsualTask(StdTask):
    """The ordinary proof task — byte-for-byte the legacy behaviour.  Its payload
    is empty and ignored."""


@aoa_task("learning")
class LearningTask(StdTask):
    """The AoA-learning task: reconstruct a goal from its original Isar proof and
    distil reusable experience.  The major's initial message opens with the original
    Isar proof, and its system prompt carries a note announcing it; the major's
    interaction forks with context see both, those without context only the note;
    workers see neither."""

    def __init__(self, original_isar: str):
        self.original_isar = original_isar

    def task_system(self, role: Role_Major | Role_Worker) -> str:
        if not isinstance(role, Role_Major):
            return ""
        return "You are also given the original Isar proof of the goal, for reference.\n"

    def task_initial(self, role: Role_Major | Role_Worker, has_system: bool) -> str:
        if not isinstance(role, Role_Major):
            return ""
        return ("## Original Isar proof (for reference)\n```isabelle\n"
                + self.original_isar + "\n```\n\n")
