# AoA Task 机制重构方案：prompt 模板归框架，task 只填自己的话

状态：第三稿，评审通过，待 owner 一句开工（2026-10-15）。第一稿经 23 个 agent 的两轮对抗评审，第二稿经 22 个；两位 judge 提出的每个决定点 owner 都已拍板，本稿把这些决定和 judge 列出的、无需 owner 决定的修正全部落进来，judge 裁定不必再评审。设计决策均为 owner 在 session「AoA Task」中拍板，本文只把它们落到文件、行号和验证步骤上。行号以当前工作树为准。

owner 的决定，按本文落实的位置：`Task` 有两个整段钩子而不是一个带布尔的钩子（§1）；`has_system` 保留，由 `Session` 算一次传入，两段无 system prompt 的长版随构造函数搬并测试（§2.2、§3、§7）；worker 的 header 留在框架里，task 文字永远加在初始消息最前（§2.2）；`print_proof_scope` 那句留在 `Session`（§6）；LearningTask 的 Isar 块前移后以空行结尾，并由此定下统一的空白约定（§2）；interaction fork 正文的插入点在正文末尾（§2.1）；golden 的改法（§7、§9.3）。

## 0. 目标与范围

今天 `Task` 有两个钩子，语义不对称：`system_prompt(session)` 整段替换 system prompt，`initial_prompt_extra(session)` 只能在初始消息末尾追加；框架的 prompt 构造函数 `_build_system_prompt` / `_compute_initial_prompt_base` 住在 `Session` 上，task 想在正文里说一句话只能借 `reference_note` 这一个插入点（仅 major 分支有）。

改成：

- `Task` 有两个抽象的 async 钩子，`system_prompt(role, session)` 返回整段 system prompt 或 `None`，`initial_prompt(role, session, has_system)` 返回整段初始消息。
- `StdTask(Task)` 实现这两个钩子，实现体就是今天的两个构造函数搬来（§1 的替换规则）；它开放两个文字改写点 `task_system(role)` 和 `task_initial(role, has_system)`，默认都返回空串，返回值拼在固定位置（§2）。
- `UsualTask`、`LearningTask`、TAT 将来的两个 Define task（`TAT.pattern_completeness`、`TAT.termination`）都继承 `StdTask`，只改写文字改写点。
- 全部异步。

不动：ML 侧、wire、`(name, payload)`、`TASK_REGISTRY` / `@aoa_task`、`Runtime.task` 的归属、tactic 段的拼接位置（仍在 task 之外，§6）、`## Tools`（仍在 `_build_system_prompt` 里）。

字节保证：`UsualTask` 的 system prompt 与初始消息在三种角色下逐字节不变；`LearningTask` 的 system prompt 不变，初始消息里 Isar 代码块从末尾移到最前（§2.2），这是唯一的字节变化，只影响 AoA-learning 运行的日志和那次运行的 agent 看到的文字。

## 1. 新接口（`task.py`）

下面的代码块只写改变的部分：`helper` 的 import、`TASK_REGISTRY`、`aoa_task`、`Task.__init__` 和 `UsualTask` 的 docstring 保持今天的样子。

```python
from abc import ABC, abstractmethod
from typing import Any
from . import config
from .model import (Session, Role, Role_Major, Role_Worker, Role_Interaction, Have,
                    TOOL_EDIT, TOOL_DELETE, TOOL_SEARCH, TOOL_READ, TOOL_RECALL_REMOVED,
                    TOOL_REQUEST_LEMMAS, TOOL_REFRESH, TOOL_REPORT, TOOL_SUBAGENT,
                    TOOL_CLOSE_SUBAGENT, TOOL_WRITE_MEMORY)


class Task(ABC):
    """<今天的第一行不变>  role, in every hook, is the role of the session the prompt
    is built for (Session passes its own role).  An interaction fork, with or
    without context, is sent the system prompt of the session that launched it, and
    sees that session's initial message only inside a copied conversation: an
    initial message built for Role_Interaction is never sent, and a system prompt
    built for it only to a fork launched from an interaction fork (interactive
    retrieval)."""

    def __init__(self, payload: Any) -> None: ...

    @abstractmethod
    async def system_prompt(self, role: Role, session: Session) -> str | None:
        """The whole system prompt, or None to send none.  Session appends the tactic
        block to it, or, when it is None, to the initial message; nothing else moves
        there, so whatever the agent must know goes into initial_prompt.  Do not
        include the tactic block.  Session may call this again at any time (for
        example when a fork starts and is sent a fresh copy), and every call must
        return the same text: it may depend only on the task, the role and the
        session's configuration."""

    @abstractmethod
    async def initial_prompt(self, role: Role, session: Session, has_system: bool) -> str:
        """The whole initial message; has_system says whether a system prompt is
        sent.  Session appends the tactic block when it is not; do not include it.
        Session memoizes the result and resends it at compaction and restart, so do
        not count on text that changes during the proof being refreshed.  A Task
        implementing this directly does not fill the nodes' .line values (Session
        does, before calling it)."""


class StdTask(Task):
    """The framework's prompts, with the task's own words at a fixed place in each;
    the contract for those words is in task_system and task_initial."""

    async def system_prompt(self, role: Role, session: Session) -> str | None:
        # annotated wider than the body: a subclass may return None (§3)
        return self._build_system_prompt(role, session)

    async def initial_prompt(self, role: Role, session: Session, has_system: bool) -> str:
        return self.task_initial(role, has_system) + await self._compute_initial_prompt_base(role, session, has_system)

    def task_system(self, role: Role) -> str:
        """The task's words in the system prompt, continuing the first paragraph of the
        role's body: whole lines, each ending in "\\n", no blank line at the end (the
        framework's paragraph break follows).  Default: nothing."""
        return ""

    def task_initial(self, role: Role, has_system: bool) -> str:
        """The task's words opening the initial message: whole lines, each ending in
        "\\n"; the framework's text follows directly, so a text that forms a section
        of its own ends with a blank line.  Default: nothing."""
        return ""

    def _build_system_prompt(self, role: Role, session: Session) -> str: ...                         # 自 model.py:13125 搬来，§2.1
    async def _compute_initial_prompt_base(self, role: Role, session: Session, has_system: bool) -> str: ...  # 自 model.py:13298 搬来，§2.2
    def _lemma_guidance(self, role: Role, session: Session) -> str: ...                              # 自 model.py:13077 搬来，§1 末


@aoa_task("usual")
class UsualTask(StdTask):
    pass


@aoa_task("learning")
class LearningTask(StdTask):
    def __init__(self, original_isar: str): self.original_isar = original_isar

    def task_system(self, role: Role) -> str:
        if not isinstance(role, Role_Major):
            return ""
        return "You are also given the original Isar proof of the goal, for reference.\n"

    def task_initial(self, role: Role, has_system: bool) -> str:
        if not isinstance(role, Role_Major):
            return ""
        return ("## Original Isar proof (for reference)\n```isabelle\n"
                + self.original_isar + "\n```\n\n")
```

**搬动时的替换规则。** 三个搬走的函数在 `StdTask` 上是新定义，不是 override，所以参数都标注类型（不标注的参数对 pyright 是 Unknown，改名产生的所有 `session.xxx` 访问就都不被检查）。构造函数体内：

- `self.is_major` / `self.is_worker` / `self.is_interaction` 改为 `isinstance(role, Role_Major)` / `Role_Worker` / `Role_Interaction`。`_compute_initial_prompt_base` 外层的 `if self.is_worker:` 改成 `isinstance(role, Role_Worker)` 之后 `role` 已被收窄，内层 `if isinstance(self.role, Role_Worker):`（`model.py:13318`）删除、其体缩进一层。
- `self.tool_name(...)`、`self.enable_read_memory`、`self.enable_write_memory`、`self.gate_global_lemma_proofs`、`self._render_useful_lemmas()` 改为 `session.xxx`；`self.role.target` / `.suggestions` 改为 `role.xxx`。`role.target` 那行（`model.py:13310`）的 `# type: ignore[attr-defined]  — is_worker ⟹ role is Role_Worker` 删除，`isinstance` 收窄后不再需要、理由也不再成立；13312 行的 ignore 保留，它的理由（`@proof_operation` 抹掉了收窄）仍然成立。
- `reference_note` 参数删除，其位置改为 `self.task_system(role)`（§2.1）；`self.system_prompt() is not None` 的两处判断改为参数 `has_system`；`print_proof_scope` 那一句不搬（§6）。
- `config` 在 `task.py` 里单独 `from . import config`（和 `model.py:11`、`mcp_http_server.py:86` 一样），不从 `model` 转手。
- 搬进去的代码里已经不实的注释随手改正，字节不动：`model.py:13349-13350` 说"没有 system prompt 的 driver，例如 Codex"，Codex 今天走 system prompt；`_lemma_guidance` docstring（13080）的 "for this non-worker major" 改为 "for the major"。

`_lemma_guidance` 的三个调用点（13219、13236、13354）全在搬走的构造函数里，所以它一起搬进 `StdTask`，签名 `_lemma_guidance(self, role: Role, session: Session) -> str`：第一个条件改为 `isinstance(role, Role_Major) and session.gate_global_lemma_proofs`（原来的 `not self.is_worker` 合取项在按角色判断后恒真，删去）；worker 条件改为 `isinstance(role, Role_Worker)`；原参数 `under_global` 在三个调用点的值都等于"角色是 major"，改为在函数内由 `isinstance(role, Role_Major)` 得出。docstring 改为指向 `StdTask` 的两个构造函数。

**角色判断的来源变了，字节不变。** 今天 `Session.is_major` 的定义是 `self.parent is None`（`model.py:12867-12873`），不是看 `role`。搬走的代码一律看 `role`，prompt 代码不再读 `session.parent`。生产环境两者永远一致（根 session 的 role 默认 `Role_Major()`，每个 `_make_fork` 调用点都传 `Role_Worker` 或 `Role_Interaction`）；只有测试给根 session 改 role 时有差别，`TacticPrompt` 就这么做，那里正文从今天的混合文本（major 正文加 worker 的工具行）变成真正的 worker / interaction 正文，但它的 golden 只记录 tactic 段尾部，断言也只看尾部，看不见这个变化。

**文字改写点没有 session。** `task_system` / `task_initial` 的文字不能点工具名（拼写由 driver 经 `Session.tool_name` 决定），不能提按调用门控的功能（write_memory、经验检索）。需要 session 上的值的 task 继承 `StdTask`、改写收 session 的整段钩子、在 `super()` 的结果上加字：初始消息写 `return text + await super().initial_prompt(role, session, has_system)`，文字落在 `task_initial` 同一个位置、同一空白约定；system prompt 只能加在 `await super().system_prompt(role, session)`（类型 `str | None`，改写要处理 `None`）之前或之后，加在之后的文字跟在工具列表后面、在 `Session` 贴的 tactic 段之前，到不了第一段之后那个位置，接缝处的空白由子类自己负责。直接继承 `Task` 只用于整个替换框架 prompt 的 task（§7 `TacticPrompt` 用例 4 的形状）。这条路安全，因为 session 是作为参数到达的：ClaudeCode 的 fork 路径上 `driver_claude_code.py:873` 调的是父会话的 `system_prompt()`，session 就是父会话。两种绕法明令禁止：在改写点里取当前绑定的 session（那条路径上绑定的是 fork，会取错）；在改写的钩子里把 session 存到 `self` 上（task 被这次调用的所有 session 共享，钩子又是 async，会竞争）。system prompt 仍只能依赖 task、role 和 session 的配置；初始消息记忆化、compaction / restart 时重发（§1 钩子 docstring）。只有当某个 task 需要在 system prompt 第一段之后那个位置放依赖 session 的文字时，才由 owner 决定给 `task_system` 加什么参数。

## 2. task 文字的位置与空白约定

**空白约定**（写进 `task_system` / `task_initial` 的 docstring、`StdTask` 类 docstring 里指向约定的那句、USER_OPERATIONS §4.2）：

- 改写点返回的文字由整行组成，每行以 `\n` 结尾，原样插入；框架在它前后不加任何分隔符；空串永远合法，字节上等于没有 task。
- system prompt 里，文字续在角色正文第一段之后，段落空行由框架随后的 `\n` 提供，所以文字以单个 `\n` 结尾，不以空行结尾。
- 初始消息里，文字开头，框架文字紧随其后，所以自成一节的文字以空行结尾。LearningTask 的块以 "```\n\n" 结尾（owner 已决定）；TAT 的 Define 文字同样以空行结尾。
- 不提供、也不在文档里暗示"前导换行另起段"的写法（无人需要）；运行时不对文字做任何归一化。

### 2.1 system prompt（`_build_system_prompt`）

三个角色正文各一处，都在第一段之后，`t = self.task_system(role)`：

| 角色 | 今天的行 | 新写法 |
|---|---|---|
| major | 13176-13182 | `"...are in `./proof.yaml`.\n" + t + "\n" "Work breadth-first:\n" ...`（`t` 取代 `reference_note`，位置相同） |
| worker | 13210-13213 | `"...are in `./proof.yaml`.\n" + t + "\n" + declarative_style + ...`（今天是 `"...\n" "\n" + declarative_style`，`t` 为空时字节相同，与 major 行同形） |
| interaction fork | 13228-13238 | 这段正文没有空行，整个是一段，所以插入点在正文末尾：`... + self._lemma_guidance(role, session) + "Be concise in text output.\n" + t`，之后是框架不变的 `"\n" "## Tools\n"`（owner 已决定） |

`## Tools` 及其后的角色条件行（13239-13274）不动，仍在 `t` 之后。interaction 行保留是为了规则统一；它的文字只送达由 interaction fork 再起的 fork（交互式检索，§2.3）。搬过去的 interaction 分支上加一行注释说明这一点。（2026-10-16 撤销：交互 fork 收发起方的 system prompt，`Role_Interaction` 正文与这一插入点都删去，见 `TASK_PROMPT_FORK_PLAN.md`。）

### 2.2 初始消息

task 文字由 `StdTask.initial_prompt` 拼在整段最前（§1），构造函数 `_compute_initial_prompt_base` 本身不穿任何 task 文字：worker 的 header（13311-13316）、suggestions / useful lemmas（13317-13327）、两行固定话（13329-13332、13344-13347）和两段无 system prompt 的长版（13333-13342、13348-13364）原样搬，只做 §1 的替换。13343 那个分支是"非 worker"分支，major 和 interaction fork 都走它。

于是 `LearningTask` 的 Isar 块从末尾（今天 13295 的 `extra`）移到最前：今天的 `"\n\n## Original Isar proof (for reference)\n```isabelle\n" + isar + "\n```\n"` 贴在两行固定话之后，新的是 `"## Original Isar proof (for reference)\n```isabelle\n" + isar + "\n```\n\n"` 之后接两行固定话。空行从块前移到块后，两行固定话仍自成一段。消息于是以框架文字结尾、没有末尾换行，和 `UsualTask` 的一样；所以 AoA-learning 运行里 driver 追加到初始消息后面的文字（ClaudeCode 的 briefing，`driver_claude_code.py:690-692`；Codex 的，`driver_codex.py:311-313`；API driver 的压缩摘要，`driver_api.py:700-704`）前面从两个空行变成一个空行。这是块前移的必然结果。

### 2.3 谁收到哪段 prompt

- 一个 session 的 system prompt 发给它自己，也发给它派生的每个 interaction fork，有无上下文都一样：ClaudeCode 的 `_run_fork` 给 fork 传的是父会话的 `system_prompt()`（`driver_claude_code.py:873`），API driver 的无上下文 fork 用父会话的（`driver_api.py:788`），Codex 的 fork 以 ephemeral `codex exec fork` 从父会话 fork 的那条线程分出、带父会话的 model instructions 文件（2026-10-16 起，见 `ai-artifacts/review/CODEX_NESTED_FORK_PLAN.md`；此前是 resume 父会话）。ClaudeCode 在 fork 的 `initialize`（235 行，由 852 行到达）里按 `Role_Interaction` 也算一份，算完不用。
- interaction fork 不算初始消息；带上下文的 fork（默认）看到的是父会话的对话。

后果：为 `Role_Interaction` 构造的初始消息永不发出，为它构造的 system prompt 只发给由 interaction fork 再起的 fork（`AoA_interactive_retrieval` 为 yes / yes_recursive 时，`retrieval.py:852-858` 的 `launch_interaction`），task 不需要为它写分支；给 major 或 worker 的 system prompt 文字，它的 fork 也看到；初始消息文字只到该 session 和它带上下文的 fork。这与 TAT 两个 Define task 的设计一致：它们只给 major 的初始消息加字，worker 得空串，system prompt 不加字（§8）。`role` 的定义写在 `Task` 类 docstring（§1）和 USER_OPERATIONS §4.2。新的 `task.py` 模块 docstring 和 `LearningTask` 的类 docstring 不再写 "shown to the major agent only"，改为：Isar 块开在 major 的初始消息里，major 带上下文的 interaction fork 看得见、不带上下文的只看到 system prompt 里的 note，worker 看不见。

（2026-10-16 起，本节关于为 `Role_Interaction` 构造 system prompt 的说法作废：交互 fork 不构造自己的 system prompt，`Session.system_prompt` 向 `parent` 委托；ClaudeCode 在 fork 的 `initialize` 里算的，以及在 ClaudeCode 和 API driver 不带上下文模式下由交互 fork 再起的 fork 收到的，都是发起方链条尽头那个 major / worker 的那份（另两种情形见 §10），见 `TASK_PROMPT_FORK_PLAN.md`。）

三个早于本方案、本次不修的问题记在 §10。

## 3. `has_system` 与 `None`

`Session._compute_initial_prompt` 调一次 `system_prompt()`，既决定 tactic 段的去留，也以 `sp is not None` 作为 `has_system` 传给 `task.initial_prompt`（§6）；`StdTask` 里不再有 Session→Task→Session→Task 的回调。`StdTask` 自己的 `system_prompt` 永不返回 `None`；一个 `StdTask` 子类若改写 `system_prompt` 返回 `None` 而沿用框架的初始消息，就走到两段长版（§2.2），`has_system` 为假。§7 里 `TacticPrompt` 用例 5 覆盖 major 的长版，插入位置测试里 `has_system` 为假的那一遍覆盖两段长版并检查文字改写点收到的 `has_system` 值。`has_system` 是给文字引用了 system prompt 内容的 task 用的；`LearningTask` 今天不看它（那句 note 在无 system prompt 时不送达，是既有行为，不在本方案范围）。

## 4. 全异步

`Session.system_prompt`、`Task.system_prompt`、`Task.initial_prompt` 均为 `async`。调用点逐一加 `await`：

| 文件 | 行 | 所在函数 | 改动 |
|---|---|---|---|
| `model.py` | 13296, 13526 | async | `await`（13328、13343 两处随搬迁变成参数 `has_system`） |
| `driver_claude_code.py` | 235（`initialize`）, 873（`_run_fork`） | async | `await` |
| `driver_api.py` | 294, 697, 788 | async | `await` |
| `driver_codex.py` | 221-225（`_write_model_instructions`，同步） | 由 async 的 `initialize` 在 198 行调用 | 函数保持同步，加参数 `system_prompt: str \| None`，体内 `text = (system_prompt or "") + (...)`，198 行改为 `self._write_model_instructions(await self.system_prompt())` |
| `test.py` | 557, 588（两个 gate 测试）, 19130, 19162（`TacticPrompt`） | async | `await` |
| `test_deep_restart.py` | 474 | 猴子补丁 `lambda: None` | 改 `async def` |
| `test_corrupted_sample.py` | 173 | 猴子补丁 `lambda: "SYS"` | 改 `async def` |

Codex 那个函数保持同步的理由：它只拼字符串、写文件，system prompt 由调用方算好传入，与 §3 对 `has_system` 的做法相同，算一次、往下传。漏 `await` 时两种写法 pyright 都报（参数写法报 reportArgumentType，async 写法报 reportUnusedCoroutine，已实测），§9.2 的 pyright 比对两种都抓得到；只有跳过静态检查时才有差别：参数写法立刻 `TypeError`，async 写法只打一条 RuntimeWarning、文件永远写不出、Codex 静默退回内置 prompt。

## 5. 导入方向反转

今天 `model.py:12` 顶层 `from .task import Task, UsualTask`，所以 `task.py` 只能在 `TYPE_CHECKING` 下引用 `model`。搬迁后 `task.py` 在运行时需要 `Role_*`、`Have`、`TOOL_*`，循环导入。解法：反转方向，不搬任何类。

- `model.py`：删除第 12 行的顶层导入；`Task` 的类型注解（12351、12725、12728）改为 `TYPE_CHECKING` 导入 + 字符串注解；`Runtime.__init__` 第 12351 行局部导入 `UsualTask`（13874 行对 `LearningTask` 已是局部导入）。
- `task.py`：顶层 `from .model import ...`（§1 的列表），`TYPE_CHECKING` 块删除。
- `toplevel.py` 先导入哪个都安全：`model` 不再在顶层依赖 `task`。

## 6. `Session` 侧（`model.py`）

```python
async def system_prompt(self) -> str | None:
    """The system prompt: the task's, with the tactic block appended; None when the
    task sends none (the tactic block then ends the initial message)."""
    sp = await self.task.system_prompt(self.role, self)
    return sp if sp is None else sp + self._tactic_prompt_block()

async def _compute_initial_prompt(self) -> str:
    """The initial message (uncached -- call initial_prompt): the task's, with the
    tactic block appended when there is no system prompt to carry it."""
    # 今天 13300-13307 那段注释和语句原样留在这里：只为填每个节点的 .line，不产生文字，
    # 对任何 Task 都要跑
    self.print_proof_scope(0, MyIO(StringIO()), update_line=True, show_warnings=True)
    sp = await self.system_prompt()
    text = await self.task.initial_prompt(self.role, self, sp is not None)
    return text if sp is not None else text + self._tactic_prompt_block()
```

`_build_system_prompt`、`_compute_initial_prompt_base`、`_lemma_guidance` 从 `Session` 删除（搬到 `StdTask`）；`initial_prompt()` 的缓存、`retry_prompt`、`_tactic_prompt_block` 不动。`Session.system_prompt` 不加缓存（gate 测试和 `TacticPrompt` 在两次调用之间改配置）。13119、13128、13291 三处 docstring 随改；`task.py:17-19` "driver 覆写 `Session.system_prompt`" 的说法删除；`model.py:12346-12350` 的 `Runtime.task` 注释改为"task 构造两段完整的 prompt"。

## 7. 测试

- `TacticPrompt`（`test.py:19099`）只测 tactic 段，五种情形中前三种不动。用例 4 "自写 system prompt 的 task" 改为一个 `Task` 子类，`system_prompt` 返回 `"MY OWN SYSTEM PROMPT\n"`、`initial_prompt` 返回 `""`，断言不变。用例 5 改为一个 `StdTask` 子类：`system_prompt` 返回 `None`，`task_initial` 返回 `"THE TASK'S INITIAL\n"`，断言 `sp is None`；`ip` 以 `"THE TASK'S INITIAL\nAn incomplete proof is provided in `proof.yaml`"` 开头（钉住 `has_system` 为假、长版、插入位置）；`ip` 以 `"if you believe so." + "\n" + head + tactic 行` 结尾（钉住 tactic 段的去处）。重写 19101-19106 的 docstring（它提到已删除的 extra）。**golden `Tests/TacticPrompt.yml` 的预期 diff 只有第 15 行：`--- a task with no system prompt and an extra ---` 改为 `--- a task with no system prompt ---`**（owner 已批准改这一行的标签，最终措辞由 owner 定）。
- 新增插入位置测试 `@model_test("TaskPlacement", "Test_TaskPlacement.thy", <by aoa 的行>)`（名字 *(author)*），**自己的 `.thy`**（CLAUDE.md 禁止两个 model test 共用 `.thy`）。用一个 `StdTask` 子类，标记回显参数：`task_system` 返回 `f"[S {type(role).__name__}]\n"`，`task_initial` 返回 `f"[I {type(role).__name__} {has_system}]\n"`；每种情形先用 `UsualTask` 算一份、再换成该子类算一份，比较：
  - system prompt，对 major、worker、interaction 各一次：去掉第一个标记行后与 `UsualTask` 的逐字节相同（纯插入）；第一个 `"\n\n"` 之前的文字以 `"\n[S Role_Major]"`、`"\n[S Role_Worker]"`、`"\n[S Role_Interaction]"` 结尾，三个角色同一种检查。
  - 初始消息，对 major 和 worker：等于 `"[I Role_Major True]\n"` / `"[I Role_Worker True]\n"` 加 `UsualTask` 的初始消息，逐字节。
  - 再用一个兄弟子类（`async def system_prompt(self, role: Role, session: Session) -> str | None` 返回 `None`）跑一遍 `has_system` 为假：major 的 `_compute_initial_prompt()` 以 `"[I Role_Major False]\nAn incomplete proof is provided in `proof.yaml`"` 开头；worker 的以 `"[I Role_Worker False]\nProve the following goal.\nThe proof state is in `proof.yaml`"` 开头。夹具：worker 的目标不是 `Have`（照 `TacticPrompt`，`root.sub_nodes[1]`），suggestions 和 useful_lemmas 保持默认空，所以 guidance 为空。
  - 用未缓存的 `_compute_initial_prompt()` 读；worker 角色照 `TacticPrompt` 的做法设 `Role_Worker(target=...)`。每项检查写一行 `label: True/False` 进输出（只有布尔值，`Tests/WriteMemoryGate.yml` 的格式），并随即 `assert` 同一个布尔，照 `TacticPrompt`（`test.py:19119-19164`）的做法：位置错了测试体内就抛，到不了 golden 比对那一步，错误结果永远记不进 golden。
- `test_user_operations.py:154`：`Another` 类改为定义两个 async 钩子；149-150、159 不变；737 行所引的报错样例随 §8 改。
- `MemorizeGuard`（`test.py:603`）、`test_session_quit.py:294` 不变（`LearningTask` 构造与 `isinstance` 检查未动）。
- 其余见 §4 的表。

## 8. 文档

- `docs/USER_OPERATIONS.md` §4.2（468-496）：接口改为两个整段钩子加 `StdTask` 的两个文字改写点，写入 §2 的空白约定、§1 末"文字改写点没有 session"那段（只给初始消息的代码例子）和 `role` 的定义（§1 `Task` 的 docstring 原文）；示例 `TerminationTask` 改为继承 `StdTask`、只改写 `task_initial`（major 返回等式，否则空串）；291-292 行"model.py imports task.py"的理由删除（§5 使之不实）；737 行的报错样例 `missing: system_prompt` 改为列出两个钩子名。
- `docs/TACTIC_DESIGN.md` 27 行括号里的 "task 的 extra 之后" 改为 "task 给出的整段 initial prompt 之后"（只转写既定的 tactic 段位置；用该文档自己的词 initial prompt）；255 行两个分发点的描述按 §6 改；306 行 `TacticPrompt` 的五种情形按 §7 改。
- `docs/EXPERIENCE_MEMORY.md` 338、410 行指向 `task.py` 的 `StdTask._build_system_prompt`。
- `task.py` 模块 docstring 和 `LearningTask` 类 docstring 重写（§2.3 末）；`tasks/AoA-learning/PLAN.md` 是历史计划，不动。
- TAT 仓库 `docs/node_classes/DEFINE.md` 第 7 节 "*The task*" 那条（463-478 行）：只改 467-470 行那个从句，今天是 "both deriving from one base that writes the constants and their equations into the initial message, each writing its obligation after them; their `system_prompt` is `UsualTask`'s"，改为：两者继承一个基类，它是 `StdTask` 的子类、只改写 `task_initial`，对 major 返回该 task 在下文（491-507 行）给出的文字并以空行结尾，对 worker 返回空串，system prompt 不从 task 得到任何文字。两个 task 名、`define.py`、`@aoa_task`、payload 那句、`TAT_Std` 的注册文字都不动，从句里不复述文字本身。DEFINE.md 在 TAT 里未跟踪、仍在设计中：手工改，不提交，何时提交由 owner 定。

## 9. 验证

1. **字节 harness**，在改动 `model.py` / `task.py` 的第一行之前写好并存下改前结果：`contrib/Isa-Mini/ai-artifacts/task_prompt_bytes.py`，输出 `task_prompt_bytes.before.txt`；脚本和输出都不提交。不需要 REPL。
   - 桩 session 用 `s = object.__new__(model.Session)` 造，不调 `__init__`、不复制任何方法，只设这些实例属性：`runtime = SimpleNamespace(task=..., tactics=..., enable_read_memory=..., enable_write_memory=...)`（task 和两个内存开关经 `Session` 真实的转发属性读取，`model.py:12725-12745`）；`role`；`parent`（角色是 `Role_Major` 时为 `None`，否则任一非 `None` 对象，与 12867-12873 一致）；`gate_global_lemma_proofs`；实例级覆盖 `tool_name`（恒等映射和 `ClaudeCode._TOOL_NAME_MAP` 两套）、`print_proof_scope`（空操作）、async 的 `_render_useful_lemmas`（带 `useful_lemmas` 的 worker 返回固定块，否则空串）。prompt 代码若读了别的 session 状态，harness 立即以 `AttributeError` 报错。造桩代码改前改后相同。
   - 夹具：`Have` 目标用 `object.__new__(model.Have)` 并手工设 `.name` 和 `.statement = {"english": ...}`（`Have.__init__` 平时设它们，`model.py:9878-9879`，worker 的 header 两个都读）；非 `Have` 目标用 `object()`；interaction 角色 `Role_Interaction(None, "", None, None)`。
   - system prompt 为 `None` 的 task 叫 `NoSys`，两种形态共用一个记录键，脚本按 `hasattr(task_module, "StdTask")` 选：改前 `class NoSys(UsualTask): def system_prompt(self, session): return None`；改后 `class NoSys(StdTask): async def system_prompt(self, role, session): return None`。两者都不改写初始消息钩子，默认都返回空串。
   - harness 只驱动 `Session.system_prompt` 和 `Session._compute_initial_prompt`（可 await 则 await），不直接调构造函数。
   - 矩阵：角色 {major, worker 目标是 `Have`, worker 目标非 `Have`, interaction} × worker 的 guidance {无, suggestions 加 useful_lemmas} × task {UsualTask, LearningTask, NoSys} × 内存开关 {(T,T),(T,F),(F,F)} × gate {F,T} × `config.DISABLE_REQUEST_GENERAL_LEMMAS` {F,T}（跑完复原）× 两套 tool_name × tactics {无, 两条 in_prompt 条目}。
   - 输出每条记录一行 JSON，键是矩阵坐标，值是 `[system prompt, 初始消息]`（JSON 区分 `None` 与空串，回读时保留末尾换行）。
   - 判据由脚本检查：三种 task 的每条记录改前改后逐字节相同（含 `NoSys` 初始消息末尾的 tactic 段），唯一例外是 LearningTask × major × 初始消息，用代码断言：`OLD = "\n\n## Original Isar proof (for reference)\n```isabelle\n" + isar + "\n```\n"`，`NEW = "## Original Isar proof (for reference)\n```isabelle\n" + isar + "\n```\n\n"`，`assert before.endswith(OLD) and after == NEW + before.removesuffix(OLD)`。`NoSys` 必须比对，因为它的记录是 §1 里**改写**而非只改名的代码的唯一字节检查：worker 的无 system prompt 长版（13333-13342）、major / interaction 的长版（13348-13364）、`_lemma_guidance` 的 gate 分支和 " under `global`" 后缀（13084、13100）。若某条不该变的记录变了，先 `git diff model.py` 排除其他 agent 的并发改动。
2. **静态检查**，改前改后各一次。从 `/home/qiyuan/Current/MLML` 跑 `.venv/bin/pyright --outputjson` 于 `task.py`、`model.py`、`toplevel.py`、`driver_claude_code.py`、`driver_api.py`、`driver_codex.py`，取 (文件, 规则, 消息) 去掉行列号后的多重集（`collections.Counter`，`model.py:11876` 同一条消息出现两次，集合比对会漏掉新增的重复），改后必须等于基线（共 10 条：model.py 5、toplevel.py 1、其余 4；没有一条落在搬迁范围内，所以不会有错误移到 `task.py`）；测试文件不跑（test.py 基线约 295 条）。再 `/usr/bin/grep -rnI -E '\b(system_prompt|initial_prompt)\(' --include='*.py' contrib/Isa-Mini/IsaMini/AoA`（`\b` 必需，否则会命中 `StdTask.system_prompt` 里同步的 `self._build_system_prompt(...)` 和 `log_initial_prompt(`），每个命中行必须含 `await`、或是 `async def`、或是注释 / docstring；裸 `def` 不过，这样测试文件里同步写的钩子 override（如 `test_user_operations.py:154` 那个从不运行的 `Another`）也能抓到。今天这个正则 35 个命中，其中既非 `await` 也非 `async def` 的是 §4 要改的调用点和定义、`model.py:13122`，以及注释 / docstring 行 12667、13350、13539、14688。pyright 对 `model.py` 里两个钩子调用点漏 `await` 已能报错，grep 是测试文件、`is None` / `is not None` 形状（`model.py:13526`）和每个 `def` 是否 async 的唯一检查。测试输出里 grep `was never awaited`。
3. **golden 的产生。** `Tests/<name>.yml` 不存在时 harness 会把测试输出写成新 golden 并报通过（`test.py:105-106`），所以：`TaskPlacement` 先把完整的预期 `Tests/TaskPlacement.yml`（测试写出的每一行，全部 True，照测试源码读出）给 owner 批，批后手工写入，然后才跑 `test_AoA.py`，绝不让一次运行创建它；`TacticPrompt` 改后第一次运行**预期失败**，留下 `Tests/TacticPrompt.diff` 和 `TacticPrompt.actual.yml`，diff 必须恰好是第 15 行的改标签，多一行就是代码缺陷而非 golden 更新；diff 给 owner 看、owner 定措辞，批后手工改 golden 第 15 行再跑到通过。然后起 REPL（`isabelle REPL -l Minilang -d . … 127.0.0.1:6666`），`python -u ../../test_AoA.py -f TacticPrompt,TaskPlacement,MemorizeGuard,WriteMemoryGate,ReadMemoryGate,GoalHints_Minilang,TacticDeclaration_Minilang > <scratchpad>/aoa.txt 2>&1`，一次一个运行。
4. `pytest test_user_operations.py`；脚本式单测 `test_corrupted_sample.py`、`test_deep_restart.py`、`test_session_quit.py`、`test_budget_exempt.py` 各跑一次。
5. 不涉及 `.ML`，REPL 无需因本改动重启。

## 10. 不做

- 把 session 拆成显式参数（`tasks/AoA-learning/PLAN.md` 78 行的待定项）。
- driver 侧 `has_system_prompt` 属性；"driver 可覆写 prompt" 的机制。
- `Role_*`、`TOOL_*` 的搬迁（§5 的反转使之不必要）。
- 去掉 `initial_prompt` 的 `has_system` 参数，或把两段无 system prompt 的长版留在 `Session` 不搬（owner 决定保留并搬迁）。
- 彻底去掉 system prompt 的 `None`。
- 三个早于本方案的问题，记录不修（2026-10-16：第二条，以及第三条里 ClaudeCode 的部分（API driver 不带上下文模式同理），由 `TASK_PROMPT_FORK_PLAN.md` 修掉；第三条里 API driver 带上下文模式的部分也已修（`_run_fork` 的 fork 对话改放在 fork 对象上，`driver_api.py`）；Codex 的部分也已修（2026-10-16，按 `ai-artifacts/review/CODEX_NESTED_FORK_PLAN.md`：交互 fork 以 ephemeral `codex exec fork` 从发起方 fork 的那条线程分出，命令由 fork 自己拼、带发起方的 model instructions 文件；`_fork_lock` 与 rollout 备份删去；线程 id 在 `thread.started` 处记录；由交互 fork 再起的 fork 分出的是同一条 major / worker 线程，看不到外层 fork 的提问（owner 接受）；记录在 `TASK_PROMPT_FORK_PLAN.md` §2）：无上下文的 Retrieve fork 拿到 `LearningTask` 那句 note 却没有 Isar 块；`_tactic_prompt_block` 对 interaction fork 的排除建立在"fork 看不到父会话 prompt"这个不成立的前提上；由 interaction fork 再起的 fork（交互式检索）至多收到为 `Role_Interaction` 构造的 system prompt，没有 major 的 task 文字、没有 tactic 段、没有 declarative guidance：ClaudeCode 发这份（`driver_claude_code.py:873`）；API driver 的带上下文模式（默认）既不发 system prompt 也不带对话，它复制的是发起方自己的 `_messages`（`driver_api.py:773`），而 interaction fork 不经 `_api_loop`、这一列表为空；Codex 的 resume 命令不带 model instructions 文件（interaction fork 不写它，`driver_codex.py:197-198`、`434-436`）。
