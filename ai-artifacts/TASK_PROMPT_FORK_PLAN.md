# 交互 fork 的 system prompt 统一为发起方的（2026-10-16，session「AoA Task」）

owner 的决定（2026-10-16）：采用统一；task 钩子的 `role` 收窄为 `Role_Major | Role_Worker`；`TacticPrompt`、`TaskPlacement` 两个测试用真 fork 重写、golden 相应改；文档文字（非 agent 可见、不涉设计）由我自决。本文只把决定落到文件上。紧接 `TASK_PROMPT_PLAN.md`（下称主方案）的工作树状态之上，major 与 worker 的 prompt 逐字节不变，一级交互 fork 收到的也不变（今天就是发起方的 system prompt）；变的只有由交互 fork 再起的 fork（§2）。

## 1. 事实

- 三个 driver 给交互 fork 发的都是**发起方**的 system prompt：`driver_claude_code.py:873`、`driver_api.py:788`（不带上下文）与 `773`（带上下文复制发起方消息，首条是它的 SystemMsg）、`driver_codex.py`（写本文时是 resume 发起方的线程；2026-10-16 起是 ephemeral `codex exec fork` 从发起方 fork 的那条线程分出，见 §2），都带发起方的 model instructions 文件。与 forking 模式无关。
- 为 `Role_Interaction` 构造的 system prompt 只在两处被算：ClaudeCode 给 fork 跑 `initialize`（`driver_claude_code.py:235`，算完不用）；交互 fork 再起 fork 时（交互式检索，`retrieval.py:852-858`），873 / 788 行的 `self` 是那个交互 fork。
- 交互 fork 从不算、不发初始消息（`model.py:13307-13309`）；它的第一条 user 消息是交互的 prompt。

## 2. 改动

### `model.py`

- `Session.system_prompt`：role 是 `Role_Interaction` 时返回 `await self.parent.system_prompt()`（fork 的 `parent` 恒非 None，`assert`）。嵌套 fork 由此在 ClaudeCode 和 API driver 不带上下文模式下得到发起方链条尽头那个 major / worker 的 prompt；Codex 的嵌套 fork 原本 resume 时命令里不带 instructions 文件（路径只记在写了文件的 session 对象上，fork 对象里是 `None`）：owner 2026-10-16 交由我自决，`driver_codex.py` 的构造函数改为 fork 继承 parent 的 `_model_instructions_path`（worker 在 `initialize` 里仍写自己的）。但这一行修不好 Codex 的嵌套 fork：嵌套 fork 在共享、不可重入的 `_fork_lock` 上死锁（`_run_fork` 整个 resume 期间持锁）；而且 codex-cli 0.163.0（2026-10-16 升级）上 Codex 的 fork 整体不可用——`resume` 之后的 `-s` 被拒绝（已改为选项前置，这也修好了 major 的 retry turn），第二个进程不能 resume 正在跑的线程（writer lock），major 第一次 exec 期间 `_codex_session_jsonl` 为 None 触发断言。owner 2026-10-16 决定：Codex fork 机制按 `ai-artifacts/review/CODEX_NESTED_FORK_PLAN.md`（ephemeral `codex exec fork`、在 `thread.started` 记 thread id、去掉锁与 rollout 备份）另立方案重做，允许付费真机验证。已于 2026-10-16 落地：每个交互 fork 自己拼 `codex exec <选项> --ephemeral fork <线程 id> <prompt>`（选项一律在子命令之前，`_codex_exec_cmd` 一个装配点），从发起方 fork 的那条线程分出；fork 自己的线程不落盘，请求沿用该线程的 prompt cache key；`_fork_lock`、rollout 备份、`_codex_session_jsonl`、`_find_session_jsonl` 删去；线程 id 在 `thread.started` 处记入 `_codex_session_id`（交互 fork 不记、保持继承值），`_codex_loop` 进入、Refresh、Restart 时清空；重试 attempt 重新 fork，提示文字是第一次的全文加一句提醒（owner 定稿）；由交互 fork 再起的 fork 分出的是同一条 major / worker 线程，看不到外层 fork 的提问（owner 接受）。单测 `test_codex_fork.py` T1–T9。同日 `mcp_http_server._tool_schemas_for` 对交互 fork 沿 `parent` 上溯到第一个非交互 session 取基础工具集（owner 批准）：Codex 与 ClaudeCode 的 MCP 工具表于是与 fork 续写的对话一致，fork 多出 `subagent` / `cancel_subagent` 两条定义，调用仍被 `_check_tool_permission` 拒绝。API driver 带上下文模式的嵌套 fork 原本复制到的是交互 fork 的空 `_messages`（`_run_fork` 把 fork 的对话放在三个局部变量里）：owner 2026-10-16 同意修，`_run_fork` 改为直接用 fork 对象的 `_messages` / `_last_response_id` / `_msgs_sent_through`——对话住在 session 上，和主循环同形，嵌套 fork 按现有逻辑复制或续写它，前缀与发起方一致、缓存可复用。工具表同理：`_tools` 存在 session 上（主循环算一次），fork 继承发起方的，请求的 tools 前缀也一致。一轮的工具结果在整轮结束后再追加（与主循环同形），于是从一轮的第二个调用起的 fork 能答全该轮的每个调用。fork 结束时用 `_accumulate_sub_session_costs` 把 fork 计数器里的东西折回发起方：fork 自己的 token 本就当场记在发起方上，它的计数器里是它自己的时间和嵌套 fork 的用量。单测：`test_corrupted_sample.py` §3b。
- `Session._compute_initial_prompt`：`assert not isinstance(role, Role_Interaction)`——交互 fork 没有初始消息；没有任何路径为它算（§1）。
- `_tactic_prompt_block`：删 `if self.is_interaction: return ""` 与 docstring 里那句前提。

### `task.py`

- 四个钩子与三个构造函数的 `role` 注解改为 `Role_Major | Role_Worker`（内联联合，不起新名）；`Role` 不再导入。
- `_build_system_prompt`：删 `Role_Interaction` 正文（`else` 分支）与 `task_system` 在它末尾的插入点；`elif isinstance(role, Role_Worker)` 改 `else`；工具行里 `isinstance(role, (Role_Major, Role_Worker))` 的守卫撤掉、块体缩进回一层；注释里关于 `Role_Interaction` 正文的话删去。
- `_lemma_guidance`：末尾的 `suffix` 三元式退化为常量（走到那里的只有 major）；docstring 随改。
- `_compute_initial_prompt_base`：`planner_hint ... if isinstance(role, Role_Major) else ""` 退化为无条件（收窄后 `elif/else` 分支里 role 只能是 major）。
- `Task` docstring：role 是 major 或 worker 的；交互 fork 没有自己的 system prompt 或初始消息，收发起方的 system prompt、只在复制的对话里看到发起方的初始消息。
- 字节：major 与 worker 的两段 prompt 逐字节不变（harness 验证）。

### 测试

- `test.py`：`_stub_interaction_role()` 改为 `_subsession(parent, role)` 与 `_interaction_fork(parent)`——以构造函数 `Session(parent=parent, role=role)` 造一个真的子 session（基类 `Session` 没有 `_make_fork`），在 `contextvars.copy_context().run` 里造，照 driver 的做法，上下文里绑定的 session 不受影响。
- `TacticPrompt`：worker 那例不变；interaction fork 那例改为 `fork = _interaction_fork(session)`，断言 `await fork.system_prompt() == await session.system_prompt()`，仍写 `--- interaction fork ---` 与段落尾部。**golden 预期 diff 只有第 21 行**：`system prompt: (no block)` 变为与第 19 行（worker）相同的段落文本。
- `TaskPlacement`：system prompt 那圈只跑 major 与 worker；之后在 `_Marked` 下断言 `await fork.system_prompt() == await session.system_prompt()`（含 task 文字），写一行 `interaction fork: system prompt is that of the session that launched it, task text included: True`；再以普通 `assert`（不加 golden 行）检查从真 worker 子 session 起的 fork、以及再嵌套一层的 fork，都等于该 worker 的 system prompt。**golden 预期 diff**：原第 5、6 行（interaction fork 的两行）换成这一行。
- 两份 golden 先跑出 diff 给 owner 看，批后手写。
- `task_prompt_bytes.py`：矩阵去掉 interaction 行，`compare` 忽略改前文件里的 interaction 记录；其余 0 mismatches。

### 文档

- `USER_OPERATIONS.md` §4.2：role 的定义句改为 §2 `Task` docstring 的内容；删 "(for an interaction fork, it ends the body)"。
- `TACTIC_DESIGN.md` 27 行决定格：「交互 fork 不显示」改为「交互 fork 收到发起方的 system prompt，段落随之可见」，右格记 2026-10-16 改为统一；255 行删交互 fork 的门控与"沿用 experience_hint"那句；306 行 `TacticPrompt` 的预期改为「major 与 worker 有；交互 fork 收到发起方的那份」；286 行决策汇总的末句同 27 行。
- `EXPERIENCE_MEMORY.md` 339-340：「interaction forks get only the `query` rewrite」改为「an interaction fork is sent the system prompt of the session that launched it」。
- 主方案：§2.1 interaction 那行、§2.3、§10 第二、三条各加一句指向本文。

## 3. 验证

harness compare（major / worker 行 0 mismatches）；pyright 六文件多重集不变；grep 审计；`pytest test_user_operations.py`；四个脚本测试（`test_deep_restart.py` 有嵌套 fork）；REPL：`TacticPrompt,TaskPlacement,MemorizeGuard,WriteMemoryGate,ReadMemoryGate`，前两个第一次预期失败在 golden 比对、diff 如 §2 所述。
