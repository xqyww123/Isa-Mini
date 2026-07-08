# 计划：Runaway-loop 检测 → 强制 context Restart（方案甲）

> 状态：**待评审 / 未实现**。本文件只是方案，代码尚未改动。

## 1. 动机与证据

日志 `~/.isabelle/Isabelle2025-2/log/AoA/F42D9D9FB_1E7F6A2/llm_interaction.json` 的尾部是
**39 次连续完全相同的 `query` 调用**：
- thinking 文本逐字相同；
- `term_patterns` 参数相同（`["(?x :: real) ^ (2::nat)"]`）；
- 工具返回每次都是 `65 match 15 shown — 0 new, 15 shown earlier`。

模型在一个几乎不变的上下文里确定性地重复同一动作。此死循环绕过了所有现有兜底：

- **between-turn 的 retry 上限**（`_retry_count` / `max_retries=5`，在 `_sdk_loop` 中检查）永不触发——因为模型**从不结束本轮**，这 39 次调用都在**同一个** turn 内，`receive_response()` 从未返回。
- 唯一的 **mid-turn 守卫** `check_budget()`（`ToolExecutor.execute`，`mcp_http_server.py`）只在 wall-clock / 总调用数 / retry 上限时触发，**从不**因“重复”触发——于是循环一直烧到全局超时。

## 2. 设计（方案甲，用户已选定）

### 2.1 插入点
`ToolExecutor.execute`（`mcp_http_server.py`），**紧跟现有 `check_budget()` 守卫之后**。
该函数注释明确标注为 *“the single dispatch chokepoint for BOTH drivers”*——ClaudeCode
SDK 驱动的 MCP `call_tool` 与 in-process 的 APIDriver 都经此分发内建 proof 工具。放在这里
天然对两个驱动都生效。

### 2.2 新增状态
`Session.__init__`（`model.py`，紧邻 `_retry_count` 初始化处），跨 restart 存活：
```python
self._repeat_sig: str | None = None   # 上一次 proof-tool 调用的签名
self._repeat_count: int = 0           # 连续相同次数
```

### 2.3 常量与导入
- `ToolExecutor` 类常量：`_LOOP_REPEAT_THRESHOLD = 5`
- **无需**再导入 `Restart`——改用现有的 `Session.request_restart()`（见 2.4，评审修订 #2）。

### 2.4 检测逻辑（评审后定稿）
仅当 `session.is_major`，**且当前没有 park 中的非 forking 交互**（`_suspended_task`/
`_nf_pending_interaction` 均为空——评审 #1）：
```python
if session.is_major and self._suspended_task is None \
        and session._nf_pending_interaction is None:
    sig = f"{name}\x00{json.dumps(arguments, sort_keys=True, default=str)}"
    if sig == session._repeat_sig:
        session._repeat_count += 1
    else:
        session._repeat_sig = sig
        session._repeat_count = 1
    if session._repeat_count >= self._LOOP_REPEAT_THRESHOLD:      # 第 5 次
        session._repeat_sig = None
        session._repeat_count = 0
        session.log_AoA_opr(f"Loop detected: {self._LOOP_REPEAT_THRESHOLD} identical `{name}` calls in a row; restarting context")
        session._log_meta("LOOP_RESTART", tool=name)
        await session.request_restart()   # = _reset_view_state() + Restart + interrupt
        return ("Loop detected: 5 identical calls; restarting context.", True)
```
放在**权限检查之前**（与现有 budget 守卫同位）。返回文案为**纯日志文案**——restart 会丢弃
整段对话，模型看不到（见 §5.1）。

### 2.5 作用域
**仅主 agent**（`is_major`，即 `parent is None` 的 planner）。Worker / interaction fork
**不**触发 restart——它们不经 `_sdk_loop` / `_api_loop`（worker 走 `WorkerHandle.run_until_yield`，
fork 走 `_run_fork`），`Restart` 对它们无效。它们的 runaway 交由全局预算/超时兜底。此为
用户接受的取舍。

### 2.6 放弃上限
**不设**。若 restart 后模型再次陷入同一 loop，则再次 restart。极端“重启即再 loop”的
乒乓情况由现有全局 wall-clock / 总调用数预算（`check_budget`）最终终止——不会真正无限跑。

## 3. 为什么 Restart 能打破循环

`Restart.is_terminal = False`：
- `check_budget()` 读到 `quit_info is not None` 时返回 `is_terminal`，即 `False`——**不会**把
  Restart 误当终止，也**不会**覆盖它。
- `_sdk_loop`（`driver_claude_code.py` ~L556–571）：`interrupt()` 使 `receive_response()`
  提前结束 → 内层 while 退出 → `if not isinstance(quit_info,(Restart,Refresh)): break` 为假 →
  进入 restart 分支，清 `quit_info`、记 `CONTEXT_RESTART`、外层 while 重开新 `ClaudeSDKClient`
  并用全新 `initial_prompt()`。
- `_api_loop`（`driver_api.py` ~L1396–1424）：`interrupt()` 置 `_interrupted=True` → 边界检查
  break → 识别 `Restart` → 用 `_initial_messages()` 重建全新 `_messages`。

全新上下文**丢弃**了驱动确定性循环的那一堆相同历史 turn，从而打破循环。

## 4. 覆盖范围

**计入**（走 `execute` 的 proof-MCP 工具）：`query`、`edit`、`delete`、`comment`、`report`、
`request`、`refresh`、`answer_*`、`subagent`、`cancel_subagent`、`recall_removed`、`write_memory`。
日志里 loop 的 `query` 属于此类。

**不计入**：`recall`(→Read)、Grep、Write、Edit(文件)——这些是 SDK 原生工具，不经 `execute`。

## 5. 已定项（原“未定项”，评审后解决）

1. **返回给模型的文案**：经核查，restart 会**整体丢弃**当前对话（`_sdk_loop` 新建 client 用
   `initial_prompt()` 不 resume；`_api_loop` 用 `_initial_messages()` 替换 `_messages`），模型
   **看不到**这句话——它只进 `interaction.yaml` 等日志。故定为纯日志文案：
   `"Loop detected: 5 identical calls; restarting context."`
2. **是否重置检索去重**：**是**。改用 `request_restart()` 后天然会 `_reset_view_state()`
   （清 `seen_entities`），同一 `query` 不再返回 `0 new`（评审 #2）。

## 6. 明确不做

- 不设放弃/surrender 上限（方案甲，用户 2026-07-08 再次确认）。
- 不处理 worker / interaction fork 的 loop。
- 不检测非连续的短周期循环（如 A,B,A,B）——仅“连续完全相同”。

## 7. 评审修订（2 轮对抗评审，wf_1d675598-3f3）

- **#1（高危，已并入 2.4）**：park 中的非 forking 交互期间**跳过**检测。否则第 5 次相同
  `answer_*` 会触发 restart，而 restart 不走 `close()`，`_suspended_task` /
  `_nf_pending_interaction` 残留 → 之后所有 edit/delete 被 `"An operation is in progress"`
  拒绝，整局卡死。
- **#2（中，已并入 2.3/2.4）**：改用现有 `Session.request_restart()` 而非内联 `Restart()`——
  自带 `_reset_view_state()`、与现有两处 restart 入口一致、无需 import `Restart`。
- **#3（中，维持方案甲）**：不 bump `_retry_count`、不设 cap。修 #2 后 re-loop 概率大降，
  churn 风险随之减小；极端情况仍由全局预算兜底。
- 另 4 条低质量意见经对抗轮淘汰（denied 计数驱动差异 / `refresh` 误判 / 逐字节签名抖动 /
  残留签名误触发），详见对话汇报。
