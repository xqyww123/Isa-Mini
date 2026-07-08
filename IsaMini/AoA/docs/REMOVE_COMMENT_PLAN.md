# 计划：完全删除 AoA 的 comment（注释掉步骤）机制

> 状态：**待批准**。本文件是实施蓝图，尚未动任何代码。
> 行号为撰写时快照，会漂移——实施时以符号名 + grep 为准，行号仅作定位提示。

---

## 0. 背景与关键事实（已核实）

**comment 机制 = 把证明步骤「注释掉」（禁用）**，与注释掉源码同理：节点被打上 `COMMENTED`
状态，求值/组装时跳过，可用 `uncomment` 原地复活并重新求值。它**不是**给节点挂自由文本注解
——`Node` / `Parsed_Opr` / `Minilang_Operation` 上没有任何 `comment` 文本字段；状态完全由
`node.status.status == COMMENTED` 承载。

已核实的关键事实：

1. **纯 Python 概念**。`library/proof.ML`、`Agent/agent_server.ML` 等所有 `.ML`
   对 `comment`/`COMMENTED` **零命中**（ML 里的 `\<comment>` 是 Isabelle 源码注释语法，无关）。
   → **不改任何 `.ML`，不需重启 REPL，不需 rebuild heap。**
2. **不进 proof-cache、不进 replay**。COMMENTED 节点不产出 op，缓存里存的是已执行的 op 序列，
   与 comment 无关。`Tests/Test_Define_CommentOracle.proof-cache` 记录的是 Define 已执行的证明。
3. **comment 与 delete 的唯一实质差异 = 可逆活体旁置**：`recall_removed` 对 delete 的归档
   **只读**（`tools/cc_recall_removed.jsonc`，不能插回树）；而 `uncomment` 能原地恢复。
   删掉 comment 即失去这一能力——已与用户确认接受。

---

## 1. 已锁定决策（用户拍板）

| # | 决策点 | 结论 |
|---|---|---|
| D1 | `COMMENTED` 枚举值 | **连根删除**（不留死代码） |
| D2 | 放弃挣扎 subagent（difficulty→abandon） | 改为**仅取消 subagent**，不注释、不删除；节点保持原样（FAILURE、仍未完成、可见） |
| D3 | 放弃选项文案 | `"1. Abandon — cancel the sub-agent"`（只说取消） |
| D4 | 大删确认交互 | **去掉「改成注释」选项**，只留 cancel / proceed |
| D5 | 大删 `null` 答案 | **不设默认**：`answer.index is None` → `raise Interaction_BadAnswer(...)` 要求 agent 显式重答 |
| D6 | 大删提示语气 | **中性告知体量**（列出将丢弃的已证明步骤数，不做推荐倾向） |
| D7 | 7 个 comment 专属测试用例 + fixture + golden | **删除** |
| D8 | `SubtreeStats` 测试 | **改写**去掉 COMMENTED 断言；golden 变更**先给 diff、经用户复核后**再改 |

**待用户补充（不阻塞实施）**：删除动机（"降复杂度/几乎没用" vs "引入了 bug/语义混乱"）——只影响
第 3 步化简那 ~40 处守卫时的把握分寸。

**用户可见文案（按项目规则不得擅自措辞）**：D3/D6 已定方向；D5 的 `BadAnswer` 消息正文与
D6 的具体提示正文见 §4，均标注「待确认措辞」，实施前需用户最终敲定。

---

## 2. 影响面清单（规模）

| 文件 | 命中 | 说明 |
|---|---|---|
| `model.py` | ~91 | 枚举值、两个方法、~40 处 `!=/== COMMENTED` 守卫、渲染分支、stats/unfinished、两个交互类 |
| `mcp_http_server.py` | ~31 | 工具 schema/注册/dispatch/逻辑、两个交互流程分支、import |
| `prompts.py` | 6 | `comment_message` + import |
| `driver_claude_code.py` | 1 | 工具名映射 |
| `tools/cc_comment.jsonc` | 整文件 | 删除 |
| `test.py` | ~123 | 7 个用例 + `SubtreeStats` 改写 |
| `Tests/*` | 8 yml + thy/cache | 删除 7 组 + 改 `SubtreeStats.yml` |

> **实施纪律**：不机械替换。每处以 grep（`COMMENTED`、`\.comment\(`、`uncomment`、
> `TOOL_COMMENT`、`CommentOutcome`、`EVALUATION_COMMENTED`）逐一定位，人工判等价后再改。
> 收尾用全局 grep 确认零残留（Isabelle `\<comment>` 除外）。

---

## 3. `model.py` 核心拆除

### 3.1 枚举与状态常量
- `EvaluationStatus.Status`（~1179）：删 `COMMENTED = "commented"`。
- （~1192）：删 `EVALUATION_COMMENTED` 单例。
- `_status_can_continue`（~1194-1195）：
  - 现：`return status in (SUCCESS, COMMENTED)`
  - 改：`return status is EvaluationStatus.Status.SUCCESS`

### 3.2 mutator 与 outcome
- `Root.comment`（~10821-10846）、`Root.uncomment`（~10848-10867）：整体删除。
- `CommentOutcome`（~10869-10872 NamedTuple）：删除。

### 3.3 统计 / 完成度
- `subtree_stats`（~4547-4554）：删「COMMENTED 子树计 `(0,0)`」的特判分支，回落到基类正常计数。
  - ⚠️ 复核：确认删掉该分支后，非 COMMENTED 路径的计数逻辑仍完整（原分支只是提前 return）。
- `unfinished_nodes` / 新完成 delta（~12567-12576）：删除「COMMENTED 计为 finished / 跳过」的注释与守卫。

### 3.4 refresh / 组装 / 上下文的 ~40 处守卫
逐处将「跳过 COMMENTED 子节点」的条件展开为无条件（因再无节点会是 COMMENTED）。已知站点：
- 提前 return 自身为 COMMENTED：`~4158`、`~5048`、`~5056`、`~7809`
- 渲染分支：`~4170-4171`（`"commented, "`）、`~4212-4214`（`"(commented out)"`）
- **`_cancel` 正向成员守卫（C2 — 勿当渲染分支整条删）**：`Node._cancel`（`~4282-4284`）与
  `StdBlock._cancel`（`~5584-5586`）均为 `if self.status.status in (CANCELLED, COMMENTED): return`
  （"别重复取消已终结节点"）。**只从元组里删掉 `COMMENTED`、保留 `CANCELLED`**，化简为
  `if self.status.status is EvaluationStatus.Status.CANCELLED: return`；**绝不整条删除**（否则误伤 CANCELLED 行为）。
- refresh 链 `can_continue` 守卫：`~5412`、`~5421`、`~5430`、`~5435`、`~5463`、`~5651`、`~5737`、`~5766`、`~5861`、`~5891`、`~5924`、`~5933`
- 上下文组装（`_ctxt_of_filling` 等）：`~5802`
- fixed-var/tvar/fact walkers：`~9838-9874`、`~10633-10647`
- 设计注释（无代码，仅说明"不存 `_closed_by`"）：`~5190-5191`、`~10840-10842` → 删除或改写为不再提 comment
- ⚠️ 每处判断分两类：（a）负向 `if c.status.status != COMMENTED: <body>` → 直接 `<body>`；
  （b）正向成员 `if status in (X, COMMENTED): ...`（如上 `_cancel`）→ 只摘掉 `COMMENTED`，保留其余成员。
  凡与**其它状态**组合的守卫，一律只去掉 COMMENTED 一项。

### 3.5 工具常量与提示
- `TOOL_COMMENT`（~2616）删除；从 `ALL_PROOF_TOOLS`（~2637）移除引用。
- 系统提示工具清单行（~11810 `"- {comment}: Comment out or uncomment proof steps"`）删除。

### 3.6 交互类改写
**`Interaction_DifficultyEvaluation`（~3065-3098）**
- docstring（~3069）：`"...abandon the step (auto-cancel + comment out)"` → `"...abandon the step (cancel the sub-agent)"`。
- prompt 选项（~3091）：
  - 现：`"  1. Abandon — cancel the sub-agent and comment out this step\n"`
  - 改（D3）：`"  1. Abandon — cancel the sub-agent\n"`
- `answer`（~3094-3098）：不变（None→0 continue，1→abandon）。

**`Interaction_ConfirmLargeDelete`（~3257-3316）**
- 移除 `comment_available` 构造参数与 `self.comment_available`（~3271-3275）。
- docstring（~3258-3264）：改为「答案是 `"cancel"` / `"proceed"`；`null` 不接受，抛
  `Interaction_BadAnswer` 要求显式选择」。
- `prompt`（~3277-3306）：删掉整个 `if self.comment_available:` 的 comment 选项分支；
  正文按 D6 中性告知（保留「列出各步 total/proved」的枚举），选项固定为：
  ```
    0. Cancel the deletion and keep everything as is.
    1. Proceed with the deletion anyway.
  ```
  （具体正文见 §4，待确认措辞。）
- `answer`（~3308-3316）：改为（D5）
  ```python
  async def answer(self, answer: 'AnswerIndex') -> str:
      if answer.index is None:
          raise Interaction_BadAnswer(<D5 消息，见 §4，待确认措辞>)
      _check_index(answer.index, 2)
      return ("cancel", "proceed")[answer.index]
  ```

---

## 4. 用户可见文案草案（**待用户最终确认措辞**）

- **D3 放弃选项**（已定方向）：`  1. Abandon — cancel the sub-agent`
- **D6 大删提示正文**（中性告知体量，草案）：
  ```
  You are about to delete {noun} containing substantial completed work:
    - step {id}, total {N} operations, {M} proved
  Deleting this discards that proved work; it can only be viewed afterwards via
  `{recall_removed}`, not restored into the proof.

    0. Cancel the deletion and keep everything as is.
    1. Proceed with the deletion anyway.
  Call `{answer_index}` with your choice.
  ```
- **D5 `BadAnswer` 消息**（草案）：
  ```
  You must choose explicitly: answer `0` to cancel and keep the work, or `1`
  to proceed with the deletion. There is no default for this decision.
  ```

---

## 5. `mcp_http_server.py`

- import（~52、~54）：移除 `TOOL_COMMENT`、`CommentOutcome`。
- **`_MUTATION_TOOLS` frozenset（C1 — 第三处 `TOOL_COMMENT` 引用）**（~276）：从
  `_MUTATION_TOOLS = frozenset({TOOL_EDIT, TOOL_DELETE, TOOL_COMMENT, ...})` 中删除 `TOOL_COMMENT`
  （该集合在 ~314 被 `_check_tool_permission` 使用）。这是 mcp 侧对应 `ALL_PROOF_TOOLS:2637` 的同类集合，
  须与 model.py:2616 定义删除、mcp:52 import 删除同一次提交。
- schema 载入（~115 `_cc_comment_schema`）删除。
- 工具注册表（~2071 `"comment": {...}`）删除该条目。
- dispatch（~2607-2612 `case "comment":`）删除。
- `_comment_tool_logic`（~647-691）整函数删除。
- **大删触发点**（~566-586）：删 `comment_available` 计算（~568-569）、删 `choice=="comment"`
  分支（~576-585）、`Interaction_ConfirmLargeDelete(entries)` 不再传 `comment_available`；
  `choice` 只可能是 `"cancel"`/`"proceed"`（proceed 落入既有正常删除路径）。
- **放弃 subagent 路径**（~1945-1964）：
  - `choice==1` 分支：保留 `await node.aclose_all_subagents()`；**删除** `await session.root.comment([node.id])`
    及其 try/except（~1947-1950）。
  - **flush 无条件保留（C6 — 判据修正）**：`P._write_newly_completed(session, buf)`（~1964）
    **无条件保留**，**不再**挂"若完成度不翻转就化简"这个门槛——flush 的真正作用（把此刻真实完成的项
    标记为已宣告，防止之后被无关编辑**误归属**，见 ~1955-1959）与 comment 无关、D2 后依旧成立。
    重写 ~1952-1961 注释：删掉两句现已为假的话——"Auto-commenting the node … can flip the scope's
    finishedness" 与 "The just-commented node itself is excluded … by Session.newly_completed_topmost"——
    改述真正的排除理由：被放弃节点保持 UNFINISHED（有 pending goal），本就被 `newly_completed_topmost` 排除。
  - docstring（~1765 `"(auto-cancel + comment)"`）→ `"(cancel the sub-agent)"`。

---

## 6. `prompts.py` / `driver_claude_code.py`
- `prompts.py`：删 `comment_message`（~171-192）；import（~8）移除 `TOOL_COMMENT`、`CommentOutcome`。
- `driver_claude_code.py`（~73）：删 `"comment": "mcp__proof__comment"` 映射。

---

## 7. 测试与 golden

### 7.1 删除 7 组专属用例（D7）
用例函数（`test.py`）+ 其 `.thy` fixture + `Tests/*.yml`：
| 用例 | test.py | fixture | golden |
|---|---|---|---|
| Comment1 | ~16617 | Test_Comment.thy | Comment1.yml |
| CommentHave | ~16677 | Test_CommentHave.thy | CommentHave.yml |
| CommentUnfinishedGoal | ~16730 | Test_CommentUnfinishedGoal.thy | CommentUnfinishedGoal.yml |
| Define_CommentHole | ~16876 | Test_Define_CommentHole.thy | Define_CommentHole.yml |
| Define_CommentOracle | ~16958 | Test_Define_CommentOracle.thy | Define_CommentOracle.yml + `.proof-cache` + `.proof-cache.lock` |
| CommentRoundTrip | ~17125 | Test_CommentRoundTrip.thy | CommentRoundTrip.yml |
| CommentClosingStep | ~17165 | Test_CommentClosingStep.thy | CommentClosingStep.yml |

- 覆盖率说明：`Define_CommentHole/Oracle` 测的是「Define 与旁置的交互」；已有
  `Test_Define_DeleteOracle.thy`（~17023）是 delete 版对照，Define 的 delete 覆盖仍在——判定覆盖不受损。

### 7.2 改写 `SubtreeStats`（D8）
- `test.py`（~17207、~17281-17291）：删掉「构造 COMMENTED 子树、断言计 `(0,0)`」的部分，
  保留其余非 comment 断言；若整测试仅为验证 comment 计数，则与用户确认是否整体删除。
- `Tests/SubtreeStats.yml`：**必然变更**。按硬规则：先跑该测试产出 `Tests/SubtreeStats.diff`
  与 `.actual.yml`，**把 diff 呈给用户复核批准后**才写入新 golden。**不擅自覆盖。**

---

## 8. 验证
1. 无 `.ML` 改动 → 无需重启 REPL / rebuild。
2. `grep -rin "COMMENTED\|\.comment(\|uncomment\|TOOL_COMMENT\|CommentOutcome\|EVALUATION_COMMENTED\|comment_message" .`
   确认零残留（Isabelle `\<comment>` 除外）。
3. `python -c "import ...model, mcp_http_server, prompts, test"` 确认无 import/引用错误。
4. 跑 `SubtreeStats`（改写后）：`python -u ../../test_AoA.py -f SubtreeStats > /tmp/aoa_subtreestats.txt 2>&1`，单个跑、重定向。
5. 抽跑几个与删除/交互相关的既有用例（如 delete、difficulty 相关）确认未回归；一次一个、勿并行（共享 6666 REPL）。
6. （C6）§5 已决定 flush **无条件保留**，不再以"完成度是否翻转"为化简判据；此处仅需确认放弃路径
   编辑后 import/逻辑无误，无需再拿"翻转与否"做去留决策。

---

## 9. 建议实施顺序
1. §3 model.py 核心（枚举→方法→守卫→交互类）——先让模型自洽。
2. §5/§6 管线（工具、驱动、prompts）——去掉入口。
3. §7.1 删测试与 fixture/golden。
4. §7.2 改 `SubtreeStats` → 出 diff → **等用户批准 golden**。
5. §8 验证 + grep 清零。
6. 提交（直接在 `main`，绝不建分支/stash/clean）；commit message 完整描述本次删除，若扫入他人未提交改动亦一并说明。

---

## 10. 风险与谨慎点
- **§3.4 守卫化简**是最大风险区：组合条件里只摘 COMMENTED，别误删其它状态判断。
- **golden 触碰**：仅 `SubtreeStats.yml`，且必须先 diff 后批准（硬规则，无例外）。
- **放弃路径完成度结算**：先保守保留 flush，实测后再简化。
- 用户可见文案（D3/D5/D6）实施前需用户最终敲定，不擅自定稿。
