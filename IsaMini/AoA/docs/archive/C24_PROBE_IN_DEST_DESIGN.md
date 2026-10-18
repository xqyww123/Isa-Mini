# 设计文档：C24 —— the probe 的每个 round 直接执行进 destination state

> **Status:** ARCHIVED — this design shipped. Historical record, no longer maintained;
> the code is the authority (`SubgoalMaker._run_the_probe`, `_beginning_opr_with_insts`,
> `test_post_inst_probe.py`, the `PostInstRoundFailure` model test); the current description
> is `TACTIC_DESIGN.md` §6.1 and §13 item 19.
> **Date:** 2026-10-11
> 行号是 dd7707d 的，用 `git -C contrib/Isa-Mini show dd7707d:<path>` 核对。
> 路径不以 `/` 开头的，相对 `contrib/Isa-Mini`；两份计划文档在主仓库根目录（`AOA_SCHEMATIC_VARIABLE_PLAN.md`、`AOA_INITIAL_GOAL_SCHEMATIC_PLAN.md`）。
> 术语：见 §2。全文一个概念只用一个词；对 git 的提交一律写"git 提交"，节点保留下来的那次执行不用"提交"这个词。

---

## 0. 审批状态与决策表（务必先看）

owner 已于 2026-10-10 采纳 C24 的**方向**（`IsaMini/AoA/docs/TACTIC_DESIGN.md:381`，§13 第 14 条），并于 2026-10-11 对下表每一行作出裁定。"裁定"列是最终结论；"备选"列是被比较过的做法，留作记录。

| 编号 | 事项 | 裁定 | 备选（未采纳） | 依据 |
|---|---|---|---|---|
| D1 | C24 的形状 | 采纳：每个 round 都把 beginning op 执行进 `dest`，收敛的那个 round 的执行结果就是节点保留的结果；删去 scratch state、它的 `reset`、循环后的重跑、今天的两处 `break`。具体位置见 D22，op 的构造见 D3 | 维持现状。裁判明言：不采纳时也**不要**做"只把 round 0 的错误原样抛出"的最小改法（加特例、成功仍跑两次、round k ≥ 1 失败仍不报告、丢掉失败 op 的 `proof_oprs.yaml` 记录） | 评审 C24；三位裁判一致 |
| D2 | round 0 的 op 从哪来 | 不再是问题：round 0 就是 `StdBlock._refresh_the_beginning_opr` 对闸门检查过的那个 op 的执行（D22）。收敛于 round 0 时，`dest` 里是 `beginning_opr()` 在 `_post_insts = None` 下构造的 op 的结果，而 `assemble` 打包的是 `_post_insts = []` 下的 op；两者相等因为 `_pack_post_insts` 把 `None` 与 `[]` 同样打包成 `[]`（`model.py:1674-1675`），由 §8.4 的测试钉住 | — | the probe 位置 team |
| D3 | 每个 round 的 op 怎么构造 | `_probes_post_insts` 为 True 的四个类各自实现 `_beginning_opr_with_insts(insts)`，以参数接收 instantiation rounds；`beginning_opr()` 在 `Tactic_Like` 与 `CaseSplit_Like` 各定义一次、以 `self._post_insts` 调它；`SubgoalMaker` 的默认实现抛 `InternalError`；删去存—设—恢复（§4.2） | 保留存—设—恢复（临时覆写 `self._post_insts` 再恢复），返回类型收窄并 `assert`，并把"只在收敛处赋值"改为"只在收敛处有持久的赋值" | 评审 C14；op 构造 team 三位裁判两位取采纳项，一位按改动处数取备选；两者行为与 golden 相同 |
| D4 | 退化的 beginning op（`FailureReason`/`None`） | 不可达（§5.4）；`_run_the_probe` 里构造 op 的地方以 `assert` 取代今天的 `isinstance … break` | 保留 `cast`（违例时会在 `execute` 里变成费解的 `NotImplementedError`，`model.py:2061-2062`） | 三位裁判一致 |
| D5 | `dest` 收窄为非 `None` | 是：`Node._execute_opr` 与 `UserNode._execute_opr` 两处（D22 之后 `SubgoalMaker` 不再覆写它）；`UserNode` 的 assert 只去掉 `dest is not None` 那一半 | 不收窄 | 四份设计稿一致 |
| D6 | "`from_state` 不是 `dest`"这条依赖 | 在 `_run_the_probe` 开头 `assert from_state is not dest`，针对节点自己的那一对状态 | 只写进 §5.9 | 第三位裁判指出的遗漏 |
| D7 | 某个 round 失败后 `dest` 留着上一次成功执行的状态，要不要 reset | 不 reset（§5.6）。由 §8.4 的 test 5 钉住（评审 C2 修正后它能分辨两种做法） | 失败时 reset `dest`（会顺手裁定首个子节点状态的归属问题，且 round 0 失败的再刷新必须保持旧状态，无法统一处理） | 四份设计稿一致 |
| D8 | 失败节点的 "derived goal:" 显示 | **批准**：加以 SUCCESS 为条件的辅助函数 `_derived_goal()`（复用 `StdBlock.goal()`），**单独一个 git 提交，排在 C24 之前**，自带 `TACTIC_DESIGN.md` §13 第 17 条。评审 C1、C7 证明"不做"不再是维持现状：C24 会让首次刷新中失败的节点在 "Error:" 下显示一个从来不是它结果的目标（§5.6、§5.7） | 甲：并入 C24 的 git 提交；乙：不做 | 评审 C1（阻塞）；owner 2026-10-11 |
| D9 | 每个 round 都写 `proof_oprs.yaml` | 批准（§6.3） | the probe 的 round 继续 `log=False` | 四份设计稿一致 |
| D10 | 交互建在 `dest` 上 | `Interaction_InstantiatePostSchematics(dest, …)`，不加守卫；但 §5.7 的论证按评审 C1 重写（交互挂起期间 `dest` 是能被渲染出来的，D8 就是对策） | — | 评审 C1 |
| D11 | 新单元测试的位置 | 新文件 `IsaMini/AoA/test_post_inst_probe.py`（§8.4） | 放进 `test_user_operations.py` | — |
| D12 | 模型测试里的执行计数 | `Tactic2`、`Tactic4`、`Tactic5`、`PostInstRuleShared` 各加只断言、不打印的计数，经该用例自己的 session 的 `on_operation_start` 钩子（`_count_operations`，§8.5）；`_count_derived_subgoal_preruns` 原样保留 | 类级别的猴子补丁辅助函数（忘记恢复会污染同进程后续测试） | 评审 C15 |
| D13 | 注入故障的模型测试（真实走 `StdBlock._refresh_the_beginning_opr` 的 round k ≥ 1 失败） | **现在就加**：`PostInstRoundFailure`，用 `Tactic`（没有 autoconvert），夹具抄 `Test_Tactic5.thy`，`isolated_db=True`，只断言，golden 只有一行 `status: FAILURE`（§8.7）。第一稿推迟它的理由（"golden 会冻结 D8 的显示"）是错的：golden 只记测试写进缓冲区的内容，已有只断言的先例 | 暂缓 | 评审 C11；owner 批准夹具与 golden |
| D14 | 两份宿主文档里的术语 | 各用宿主文档自己已有的词（§9 开头的表）：`TACTIC_DESIGN.md` 探测 / 目标状态（`dest`）/ 探测轮次 / 实例化轮次；计划 探针 / 目标状态（`dest`）/ 每轮 / rounds；"节点保留的那次执行"在两份文档里都写成描述句、不用"提交" | 在宿主文档里引入英文词 destination state 等（给同一概念第二个名字；计划 `:38` 明禁同义词） | 评审 C5（放宽 brief 约束 6 的范围：只管本文与代码注释） |
| D15 | `TACTIC_DESIGN.md` 的文案 | §6.1 第 164 行末句与第 168 行加括号、§6.2 第 188 行改写、§13 第 14 条末尾加指引、新增第 17 条（D8）与第 18 条（C24）；逐字文本见 §9.1、§9.2 | 第 14 条原地重写 | 评审 C16：D8 的 git 提交自带记录，C24 的条目号随之为 18 |
| D16 | `AOA_SCHEMATIC_VARIABLE_PLAN.md` 的文案 | `:520-521`、`:522`、`:526-527`、`:606` 按 §9.3 逐字替换；`:526` 的粗体只把"scratch 双执行的"换成"探针的"，括号与 blocker 那句一字不动，其后追加 C24 的事实 | `:606` 不动 | 评审 C4：三位裁判要求的正是"换成探针的"（第一稿误引为"只删 scratch"）；"双执行"两义见 §0.1 R2 |
| D17 | 全量回归里有 golden 翻转时 | 一般规则：任何以 "Timeout" 或 `FACT_IN_TIME_FAIL` 翻转的 golden 先按 §10 第 1 条（失去偶然的第二次运行）排查，再报 owner；`Tactic3`、`InferenceRule_ProveInTime_Backfill`、`RetrieveFact2` 只是例子，不预先列"慢"的名单 | 调整夹具 / 接受为有意的行为变化 | 评审 C3 |
| D18 | 首次刷新中的 `InferenceRule` 在 round k ≥ 1 失败后进入既有的 `_autoconvert_to_rewrite`（`model.py:10906-10915`） | 接受。理由更正：只经墙钟上限可达、且只对 Presented 的规则（prove-in-time 规则不 autoconvert，`:11005-11006`）；它与 round 0 超时是同一事件，单独排除 round k 才是特例；agent 的 k 个答案随被替换的节点一起丢弃 | 显式排除 | 评审 C3 |
| D19 | round k ≥ 1 失败时的报错文字 | 只用该 round 自己的 Isabelle 原话 | 加一句"这次执行带着 agent 给的实例化" | — |
| D20 | 免执行的 M2 变体（R1） | 不做；若将来做，另立计划。R1 不依赖 C24（§0.1） | — | 评审 C4 |
| D21 | 校验答案时发出的 hint 提示会进入 `dest.messages`（评审 C6） | **批准 ML 一行改动**：`proof_opr` 装上 reporter 之后立刻清空消息缓冲（§4.10）；单独一个 git 提交，排在 C24 之前；与 D8 合跑一次全量回归（D24）。改了 `.ML` 之后要起 REPL：Isa-REPL 工具在启动时自己重建 logic heap（`contrib/Isa-REPL/src/scala/repl_tool.scala:103-110`，`Build.build_logic(…, build_heap = true)`），而设了 `RPC_Host` 却没有 host 在听时这次重建失败（2026-10-10 23:48 实测），所以要先 `env -u RPC_Host isabelle build -b Minilang_AoA` 再起 REPL——这与主仓库 `CLAUDE.md:35`（改 `.ML` 只重启、不重建 heap）、`IsaMini/AoA/CLAUDE.md:122`、Isa-Mini `CLAUDE.md:9` 相抵触，§8.8 第 1 步请求授权时必须说明这一点，owner 明确同意后才跑（未试过的替代：先不设 `RPC_Host` 起一次 REPL 让它自己建 heap，再带 `RPC_Host` 重启，同样是重建 heap） | (a) 只在 `validate_inst_var` 里用 `record_reporter` 包住校验；(c) ML 不动，把效应记为 owner 批准的行为变化 | 评审 C6（放宽 brief 约束 5）；owner 2026-10-11 |
| D22 | the probe 挂在哪 | 挂在 `SubgoalMaker._refresh_the_beginning_opr` 里、`super()` 成功返回之后（§4.1）：round 0 就是基类那次执行，之后的 round 由私有方法 `_run_the_probe` 完成；`SubgoalMaker` 不再覆写 `_execute_opr`；不新增任何接口；循环用"先检查、再问、再重跑"的写法 | 评审 C13 的专用入口 `StdBlock._execute_beginning_opr`（三位裁判都排第三：一个现成的覆写点已经有它要划出的范围）；维持 `_execute_opr` 上的覆写并加等式 assert | the probe 位置 team 三位裁判一致；owner 2026-10-11 |
| D23 | 设计文档提不提交、放哪 | git 提交 C24 时把本文搬到 `IsaMini/AoA/docs/archive/C24_PROBE_IN_DEST_DESIGN.md`，加仓库现成的 ARCHIVED 头，§11 写全被驳回的意见与理由，§12 只留一行；绝对路径改相对；交接文件 `ai-artifacts/C24_PROBE_IN_DEST_HANDOFF.md` 不提交，其回归命令已写进 §8.3 | 留在 `ai-artifacts/` 作 git 提交（CLAUDE.md 把它归"临时文件"，`TACTIC_DESIGN.md:48` 告诉读者那里不提交）；不提交（共享工作树里没有 `.gitignore` 规则，可能被别的 agent 的 git 提交扫进去）；放 `docs/` 顶层（那里是现行参考文档、规矩不写行号） | 评审 C17；设计文档 team；owner 2026-10-11 |
| D24 | git 提交顺序与回归次数 | 三个 git 提交（D21 的 ML 一行 → D8 → C24），两次全量回归（D21 与 D8 合跑一次；C24 一次）；C24 的测试先写、先在未改的代码上跑红；细节与前提见 §8.8 | 三次回归；两个 git 提交；一个 git 提交；测试单独一个 git 提交 | 提交流程 team 两位裁判一致；owner 2026-10-11 |
| D25 | 既有缺口：删除前面的兄弟节点不触发后面节点的 `_on_upstream_change` | 记为独立 bug，不在 C24 里修：git 提交 C24 之前在主仓库根目录写 `BUG_DELETE_SKIPS_UPSTREAM_CHANGE.md`（照既有 `BUG_*.md` 的惯例，untracked；内容见 §10 第 8 条，它是冻结的记述并指向这份记录；归档的本文不是这个 bug 的维护记录） | 现在修；只记在本文 | op 构造 team；owner 2026-10-11 |

### 0.1 放宽建议的下落

- **R1（免执行的 M2 变体）**：不做（D20）。第一稿说"当年选双执行是因为既有状态是用完即弃的 scratch state"，这是编出来的历史：计划只记了 M2 为什么必要（`AOA_SCHEMATIC_VARIABLE_PLAN.md:520`、`:838-839`："scratch 终态看不见 `CASE_SPLIT` 未物化的 case"），而今天的 scratch state 在 the convergence check 期间一直活着（`model.py:6893` 执行、`:6897-6898` 读、`:6912-6914` 才 reset），所以免执行的变体在 C24 之前同样可行，R1 不依赖 C24。R1 的内容仍然成立（对 `Tactic_Like` 是精确的：RULE、TACTIC 留在当前 frame 内，`derived_subgoals_of` 走"栈深不变"那一支只读两个状态，`library/proof.ML:836-839`），收益是整体扫描非空的 round 少跑一次 op，代价是一个 ML 回调和 `Tactic2`、`Tactic5` 打印的 `preruns:` 行会变。
- **R2（放宽 owner 那句约束的字面）**：保留。`AOA_SCHEMATIC_VARIABLE_PLAN.md:526` 的粗体"scratch 双执行的循环结构必须保留"改为"探针的循环结构必须保留"，括号与 blocker 那句一字不动（§9.3）。"双执行"在代码库里有两个意思：在作废计划（`AOA_INITIAL_GOAL_SCHEMATIC_PLAN.md:146`）与 `TACTIC_DESIGN.md:164` 里指"scratch 执行 + 循环后的那次执行"，C24 删掉的正是它；在计划 `:520`、`:838` 与 `model.py:10780` 的注释里指"本轮的执行 + M2 预跑"，对 `Tactic_Like` 仍然成立、仍记在 `:520` 与 §4.4 的注释里。`:526` 管四个类的 the probe 循环，而 `CaseSplit_Like` 从不预跑，所以"探针的"是对四个类都成立的唯一写法。

### 0.2 评审意见的落实

- 第一稿的 §5.7 断言"交互挂起期间没有读者会观察到 `dest`"，评审 C1 证明为假（§5.7 重写）；§3.4 第 4 条关于中断的描述为假（评审 C8，§3.4 重写；一位设计裁判要求删掉那句是对的）；"对确定性的 base op，校验过的 round 不会失败"为假（评审 C3，§5.2、§7.5 重写）；D16 误引裁判意见、R1 的前提为假（评审 C4，§0.1）；§4.4 的替换范围差一行（评审 C10）；§8.1(5) 引的残留列表读的是规则之前的状态、`Tactic6` 的"事实找不到"根本不执行（评审 C12，§8.1、§8.2）；§9 的替换文本给宿主文档引入了第二套名字并把"提交"用于两个意思（评审 C5，D14）；本文自己违反术语规则（评审 C18：status 一律写 status，"局部变量/局部残留""探测类/探测分支/探测命令""正式执行""静默回退""refresh seam"全部改为描述句或方法名）。
- 评审 C2（test 5 分不清 D7 的两种做法、变异检查只有一个变体）、C7（round 0 的 the convergence check 失败漏列）、C9（宿主文档文本里"收敛判据读的就是 `dest`"对 `Tactic_Like` 不对）、C15（计数经 session 钩子）、C16（第 17 条的编号与条件句）均已落实，见各节。
- 评审 C13、C14、C17 与提交流程各经一个 agent team 辩论，结论见 D22、D3、D23、D24。op 构造 team 留给 owner 的第 5 个问题（CASE_SPLIT/INDUCT 到达 round 1 的测试）由复审 R10 关闭：§8.4 加纯 Python 的构造方法测试。
- 复审（2026-10-11，18 条 R1–R18，全部采纳或部分采纳，无阻塞）已落实：R1/R8 文本里不再要求写本 git 提交自己的 hash，第 17 条用描述句指前一个 git 提交（§9.2、§9.5、§12）；R2 第 18 条补上"再刷新/首次刷新"的区分与"第 k ≥ 1 轮"的限定；R3/R4 宿主文档的文本只用宿主自己的词（§9 的表加行）；R5/R17 归因与暂存的做法（§8.8）；R6 变异变体的预测；R7 `_probes_post_insts` 注释只留计数器一条前提（§4.7）；R9 构造方法的注释与 §5.9/§10 的措辞（`Tactic.assembled_beginning_opr` 是构造方法之外唯一的构造点）；R10 构造方法测试；R11 §8.7 的 stub 不向 golden 缓冲区写东西；R12 D25 的维护记录；R13 术语（首次填入→首次刷新等）；R14 §8.4 的行号；R15 证据写进 C24 的 git 提交信息、§9.5 补齐；R16 D21 的 heap 重建与 CLAUDE.md 的抵触写明；R18 `EMBEDDING_API_KEY` 的来源。裁判驳回的子意见见 §11。

---

## 1. 本质与目标

**C24 的本质是：把 the probe 每个 round 的执行结果存进节点自己的 destination state，而不是存进一份用完即弃的 scratch state；于是收敛的那个 round 的执行结果本身就是节点保留的结果，不必再执行一遍。** 每个 round 仍然把已累积的全部 instantiation rounds 真正作用到目标上——变的只是执行结果存放的位置，以及（D22）the probe 在代码里挂的位置。

先说 the probe 是做什么的。有四种操作的 beginning op 执行之后，派生出来的子目标里可能留下 schematic 变量（形如 `?x` 的、等待实例化的变量）：`InferenceRule` 与 `Tactic`（共同基类 `Tactic_Like`），`CaseSplit` 与 `Induction`（共同基类 `CaseSplit_Like`）。the probe 在 op 执行之后检查这些变量，向 agent 要取值，把取值作为 instantiation rounds 烘焙进 op（`_post_insts`），再执行一次看还剩什么，直到没有需要实例化的变量为止。这样节点保留并在重放时使用的 op 就不再留下被几个子目标共享的 schematic 变量。

**运行例子**（全文沿用，取自既有夹具 `IsaMini/AoA/Tests/Test_Tactic5.thy`，golden `Tactic5.yml`）：目标 `∃x. PP x ∧ QQ x`，其中 `PP`、`QQ :: nat ⇒ bool` 不透明，另有 sorry 掉的 `p0: PP 0`、`q0: QQ 0`。

- 第 1 步，agent 写 `Tactic rule exI`。目标变成 `PP ?x ∧ QQ ?x`。`?x` 只出现在这一个派生子目标里，`Tactic_Like` 的判据认为它不必现在实例化，于是这一步不发生交互。
- 第 2 步，agent 写 `Tactic rule conjI`，作用在 `PP ?x ∧ QQ ?x` 上，派生出两个子目标 `PP ?x` 与 `QQ ?x`，`?x` 被两者共享。the probe 向 agent 要 `?x` 的取值，agent 答 `?x := 0`；带着这个 round 再执行一次，得到 `PP 0` 与 `QQ 0`，没有剩余的 schematic 变量，收敛。

今天第 2 步共执行 `rule conjI` **三次**：round 0 进一份 scratch state，round 1 进另一份 scratch state，最后再执行一次进节点自己的状态。C24 之后是**两次**：round 0 与 round 1 都直接执行进节点自己的状态，round 1 收敛，它的结果就是节点保留的结果。第 1 步从两次变一次。

**目标**：
1. 常见情形（round 0 就收敛）从两次执行变一次；k 个 instantiation round 从 k+2 次变 k+1 次；失败的 op 从两次变一次。
2. 任何一个 round 失败都是节点如实的失败，消除今天"节点报告成功、但保留的 op 没经过 the convergence check"的三种情形（§3.4）。
3. 每个 round 仍然把已累积的 instantiation rounds 真正作用到目标上（owner 的约束，`AOA_SCHEMATIC_VARIABLE_PLAN.md:526-527`），收敛机制不变（§7）。
4. 既有 golden 全部逐字节不变（§8.1）。
5. the probe 只在 `SubgoalMaker` 自己的方法里，不新增接口（D22）；ML 只改 D21 那一行（单独的 git 提交）；`PlainAgent/`、`_rewrite_trial`、重放不动。

---

## 2. 术语表

| 术语 | 含义 |
|---|---|
| **destination state / `dest`** | 节点自己的、beginning op 执行进去的那个状态，即 after-beginning state。`StdBlock._refresh_the_beginning_opr` 把 beginning op 从 `self.ml_state` 执行进它（`model.py:6040`） |
| **scratch state** | 今天 the probe 每个 round 临时分配、执行完检查完就 `reset` 掉的那个状态（`model.py:6893`、`:6912-6914`）。C24 删除它 |
| **the probe** | 整个事后实例化机制。今天是 `SubgoalMaker._execute_opr` 里 `_probes_post_insts and _post_insts is None` 时进入的那个循环（`model.py:6885-6920`）；C24 后是 `SubgoalMaker._refresh_the_beginning_opr` 在 `super()` 成功返回后调用的 `_run_the_probe` |
| **round** | 一次执行 + 一次 the convergence check，可能再加一次交互。round 0 是不带任何实例化的那一次，C24 后它就是 `StdBlock._refresh_the_beginning_opr` 的那次执行 |
| **instantiation rounds / `_post_insts`** | agent 历次交互答出的取值，按顺序累积成的列表（每项是一组 `(变量名, 值)`），烘焙进 op（`_pack_post_insts`，`model.py:1669-1677`；对 RULE、CASE_SPLIT、INDUCT 是最后一个构造参数，对 TACTIC 是五个参数里的第四个，`:1796-1798`）。`None` 表示"还没探测过" |
| **the convergence check** | `_probe_residual_schematics`：返回仍需实例化的变量，两个映射都空即收敛（`model.py:6856-6868`，`Tactic_Like` 覆写于 `:10766-10791`） |
| **beginning op** | `beginning_opr()` 返回的 op，即节点块开头执行的那个操作 |
| **after-beginning state** | `_state_after_beginning()`（`model.py:5979-5983`）：有子节点时是第一个子节点的 `ml_state`，否则是 `_state_before_ending_` |
| 整体扫描 | `Minilang_State.schematic_variables_of(whole=True)`：只读地列出某个状态里全部子目标的 schematic 变量（`model.py:2743-2758`）。沿用 `TACTIC_DESIGN.md` §6.1 的说法 |
| 服务端预跑 | `Minilang_State.schematic_vars_of_derived_subgoals(opr)`：在 ML 侧从某个状态把 op 再跑一遍、不存结果，按派生子目标分别列出 schematic 变量（`model.py:2760-2776`，ML `Agent/agent_server.ML:1415-1460`）。沿用 `TACTIC_DESIGN.md` §6.1 的说法 |
| 首次刷新 / 再刷新 | 节点第一次被刷新 / 节点此前刷新过、因上游改动等原因再次刷新（代码里叫 re-refresh） |
| status | 节点的评估结果 `self.status.status`（SUCCESS / FAILURE / CANCELLED）。一律写 status，不写"状态"；"状态"只指 `Minilang_State` |

---

## 3. 现状机制

### 3.1 谁会进入 the probe

`SubgoalMaker._probes_post_insts` 默认 `False`（`model.py:6809`）；`CaseSplit_Like` 设为 `True`（`:7341`），`Tactic_Like` 设为 `True`（`:10741`），`UserNode` 钉死为 `False`（`:7812`）。`SubgoalMaker._execute_opr` 在 `self._probes_post_insts and self._post_insts is None` 时进入循环（`:6885`），上限 `_MAX_POST_INST_ROUNDS = 16`（`:6800`）。`_on_upstream_change` 把 `_post_insts` 置回 `None`，下次刷新重新探测（`:6836-6840`）。

`_execute_opr` 的四个调用点都传了非 `None` 的 `dest`：`Leaf`（`:5432`，`self.resulting_state()`）、`StdBlock._refresh_the_beginning_opr`（`:6040`，`self._state_after_beginning()`）、`StdBlock._refresh_footer`（`:6050`，ending op 进 `self.resulting_state()`）、`CaseSplit_Like` 的再执行（`:7656`）。`_probes_post_insts` 为 True 的四个类都没有 ending op：`SubgoalMaker.ending_opr` 返回 `None`（`:7008-7012`），覆写它的只有 `GoalNode`（`:6609`）、`Define`（`:8840`）、`Interpret_Locale`（`:9088`）、`GlobalEnv`/`Root`（`:11751`、`:11923`），所以 `_refresh_footer` 对它们只做 clone（`:6046-6047`）。the probe 与 `_execute_opr` 这个通用入口是同一个 git 提交加进来的（`3ae2246`，2026-06-19）：当时 the probe 要拦住执行以换掉被保留的 op，并按 op 的命令名触发（`_POST_INST_COMMANDS`）；`dd7707d` 把触发改为类属性，C24 则让它不再需要拦住执行。

### 3.2 今天的一个 round（`model.py:6882-6921`）

1. `scratch_op = self._beginning_opr_with_insts(rounds)`（`:6888`）：临时把 `self._post_insts` 设成 `rounds`、调 `self.beginning_opr()`、再恢复（`:6870-6880`）。若结果不是 `Minilang_Operation` 就 `break`，注释说"let the real execute handle it"（`:6889-6890`）。
2. `scratch = await from_state.execute(scratch_op, None, log=False)`（`:6893`）：`assign_to` 为 `None` 时分配一个新名字的状态（`:2006-2007`），`log=False` 不写 `proof_oprs.yaml`。`IsabelleError`/`InternalError` 则 `break`，注释说"the base op itself failed — let the real execute below surface it"（`:6894-6895`）。
3. the convergence check 读 scratch state（`:6897-6898`）；收敛则 `self._post_insts = rounds; break`（`:6899-6901`）；否则先项后型地选出要问的变量（`:6902-6908`），`Interaction_InstantiatePostSchematics(scratch, …)` 问 agent（`:6909-6910`），`rounds = rounds + [rnd]`（`:6911`）。`finally` 里 reset scratch state（`:6912-6914`）。
4. 16 轮用完则 `for … else` 抛 IsabelleError（`:6915-6919`）。
5. 循环结束后 `opr = cast(Minilang_Operation, self.beginning_opr())`（`:6920`，这时带着 `_post_insts`），再 `super()._execute_opr(from_state, opr, dest)` 执行一次进 `dest`（`:6921`）。本文把这一次叫"今天循环后的那次执行"。

相关事实：`Minilang_State.execute`（`:2001-2063`）成功时覆写 `assign_to` 的全部字段（`leading_goal`、`display_goals_count`、`_initialized`、`messages`、`new_subgoals_count`，`:2047-2060`）；`IsabelleError` 时不碰 `assign_to` 的任何字段并把错误抛出（`:2030-2041`）。ML 侧 `proof_opr` 只在成功时 `state := Symtab.update (to, s1) (!state)`（`Agent/agent_server.ML:1106`，在 `Exn.capture` 内，`:1100-1122`），失败时该名字下原有的值保留；`reset_state` 删除该名字（`:1143-1150`）。所以向一个已初始化的状态再执行一次就是覆盖，两次成功执行之间不需要 reset。`log=False` 只关掉 `proof_oprs.yaml` 的两条记录（`model.py:2011-2020`、`:2033-2038`）；计时钩子 `on_operation_start`/`on_operation_end` 无条件调用（`:2021`、`:2031-2032`、`:2042-2043`），后者把耗时加进 `total_isabelle_time`（`:14806-14808`）。

### 3.3 运行例子今天怎么跑

第 2 步（`Tactic rule conjI`）。它的 from_state 记作 S（节点的 `ml_state`）；它的 `dest` 记作 D：节点还没有子节点，所以 D 是 `_state_before_ending_`（`model.py:5979-5983`），一个在 `StdBlock.__init__` 里用新名字分配的状态（`:5923`），从来不是 S 本身。

- round 0：`TACTIC(rule, conjI, rounds=[])` 从 S 执行进 scratch X1，得到 `PP ?x`、`QQ ?x`。整体扫描 X1 发现 `?x`；服务端预跑从 S 再跑一遍，发现 `?x` 出现在两个派生子目标里，是共享的。`Interaction_InstantiatePostSchematics(X1, …)` 问 agent，agent 答 `?x := 0`，答案由 `IsaMini.validate_inst_var` 在 X1 上校验（`Agent/agent_server.ML:1890-1903`）。X1 被 reset。
- round 1：带 `[[?x := 0]]` 的 op 从 S 执行进 scratch X2，得到 `PP 0`、`QQ 0`；整体扫描为空，`_post_insts = [[?x := 0]]`。X2 被 reset。
- 今天循环后的那次执行：同一个 op 第三次从 S 执行进 D。

`rule conjI` 共执行三次，服务端预跑一次。第 1 步（`rule exI`）：scratch 一次（整体扫描见 `?x`，服务端预跑见它只在一个子目标里，收敛），循环后再执行一次，共两次执行、一次预跑。`Tactic5.yml` 记录的是累计预跑数：`interactions: [], preruns: 1`（`:17`）与 `interactions: ['term'], preruns: 2`（`:51`）。

### 3.4 缺陷

1. **成功跑两次，失败也跑两次**。round 0 失败 → `break` → 循环后的那次执行把同一个 op 再跑一遍、再失败一次。任何 op 都有墙钟上限（§5.2），例如一个 15 s 超时（`mini_single_cmd_timeout`，`TACTIC_DESIGN.md:23`）的 tactic 失败一次花 30 s 墙钟；带命题形式事实的 op 会把最多 10 s 的 MePo 搜索（`Agent/agent.ML:1181-1194`）也做两次。
2. **round k ≥ 1 失败时，节点报告成功，但保留的 op 没经过 the convergence check**。同一个 `break` 触发，这时 `_post_insts` 仍是 `None`，于是 `:6920` 的 `beginning_opr()` 是**不带** rounds 的 op；它在 `:6921` 执行成功，节点报告成功，但共享的 schematic 变量仍在，没有任何报告。
3. **同一种情形的另一条路**：round 0 的 scratch 执行失败、而 `:6921` 的那次执行成功——任何接近墙钟上限的 op 在第二次（更热的）运行里都可能成功。节点保留了成功的结果，`_post_insts` 仍是 `None`，the convergence check 从未运行。

   第 2、3 两条之后 `_post_insts` 都仍是 `None`，而 `_execute_opr` 正常返回了。于是 `CaseSplit_Like` 成功之后的再执行（`:7650-7659`）会再次进入 the probe——它默认的前提"`_post_insts` 已设好"不成立（对 CASE_SPLIT/INDUCT 几乎不可达，但形状没有排除它）。
4. **取消传播途中的 `finally` reset**。在一次 `IsaMini.AoA` 运行里，被中断的 Isabelle 回调到达 Python 时已经是 `asyncio.CancelledError`，不是 `IsabelleError`：`interrupts_are_cancellations` 在连接实例上遮蔽了 `callback`（`model.py:80-104`），它装饰 AoA 的入口（`IsaMini/AoA/toplevel.py:192-193`），每个状态都经 Root 的连接回调（`model.py:2028`）。所以 `:6894` 的 `except (IsabelleError, InternalError)` 与 `StdBlock._refresh_the_beginning_opr` 的 `except IsabelleError`（`:6042`）都接不住它，第一稿写的"中断被 `except` 吞掉后又调一次 RPC"是不存在的路径。真实的隐患是 `:6912-6914` 的 `finally`：服务端预跑或答案校验被中断、`CancelledError` 正在向上传播时，它向正在关闭的连接发 `reset_state`；按 `IsabelleInterrupt` 的 docstring（`/contrib/Isabelle_RPC/Isabelle_RPC_Host/rpc.py:49-55`，相对主仓库），这个调用要么以 `ConnectionResetError` 取代原来的取消、要么永不返回。C24 删掉了这个 `finally`。中断处理本身不在 C24 范围内。

---

## 4. 设计

**改了什么**：the probe 从 `SubgoalMaker._execute_opr` 搬进 `SubgoalMaker` 本来就覆写的 `_refresh_the_beginning_opr`，在 `super()` 成功返回之后运行（D22）。C24 之下 round 0 就是"把不带 instantiation round 的 beginning op 从 `ml_state` 执行进 after-beginning state"，而这正是基类 `StdBlock._refresh_the_beginning_opr` 已经在 `:6040` 做的那一次执行——所以 the probe 不必再拦住这次执行，只需跟在它后面：读 `dest` 做 the convergence check；收敛就把 `rounds` 记进 `_post_insts` 并返回；不收敛就在 `dest` 上发起交互，把答案追加进 `rounds`，用 `_beginning_opr_with_insts(rounds)`（D3：显式接收 rounds 的构造方法）造出带全部取值的 op，经普通的 `_execute_opr` 再执行进 `dest`，回到检查。任何异常（某个 round 的执行失败、the convergence check 失败、交互失败、16 轮上限）由 `SubgoalMaker._refresh_the_beginning_opr` 用与基类同一个 `_beginning_opr_err_msgs` 转成节点的 `FailureReason`。`SubgoalMaker` 不再覆写 `_execute_opr`，于是 `_execute_opr` 的每个实现都只执行传给它的那个 op。

**运行例子在 C24 下**：第 2 步，`StdBlock._refresh_the_beginning_opr` 过闸门后把 `TACTIC(rule, conjI, rounds=[])` 从 S 执行进 D（round 0）；回到 `SubgoalMaker` 的覆写，进入 `_run_the_probe`：the convergence check 读 D，整体扫描见 `?x`，服务端预跑从 S 跑同一个 op、见 `?x` 共享；交互建在 D 上，agent 的答案在 D 上校验；round 1 把带 `[[?x := 0]]` 的 op 从 S 再执行进 D，整个覆盖 D（ML 侧 `Symtab.update` 替换条目，`Agent/agent_server.ML:1106`；Python 侧成功的 `execute` 重写状态的全部字段，`model.py:2047-2060`）。the convergence check 读 D，为空，`_post_insts = [[?x := 0]]`，返回。D 已经是节点保留的状态；覆写接着读 D 的 `new_subgoals_count` 决定开子块。共两次执行。agent 看到的东西与今天由同样的数据算出：提示文字只取决于 `schematic_vars` 与 `kind`（`model.py:4135-4158`），校验结果只取决于该状态名字下存的值（`:4160-4170`）。

**为什么每个 round 都重跑整个 op，而不是只把最新的那个 round 作用到 `dest` 上**：`dest` 里存的消息必须是 op 自己的消息，后续好几个读者靠它：`_should_open_proof_block` 读 `new_subgoals_count`（`model.py:7220-7243`），`CaseSplit_Like` 读 `Consider_Case_Msg`（`:7661-7673`），回填读 `FACT_PRF`（`:10899-10900`、`:11147-11148`），`Tactic.assembled_beginning_opr` 读 `TACTIC_TIMES`（`:11159-11163`）。重放的 op 也必须能重现 `dest`。整个 op 重跑，`dest` 就恒等于"`beginning_opr()` 当前返回的那个 op"的执行结果。

### 4.1 the probe 的位置与新代码（D22；取代 `model.py:6882-6921` 的覆写，改写 `:7244-7249`）

`SubgoalMaker._refresh_the_beginning_opr` 的头部（`:7244-7249`）改为：

```python
    async def _refresh_the_beginning_opr(self) -> 'FailureReason | None':
        is_init = self._first_time
        old_n_subnodes = len(self.sub_nodes)
        fail = await super()._refresh_the_beginning_opr()
        if fail is not None:
            return fail
        if self._probes_post_insts and self._post_insts is None:
            try:
                await self._run_the_probe()
            except IsabelleError as err:
                return self._beginning_opr_err_msgs(err)
        s0 = self._state_after_beginning()
        ...   # :7250-7317 不变
```

`:7250-7317` 一字不动：它读 `s0` 并断言已初始化，再按 `new_subgoals_count` 决定要不要开子块——现在读到的就是收敛后的状态。`SubgoalMaker._execute_opr` 的覆写（`:6882-6921`）整个删除，原位放一个私有方法：

```python
    async def _run_the_probe(self) -> None:
        """The post-instantiation probe. `StdBlock._refresh_the_beginning_opr`
        has executed round 0 (the beginning op with no instantiation round)
        from `ml_state` into the after-beginning state, `dest`; each later
        round executes the beginning op, every round so far baked in, into
        `dest` again, and the convergence check reads `dest`. The converged
        round's state is the node's result; any IsabelleError is the node's
        failure."""
        from_state, dest = self.ml_state, self._state_after_beginning()
        assert from_state is not dest, "each round re-executes from an untouched from_state"
        def built(rounds: 'list[list[tuple[str, xterm | xtyp]]]') -> Minilang_Operation:
            opr = self._beginning_opr_with_insts(rounds)
            # What degrades a beginning op never reads the rounds, and
            # StdBlock._refresh_the_beginning_opr has already checked this op.
            assert isinstance(opr, Minilang_Operation), \
                f"a probe round expects a Minilang_Operation, got {type(opr).__name__}"
            return opr
        rounds: 'list[list[tuple[str, xterm | xtyp]]]' = []
        opr = built(rounds)
        while True:
            term_vars, type_vars = await self._probe_residual_schematics(
                from_state, dest, opr)
            if not term_vars and not type_vars:
                self._post_insts = rounds
                return
            # Term-first: a term value pins most type vars via infer_instantiate,
            # so ask for types only once no term vars remain.
            if term_vars:
                offered, kind = term_vars, "term"
            else:
                offered, kind = type_vars, "type"
            schematic_vars = [(name.unicode, ty.unicode) for name, ty in offered.items()]
            rnd = await the_session().launch_interaction(
                Interaction_InstantiatePostSchematics(dest, schematic_vars, kind))
            rounds = rounds + [rnd]
            if len(rounds) == _MAX_POST_INST_ROUNDS:
                raise IsabelleError(
                    [f"Could not eliminate the residual schematic variables of this "
                     f"{opr.command} operation within {_MAX_POST_INST_ROUNDS} rounds of "
                     f"instantiation."], None)
            opr = built(rounds)
            await self._execute_opr(from_state, opr, dest)
```

形状上的几点：

- 不给 `StdBlock`、`Node` 加任何方法；`SubgoalMaker` 用一个私有方法换掉一个覆写，方法数不变。`_execute_opr` 从三个实现减到两个（`Node`、`UserNode`），每个都只执行传给它的 op；它的调用方从四个变成五个（多了 `_run_the_probe`）。
- "只有 beginning op 会进 the probe"由位置保证：footer、`Leaf`、`CaseSplit_Like` 的再执行到得了的只是纯执行的 `_execute_opr`。第一稿把这条列为"留给记忆的"，现在删去。
- `_post_insts` 只有一处赋值，就在唯一的正常 `return` 前面；D3 之后这句话字面成立（全文件对它的赋值只剩 `__init__`、`_on_upstream_change`、这一处，grep 可证）。其余每个出口都是异常，`_post_insts` 留 `None`，下次刷新重新探测。
- 循环先检查再问再重跑：round 0 已由基类执行，所以没有"第 0 轮不执行"的特例；代价是 op 在两处构造（进循环前、每次重跑前），由局部函数 `built` 统一做 D4 的收窄。上限的检查在收下第 16 个答案之后、执行它之前：16 次执行（round 0 加 15 次重跑）、16 次交互、第 16 个答案不执行——与今天相同。
- 没有 `except`，也没有任何一行会在某个 round 之后执行不带已累积 rounds 的 op：§3.4 第 2、3 条写不出来。
- D6 的 `assert`：每个 round 都从 `from_state` 重新执行进 `dest`；若两者是同一个对象，round k 会在 round k−1 的结果上再跑一遍 op。`from_state` 是节点的 `ml_state`，`dest` 要么是 `StdBlock.__init__` 新分配的 `_state_before_ending_`（`:5923`），要么是第一个子节点的 `ml_state`，而 `SubgoalMaker` 的子节点 `GoalNode` 建在 `s0.clone(None)` 新分配的状态上（`:7288`）。
- 新的记忆项（§5.9）：若将来有人在 `SubgoalMaker` 与 `StdBlock` 之间的 MRO 位置插一个 `_refresh_the_beginning_opr` 覆写，它看到的是 round 0 的状态而不是收敛后的。今天那个位置是空的（`GoalContainer`，`:6517-6555`，不定义这个方法），插件类把 `UserNode` 列在最前（`:7810-7812`）。
- 第三份错误转换：`except IsabelleError → self._beginning_opr_err_msgs(err)` 与基类的两处（`:6035-6036` 闸门、`:6041-6043` 执行）并列。接受。

**为什么不用评审 C13 的专用入口**（`StdBlock._execute_beginning_opr`，由 `StdBlock._refresh_the_beginning_opr` 调、`SubgoalMaker` 覆写）：它要划出的范围——"这个块的 beginning op 刚跑完"——已经属于 `SubgoalMaker._refresh_the_beginning_opr`，这个方法在代码库里被覆写十次（`:7244`、`:7644`、`:7854`、`:9945`、`:10109`、`:10188`、`:10294`、`:11318`、`:11414`、`:11478`），一律是"`super()` 之后做事"；专用入口的基类实现会与 `CaseSplit_Like` 再执行那一行（`:7656`）逐字相同，而那一行恰恰不能走它，所以它命名的是一个调用点而不是一个概念；每个普通块的 beginning op 会经过三个可覆写的名字。只在没有现成覆写点时才该加钩子：`dd7707d` 的 `assembled_beginning_opr` 过得了这条规则（没有别的地方产出"`assemble` 打包的 op"这个值），专用入口过不了。

**为什么不维持 `_execute_opr` 上的覆写**：它让一个叫"执行这个 op"的方法在一个覆写里悄悄执行另一个 op（第一稿的循环根本不用 `opr` 参数），基类 docstring 还得描述子类机制；加等式 `assert opr == …` 是按 op 的值识别调用方，违例时 `AssertionError` 不被 `except IsabelleError` 接住、整个刷新崩掉而不是节点失败。它仍是诚实的备选（需要修正 docstring 与 §5.9），owner 未选。

### 4.2 每个 round 的 op 怎么构造（D3；取代 `model.py:6870-6880` 与四个类的 `beginning_opr`）

**(1) `SubgoalMaker`**（取代 `:6870-6880`；`SubgoalMaker.beginning_opr` `:6993-6995` 仍是抽象的）：

```python
    def _beginning_opr_with_insts(
            self, insts: 'list[list[tuple[str, xterm | xtyp]]] | None'
    ) -> 'Minilang_Operation | FailureReason':
        # This node's beginning op with the instantiation rounds `insts` baked
        # in. For a class that sets `_probes_post_insts` the rounds enter the
        # op only through this `insts`: its family's `beginning_opr()` passes
        # `_post_insts`, the probe each round's rounds so far. This default
        # exists only to fail loudly when such a class forgot to implement it.
        raise InternalError(
            f"_beginning_opr_with_insts is not designed for {type(self).__name__}.")
```

同类的大声失败默认实现已有先例：`can_operate_on_schematic_goal`（`:6842-6854`）。

**(2) `Tactic_Like`**（`:10741` 之后）与 **(3) `CaseSplit_Like`**（`:7341` 之后）各加同一个方法，逐字相同：

```python
    def beginning_opr(self) -> 'Minilang_Operation | FailureReason':
        return self._beginning_opr_with_insts(self._post_insts)
```

返回类型必须是宽的那个：静态解析到的是 `SubgoalMaker` 上的声明。`CaseSplit_Like` 这边唯一的读者 `:7653-7654` 已经用 `isinstance` 判类型。

**(4) `InferenceRule`**（取代 `:10960-10968`）：

```python
    def _beginning_opr_with_insts(
            self, insts: 'list[list[tuple[str, xterm | xtyp]]] | None'
    ) -> 'Minilang_Operation | FailureReason':
        if isinstance(self.rule_ref, IsabelleFact_Unfound):
            return FailureReason(f"Inference rule fact \"{self.rule_ref.name().unicode}\" not found")
        if self.rule_ref is not None and _binds_no_theorem([self.rule_ref]):
            # RULE with zero theorems fails hard, with a message that never
            # mentions the empty fact.
            return FailureReason(
                f"Inference rule \"{self.rule_ref.name().unicode}\" binds no theorem here. It's empty.")
        return Minilang_Operation.RULE(self.rule_ref, insts)
```

**(5) `Tactic`**（取代 `:11150-11163`）：

```python
    def _tactic_opr(self, insts: 'list[list[tuple[str, xterm | xtyp]]] | None',
                    recorded_times: 'tuple[int, int] | None') -> 'Minilang_Operation | FailureReason':
        facts = self.fact_refs if self.fact_refs is not None else []
        failure = _unfound_failure(facts)     # a missing fact fails the step (Obvious drops it)
        if failure is not None:
            return failure
        return Minilang_Operation.TACTIC(self.tactic_full, self.arguments, facts,
                                         insts, recorded_times)
    def _beginning_opr_with_insts(
            self, insts: 'list[list[tuple[str, xterm | xtyp]]] | None'
    ) -> 'Minilang_Operation | FailureReason':
        return self._tactic_opr(insts, None)      # a live op never carries the record
    def assembled_beginning_opr(self) -> 'Minilang_Operation | FailureReason':
        # the live run's last TACTIC_TIMES, from the after-beginning state
        times = next((m.times_ms for m in reversed(self._state_after_beginning().messages)
                      if isinstance(m, Tactic_Times_Msg)), None)
        return self._tactic_opr(self._post_insts, times)
```

`assembled_beginning_opr` 走同一个 `_tactic_opr`、传 `self._post_insts`：它是构造方法之外唯一一处构造 op 的地方，只在第五个参数带上记录的时间，其余与 `beginning_opr()` 相同。

**(6) `CaseSplit`**（取代 `:11403-11409`）：

```python
    def _beginning_opr_with_insts(
            self, insts: 'list[list[tuple[str, xterm | xtyp]]] | None') -> Minilang_Operation:
        return Minilang_Operation.CASE_SPLIT(
            self.target_isabelle_term,
            cast(list[varname_spec] | None, self._case_vars_of_child(0)),
            self._resolved_rule_str,
            self.no_simp,
            insts)
```

**(7) `Induction`**（取代 `:11685-11693`）：

```python
    def _beginning_opr_with_insts(
            self, insts: 'list[list[tuple[str, xterm | xtyp]]] | None') -> Minilang_Operation:
        return Minilang_Operation.INDUCT(
            self.target_isabelle_term,
            cast(list[varname_spec] | None, self._case_vars_of_child(0)),
            [var["name"] for var in self.variables if var["status"] == "generalized"],
            [r.full_name for r in self.fact_refs_to_generalize],
            self._resolved_rule_str,
            self.no_simp,
            insts)
```

**`UserNode` 不动**。插件类把 `UserNode` 列在最前（`Tests/sample_plugin/__init__.py:25` 的 `Apply(UserNode, SubgoalMaker)`，`test_user_operations.py:613` 的 `PluginCases(UserNode, _Hooks, CaseSplit_Like)`），`beginning_opr` 解析到 `UserNode` 的（`:7844`），`_probes_post_insts` 解析到 `False`（`:7812`），所以 the probe 从不在插件类上运行，抛错的默认实现也从不被插件类调到。

**不变的**：`beginning_opr()` 的每个调用者（`:5991`、`:6000`、`:6024`、`:6100`、`:7653`；`test.py:18737`、`:18858`、`:18901`；`test_user_operations.py:216`）；每个 op 的值（每个构造方法做的是同一个工厂调用，参数就是原来字段里的值），所以 golden 不变。

**如实定性**：这是结构性收益，但很窄，不修任何 bug。不是改名——存—设—恢复的两次临时写入与恢复（`:6875-6880`）是被删掉而不是挪走，`_post_insts` 从 5 处写、6 处读变成 3 处写、4 处读。也不是安全修复——今天的临时值没有任何别的代码能看到（没有 `await`、`finally` 里恢复）；"`beginning_opr()` 保持同步"本来就被 `StdBlock._refresh_the_beginning_opr` 的断言（`:6024-6026`）保证，不算 D3 的收益。买到的是：§4.1、§4.7、§5.9 里"只在收敛处赋值"字面成立；构造一个 round 的 op 是带显式输入的调用、不写节点；`Tactic` 两个可变部分都走 `_tactic_opr` 的参数；一个设了 `_probes_post_insts` 却没按这个方法构造 op 的类在首次刷新就大声失败，而不是（像今天保留字段读法时那样）烧满 16 轮交互后报上限错误。代码库自己的习惯也支持它：临时覆写属性只用在读者离得远的地方（`_refresh_child_replace_aware` `:5502-5510` 设的标志在 `:10911` 被读，隔着 15 个覆写），这里读者只隔一次调用、`rounds` 又只是 `_run_the_probe` 里的一个 local variable，该走参数，正如 `_tactic_opr(recorded_times)` 已经做的。

**代价**：七个类约 30 行改动；两处逐字相同的一行委托；两处略弱的抽象性检查——忘记实现构造方法的新子类在首次刷新时以 `InternalError` 失败（而不是构造时 `TypeError`），把 `Tactic_Like` 或 `CaseSplit_Like` 排在 `UserNode` 前面的插件类不再在导入时被拒（`helper.py:286`；这种排法本就在文档许可的插件基类之外，`USER_OPERATIONS.md:298-300`）。两种误用今天都不存在（没有类继承这四个类，grep）。新的记忆项见 §5.9。

### 4.3 `SubgoalMaker._probe_residual_schematics`（取代 `model.py:6856-6868`）

```python
    async def _probe_residual_schematics(
            self, from_state: 'Minilang_State', dest: 'Minilang_State',
            opr: 'Minilang_Operation') -> 'tuple[Vars, TVars]':
        """The probe's convergence check: `dest` is the state a round just
        executed `opr` (the beginning op with the rounds so far) into, from
        `from_state`; return the variables that still need instantiating; both
        maps empty = converged.

        Default = the conservative criterion: read `dest` and require it
        schematic-free. Block-opening operations (CaseSplit_Like) MUST keep
        this default — their only all-cases data source, the Goals message, is
        emitted before `apply_post_insts` runs, i.e. a pre-instantiation
        snapshot: a message-based check would never observe the baked rounds
        and the probe would never converge (C1)."""
        return await dest.schematic_variables_of(whole=True)
```

### 4.4 `Tactic_Like._probe_residual_schematics` 的头部与注释（取代 `model.py:10766-10782`；其后的 `shared` 辅助函数与 `return shared(0), shared(1)`，`:10783-10791`，不变）

```python
    async def _probe_residual_schematics(
            self, from_state: 'Minilang_State', dest: 'Minilang_State',
            opr: 'Minilang_Operation') -> 'tuple[Vars, TVars]':
        # The read-only whole scan of `dest` first: a state with no schematic
        # variable is converged, with no server-side prerun.
        term_vars, type_vars = await super()._probe_residual_schematics(
            from_state, dest, opr)
        if not term_vars and not type_vars:
            return term_vars, type_vars
        # S4 relaxation (§5.4): interact only on variables shared by ≥2 derived
        # subgoals — one confined to a single subgoal is that subgoal's own
        # business. Safe here because the op is single-frame: the per-subgoal
        # query reads the prerun's FINAL state, which is post-instantiation, so
        # convergence observes the baked rounds. The query preruns the op again
        # server-side; the double execution (the round's own + the prerun) is
        # deliberate — see the batch-6 record.
        derived = await from_state.schematic_vars_of_derived_subgoals(opr)
```

`Tactic_Like` 的类 docstring（`:10734-10740`）**不改**：它说的 "the prerun's final state" 指服务端预跑，不是 scratch state；C24 不碰服务端预跑，它陈述的性质仍然成立。这段 docstring 正是 `TACTIC_DESIGN.md:166` 规定的那句。`Tactic_Like` 闸门里的注释（`:10759`）"the post-rule probe in SubgoalMaker._execute_opr" 改为 "SubgoalMaker._run_the_probe"。

### 4.5 `Node._execute_opr`（取代 `model.py:4430-4439`）

```python
    async def _execute_opr(self, from_state: 'Minilang_State',
                           opr: 'Minilang_Operation',
                           dest: 'Minilang_State') -> None:
        """Chokepoint for executing this node's own operation from an explicit
        `from_state` (the call sites execute from two different receivers)
        into `dest`."""
        await from_state.execute(opr, dest)
```

旧 docstring 描述的子类机制（the probe）不再挂在这里；D5 把 `dest` 收窄为非 `None`。`Interaction_InstantiatePostSchematics` 的 docstring（`:4108`）"Fired by the probe loop in `SubgoalMaker._execute_opr`" 改为 "`SubgoalMaker._run_the_probe`"。

### 4.6 `UserNode._execute_opr`（`model.py:7863-7865` 与 `:7872`）

签名第三行 `dest: 'Minilang_State | None') -> None:` 改为 `dest: 'Minilang_State') -> None:`；`:7872` 的

```python
        assert dest is not None and dest.new_subgoals_count is not None
```

改为

```python
        assert dest.new_subgoals_count is not None
```

剩下那一半是另一条不变式（`interpret_i` 对每个 USER 步都报一个 Goals），保留。它成为 `_execute_opr` 唯一的覆写。`test_user_operations.py:242-245` 传的是 `SimpleNamespace` 假 `dest`，运行时不受影响。`Minilang_State.execute` 自己的 `assign_to: 'Minilang_State | None'` 保持不变，它还有别的调用者。

### 4.7 `_post_insts` 与 `_probes_post_insts` 的注释（取代 `model.py:6804-6808` 与 `:6827-6833`；`:6834` 的赋值不变）

```python
    # Whether this node's beginning op may leave residual schematic variables
    # that the post-rule instantiation probe (`_run_the_probe`, run by
    # `_refresh_the_beginning_opr` after the beginning op) must eliminate:
    # True on Tactic_Like and CaseSplit_Like; False on UserNode, which a plugin
    # class lists first, so a USER command (it carries no instantiation
    # rounds) never probes, whichever base the class picks. The probe relies on
    # one fact about these classes: none of RULE, TACTIC, CASE_SPLIT, INDUCT
    # advances a session-shared counter (a probe round, the server-side prerun
    # and the CaseSplit_Like re-execution all run the op again).
```

```python
        # Post-rule schematic instantiation, used when `_probes_post_insts` is
        # True.  `None` = not yet probed; otherwise the ordered list of
        # instantiation rounds (each a list of (var-name, value) pairs) baked
        # into the op so that no schematic variable is shared by ≥2 derived
        # subgoals (a variable confined to one subgoal may remain), and the op
        # replays from cache. Assigned only where the probe converges, so a
        # failing round leaves it None and the next refresh probes again.
        # Reset on upstream change (see _on_upstream_change).
        # When `_probes_post_insts` is False it stays None and is never read.
```

### 4.8 刻意不改的东西

- `StdBlock._refresh_the_beginning_opr` 本身（`model.py:6016-6043`）；`_refresh_footer`（`:6044-6052`）、`Leaf` 的调用点（`:5432`）、`CaseSplit_Like` 的再执行（`:7644-7660`）。
- `Interaction_InstantiatePostSchematics` 及其 docstring 的其余部分（`:4101-4170`；"once per round" 仍然准确）。
- `Minilang_State.execute` 及其 `log=False` 注释（`:2002-2005`；它举的例子 `_rewrite_trial` 在 C24 之后就是唯一的 `log=False` 调用者）。
- `InferenceRule._rewrite_trial`（`:10969-10993`）。它与 scratch state 是两回事：它执行的是**另一个** op（SIMPLIFY），目的是判断要不要把节点**换成** Rewrite；它的结果永远不能成为任何节点的状态，被拒绝时节点的 RULE 失败必须原样保留。the probe 的每个 round 执行的是节点自己的 beginning op，收敛那个 round 的结果正是要保留的结果——scratch state 只是它的一份暂存副本。
- 四个调用点、`_on_upstream_change`、重放（`toplevel._replay_assembled_proof`，`IsaMini/AoA/toplevel.py:87-125`：它把打包好的 op 直接交 `IsaMini.proof_opr`，从不经过 `_execute_opr`）、`PlainAgent/`、ML 侧除 D21 那一行之外的全部（`proof_opr` 成功覆盖、失败不动的语义正是 C24 需要的；`reset_state` 不再被 the probe 调用）。
- `USER_OPERATIONS.md:432` 与 `AOA_SCHEMATIC_VARIABLE_PLAN.md:584`、`:758`、`:834`、`:1038` 把闸门说成"在 `_execute_opr` 之前"，在 `:6040` 仍然字面成立，不改。

### 4.9 失败节点不显示 derived goal（D8；单独一个 git 提交，排在 C24 之前；取代 `model.py:10813-10836`）

```python
    def _derived_goal(self) -> 'Goal | None':
        """The goal the op left when it left one subgoal; None unless the node
        succeeded — a failed node's after-beginning state is not its result."""
        if len(self.sub_nodes) > 1 or not _status_can_continue(self.status.status):
            return None
        return self.goal()
    def _quickview_derived_goal(self, indent: int, file: MyIO) -> None:
        """The quickview's `derived goal:` line when the op left one subgoal,
        printed again only when that goal changed."""
        goal = self._derived_goal()
        if goal is not None:
            conclusion = goal.conclusion
            if conclusion != self._prev_quickview_derived_goal:
                conclusion_str = conclusion.unicode
                if len(conclusion_str) > AGENT_GOAL_CHAR_LIMIT:
                    conclusion_str = _trunc_expr_base(conclusion_str, AGENT_GOAL_CHAR_LIMIT)
                print_indent(indent, file)
                file.write(f"derived goal: {conclusion_str}\n")
                self._prev_quickview_derived_goal = conclusion
    def _print_derived_goal(self, indent: int, file: MyIO) -> None:
        """The full print's `derived goal:` block when the op left one subgoal."""
        goal = self._derived_goal()
        if goal is not None:
            print_indent(indent, file)
            file.write("derived goal:\n")
            print_goal(goal, indent+1, False, file, self._ctxt_before_me())
```

理由：这两个打印辅助函数是打印路径上**仅有的**不看 status 就读 after-beginning state 的读者（调用点 `:10941`、`:10959`、`:11169`、`:11183`）。代码库自己的规则是"判断一个节点的状态能不能用，看 status，不看 `.initialized()`"（`model.py:14320-14331`），`_retrieval_fallback_state`（`:5973-5978`）、`_hint_notice_state`（`:5984-5993`）与两处回填（`:10899`、`:11147`）都按 SUCCESS 门控；`_status_can_continue` 就是那个判据（`:1237-1238`）；`StdBlock.goal()`（`:5994-5995`）就是读 after-beginning state 首个目标的现成函数，不重抄。头部成功、子节点失败的节点 status 仍是 SUCCESS（`EvaluationStatus.Success(t, reason)`，`:1228-1230`；`StdBlock._refresh_me_alone` 在 `:6138-6143` 这样设），照常打印。它修掉今天"再刷新失败后显示旧 derived goal"的既有问题，也挡住 C24 会让首次刷新也出现的同一问题（§5.6、§5.7）。预计 golden 不变：397 个被跟踪的 golden 里含 "derived goal" 的 13 个，其前 12 行内都没有 Error/fail/cancel（grep）；只有回归能确认。

它**不**覆盖：(1) 再刷新期间——status 只在 `Node.__init__`（`:4407`）与 `_refresh_me_alone` 结尾赋值，再刷新途中节点仍带着上一次的 SUCCESS，所以再刷新的交互挂起窗口、或深度重启打断再刷新之后，节点没有子节点时会在旧的 SUCCESS 下显示 round k 的目标，子节点被复用时经第一个 `GoalNode` 的目标头部显示——与今天"再刷新失败后显示旧状态"同类，列出、不加机制；(2) 另外两个不看 status 的读者：`GoalNode` 的目标头部（`goal()` = `self.ml_state.leading_goal`，`:6595-6596`，打印于 `:6630-6644`）与删除节点时的存档行（`StdBlock.goal()`，经 `IsaMini/AoA/mcp_http_server.py:487-495`）。

### 4.10 `proof_opr` 开头清空消息缓冲（D21；单独一个 git 提交，排在 C24 之前；`Agent/agent_server.ML:1098` 之后加一行）

```sml
        function = (fn (from, to, opr) =>
          let val _ = Minilang.set_reporter listen_report
              (* this op's report starts empty: a message another callback left
                 since the last drain (e.g. a hint notice fired while validating
                 an instantiation answer) is not this op's (A3) *)
              val _ = messages := []
              val s0 = get_state from
```

机制（评审 C6 查实）：`proof_opr` 装上 reporter（`:1098`，`Thread_Data.put`，从不恢复，`library/proof.ML:792`），回调在派发线程上就地运行（`Isabelle_RPC/Tools/RPC.ML:554-566`）；`validate_inst_var` 对 agent 的答案跑 `apply_post_insts [round]` 而不捕获 reporter（`Agent/agent_server.ML:1896-1899`），其中 `check_authored_terms`（`Agent/agent.ML:1437`、`:525-536`）会经 `get_reporter ()` 发出 hint NOTICE，发生在答案可能被拒绝之前；`proof_opr` 只在每条路径的**结尾**清空缓冲（`:1117-1121`，注释 A3），不在开头，所以下一次 `clean_report`（`:1105`）把残留当作自己的消息返回。今天下一次 `proof_opr` 是被丢弃的 scratch 执行；C24 之后是执行进 `dest` 的那个 round，于是一条来自被拒绝答案里的常量的 NOTICE、以及可能被重排的 NOTICE 块会进入 `dest.messages`、被 agent 看到。这一行把 A3 那条规则补完到源头，对整类情形成立；它同时关掉今天就有的泄漏（第 16 个答案、被中止的交互的答案漏进下一个不相干的操作）。做法 (a)（只在 `validate_inst_var` 里 `record_reporter`）只守一个生产者，未选。预计 golden 不变（唯一的 notice 常量夹具 `Tests/Test_HintNoticeConst.thy` 不进 the probe），但它也会丢掉其它回调留下的残留——若某个 golden 今天恰好显示这种残留，回归会翻转，按 §8.8 归因后报 owner。

### 4.11 改动文件清单

| git 提交 | 文件 | 改动 |
|---|---|---|
| D21（先） | `Agent/agent_server.ML` | §4.10 一行；需重建 heap、重启 REPL |
| D8 | `IsaMini/AoA/model.py` | §4.9 |
| D8 | `IsaMini/AoA/docs/TACTIC_DESIGN.md` | §13 第 17 条（§9.2） |
| C24 | `IsaMini/AoA/model.py` | §4.1–§4.7 |
| C24 | `IsaMini/AoA/test.py` | `_count_operations`；`Tactic2`、`Tactic4`、`Tactic5`、`PostInstRuleShared` 的计数断言；`PostInstRoundFailure`（§8.5、§8.7） |
| C24 | `IsaMini/AoA/test_post_inst_probe.py` | 新文件（§8.4） |
| C24 | `IsaMini/AoA/Tests/Test_PostInstRoundFailure.thy`、`Tests/PostInstRoundFailure.yml` | 新夹具与手写的 golden（§8.7） |
| C24 | `IsaMini/AoA/docs/TACTIC_DESIGN.md` | §6.1、§6.2、§13 第 14 条与第 18 条（§9.1、§9.2） |
| C24 | `IsaMini/AoA/docs/archive/C24_PROBE_IN_DEST_DESIGN.md` | 本文归档（D23） |
| （主仓库，不进 git） | `AOA_SCHEMATIC_VARIABLE_PLAN.md` | §9.3，手改 |
| 不动 | `Agent/*.ML` 其余、`library/proof.ML`、`toplevel.py`、`mcp_http_server.py`、`PlainAgent/`、全部既有 golden | — |

---

## 5. 失败语义与状态生命周期

### 5.1 round 0 的执行失败

`StdBlock._refresh_the_beginning_opr` 里的执行抛 `IsabelleError`，被它自己的 `except` 转成 `FailureReason`（`model.py:6041-6043`），`SubgoalMaker` 的覆写在 `fail is not None` 处返回（§4.1），the probe 根本不开始。只执行一次（今天两次）。`dest` 不变，两个原因：ML 侧只在成功时写进状态表（`Agent/agent_server.ML:1100-1106`），Python 侧在 `IsabelleError` 时不碰 `assign_to` 的任何字段（`model.py:2030-2041`）。于是 `dest` 在首次刷新时仍未初始化，再刷新时仍是上一次刷新留下的状态——与今天完全相同。错误文字现在来自 round 0 的那次执行而不是今天循环后的那次执行；两者是同一个 op 从同一个 from_state 执行，文字相同。

### 5.2 round 0 的 the convergence check 失败、round k ≥ 1 的执行失败、交互失败

这些都发生在 `_run_the_probe` 里，由 `SubgoalMaker._refresh_the_beginning_opr` 的 `except IsabelleError` 转成同一个 `_beginning_opr_err_msgs`（§4.1）。节点失败，`_post_insts` 留 `None`。

- **某个 round（含 round 0）的 the convergence check 失败**：例如 `Tactic_Like` 的服务端预跑超时。它不需要任何交互就能发生：整体扫描非空就会预跑（`model.py:10771-10782`），"只出现在一个派生子目标里的 schematic 变量"这种常见情形正是如此；预跑在 method 自己的时限下重跑 op，带 prove-in-time 事实的 op 还会重做搜索（`recorded` 在 SUCCESS 回填之前是 `None`）。执行次数：1（今天 scratch 1 次，然后抛错）。`dest`：今天不变（异常越过只有 `finally` 的 `try`，`:6896-6914`，到不了 `:6921`）；C24 下留着该 round 的执行结果——round 0 时就是首次刷新中失败的节点带着一个已初始化的 `dest`，连交互都没有发生过。这是 §5.6/§5.7 里首次刷新情形最容易到达的一条路。
- **round k ≥ 1 的执行失败**：共 k+1 次执行。`dest` 留着 round k−1 的状态。今天：节点报告成功、保留的 op 没经过 the convergence check（§3.4 第 2 条）。
- **交互失败**（`Interaction_BadAnswer` 之外的异常）：异常的传播与今天相同（今天 `launch_interaction` 也在没有 `except` 的 `try/finally` 里）；区别只在 `dest`——今天不动（当前 round 在 scratch state 里），C24 下留着当前 round 的状态。

**可达性**：一个校验过的 round 本身不会让下一次执行失败——校验 `IsaMini.validate_inst_var` 在 round k−1 的状态上做 `apply_post_insts [round]`（`Agent/agent_server.ML:1896-1899`），下一次执行在同一个 base 结果上做同一个左折叠（`Agent/agent.ML:1424-1442`）。一个 round 失败只能来自墙钟上限，而**每个** base op 与每轮的实例化都有墙钟上限：`timed_OPR` 用 `Timeout.apply` 把超时变成 `OPR_FAIL "Timeout"`（`library/proof.ML:1798-1800`），INDUCT、CASE_SPLIT 各 10 s（`:3279`、`:3297`），RULE 8 s（`:3390`），每轮的 `INST_GOAL_VARS` 8 s（`:3827`），TACTIC 受 `mini_single_cmd_timeout`，prove-in-time 事实的搜索 10 s（`Agent/agent.ML:1181-1194`、`:1206-1212`，每次执行重新搜），服务端预跑内部同样受这些时限。`Timeout.apply` 是墙钟，所以这些失败取决于机器负载。第一稿说"对确定性的 base op 不会失败、只有 Tactic 与 prove-in-time 能失败"是错的（评审 C3）。

### 5.3 16 轮上限

16 次执行（round 0 加 15 次重跑）、16 次交互；第 16 个答案收下但不执行，与今天相同。然后抛出同样文字的 IsabelleError，节点失败。`dest` 留着第 16 次执行的状态（烘焙了 15 个 round）。今天这种情形 `dest` 不变。

### 5.4 退化的 beginning op：不可达（D4）

`StdBlock._refresh_the_beginning_opr` 已经断言 `opr` 是 `Minilang_Operation`（`model.py:6022-6026`），而让 `beginning_opr()` 退化的条件都不读 instantiation rounds：`InferenceRule` 只看 `rule_ref`（Unfound，或绑定零个定理，`:10961-10967`）；`Tactic` 只看 `fact_refs`（`_unfound_failure`，`:11150-11153`）；`CaseSplit` 与 `Induction` 永远返回 op（`:11403-11409`、`:11685-11693`）。D3 之后这一点在形状上更明显：`insts` 只进入最后那个工厂调用。这些字段只由节点自己的 `_refresh_me_alone` 在执行之前写（`:10870-10884`、`:11137-11143`），而 inline 交互挂起期间树不能被改动（改动类工具一律拒绝，`IsaMini/AoA/mcp_http_server.py:266-274`、`:306-310`）。所以今天的 `break` 与"real execute will handle it"是死代码——而且万一触发，`:6920` 的 `cast` 会把 `FailureReason` 交给 `execute`，在 `:2061-2062` 抛 `NotImplementedError`，它从来没有"处理"过什么。C24 以 §4.1 里 `built` 的 `assert` 取代它。

### 5.5 中止

forked 交互抛出的 `SessionQuit`、深度重启丢弃挂起交互时的 `CancelledError`（`model.py:13396-13402`、`:13404-13432`；`mcp_http_server.py:2477` 起）、被中断的 Isabelle 回调（到达时已是 `CancelledError`，§3.4 第 4 条）、或 `InternalError`（如 `beginning_state_not_found`，`model.py:2039-2040`）都不是 `IsabelleError`，照今天的方式穿过 `_run_the_probe`、`SubgoalMaker._refresh_the_beginning_opr` 与 `StdBlock._refresh_me_alone` 向上传播；`dest` 留着当前 round 的状态，节点的 status 根本没被赋值。C24 删掉的只是 scratch state 在 `finally` 里的 reset（§3.4 第 4 条）。中断处理本身不在 C24 范围内。

### 5.6 节点失败且 `dest` 已初始化时，逐个读者走一遍

- `StdBlock.has_pending_goal`（`model.py:6166-6173`）：调用者 `_print_footer`（`:6188-6204`）、`unfinished_nodes`（`:6215-6219`）、`does_quickview_need_detail`（`:6283-6289`）、`_quickview_pending_footer`（`:6290-6296`）都以 `self.opening()` 为前提，而 `SubgoalMaker.opening()` 恒为 `False`（`:7320-7325`）；`should_I_show_pending_goal` 还要求 `_id_of_openning_prf_to_fill()` 非 `None`，对 `SubgoalMaker` 恒为 `None`（`:6175-6185`、`:7318-7319`）。输出不变。失败节点在两种设计下都由 `Node.unfinished_nodes` 按 status 计入（`:4906-4908`）。goal hints 那条线新加的两个读者也在这些 `opening()` 守卫之内，同样不生效。
- `SubgoalMaker._refresh_the_beginning_opr`（`:7244-7317`）：失败时在 `fail is not None`（C24 后也包括 the probe 的失败）就返回，在初始化断言（`:7251-7252`）与 `_opened_closing_block`/`_opened_count` 的锁存之前。不变。
- `Session.resolve_context_at`（`:13534-13590`）：失败节点解析到它的 `ml_state`，从不到 `dest`（`:13578-13586`）。再刷新时被取消的第一个子节点 `GoalNode` 解析到它的 `ml_state`，而那正是 `dest`；它在两种设计下都已初始化（今天是旧状态，C24 下是 round k−1 的状态），所以两者都不走"dead region"的 `ValueError`，只是检索上下文的内容不同。`_retrieval_fallback_state`（`:5973-5978`）只对 SUCCESS 节点返回 `dest`。
- SUCCESS 门控的读者：`_hint_notice_state`（`:5984-5993`）、两处回填（`:10899-10900`、`:11147-11148`）、`Induction` 读消息（只在 `super()._refresh_the_beginning_opr()` 成功后，`:11503` 起）。不变。
- `Tactic.assembled_beginning_opr`（`:11159-11163`）只在 `assemble()` 里读失败节点的 `dest`，而装配结果只在证明完成时重放（`toplevel.py:394-422`），未完成时直接返回（`:423-428`）。
- `InferenceRule` 的 `_autoconvert_to_rewrite`（`:10906-10915`）：把首次刷新中在 round k ≥ 1 失败的节点当作任何失败的 RULE（D18，§10 第 4 条）。
- `StdBlock._cancel`（`:5948-5954`）reset `_state_before_ending_`，所以之后的取消清掉 round k−1 的状态，正如它清掉旧状态。
- **不看 status 的读者**：`Tactic_Like._print_derived_goal`/`_quickview_derived_goal`（`:10813-10836`）在 `len(sub_nodes) <= 1` 时打印 `dest` 的首个目标——这就是 D8 要改的（§4.9）。`GoalNode.goal()`（`:6595-6596`）与删除时的存档行（`mcp_http_server.py:487-495`）同理，D8 不覆盖。没有任何既有 golden 在错误、失败或取消附近打印 derived goal（grep）。

**结论分两半**。**再刷新**：这与"再刷新失败后留着已初始化的旧状态"是同一种情形（`StdBlock._refresh_me_alone` 取消子节点，但不 reset 自己的 `_state_before_ending_`，`:6099-6147`）：一个失败的 `SubgoalMaker`，其 after-beginning state 已初始化，内容却不是它当前 op 的结果。每个读者只区分 `initialized()` 与 status，从不区分内容从哪来。**首次刷新**：今天 `dest` 是空的、什么都不显示，C24 下它带着从来不是节点结果的内容，这是 C24 引入的新情形（评审 C1、C7），对策是 D8——由 D8 之后，唯一能把它显示出来的读者按 status 门控。两种情形都不加 reset（D7）。reset 在这里还是错的，不只是多余：(1) 节点有子节点时，`dest` 就是 `sub_nodes[0].ml_state`，而取消级联从不 reset 一个块的第一个子节点的 `ml_state`（`IsaMini/AoA/docs/D1_CANCEL_STATE_OWNERSHIP.md:172-177`；该文档已被取代，但其文件头说明它对机制的分析仍然正确），在这里 reset 等于顺手裁定那个归属问题；(2) round 0 失败的再刷新必须让 `dest` 保持旧状态（今天 golden 可见的行为），要恢复更早的内容就得做快照——那又是换了个形式的 scratch state。

### 5.7 inline 交互挂起期间，`dest` 已初始化但节点的 status 尚未赋值

交互挂起期间 `dest` 是一个已初始化、树还没当作节点结果的状态。第一稿说没有读者能观察到它，评审 C1 证明这是错的：有三条路会在这个窗口里把整棵证明树重新渲染成 proof.yaml。

- `refresh` 工具不在 `_MUTATION_TOOLS` 里（`mcp_http_server.py:268-276`）；交互挂起时 `_check_tool_permission` 只拦改动类工具（`:306-310`）；`refresh` 直接派发（`:2806-2807`），`_refresh_tool_logic` 只在 fork 挂起、已有 `quit_info` 或冷却期内拒绝（`:2036-2063`）。随后 driver 开新对话并无条件 `refresh_YAML()`：`driver_claude_code.py:763-771` 之后的 `:689`，`driver_codex.py:351-356`，`driver_api.py:560-569` 经 `_compact` 到 `:695`。
- API driver 仅按 token 用量就会自动 compaction（`driver_api.py:548-555` → `_compact` → `:695`），不需要 agent 的任何动作。
- 深度重启丢弃挂起的交互但保留树（`discard_parked_interaction`，`mcp_http_server.py:2477-2495`，由 `model.py:13404-13432` 调用），新对话在 `driver_claude_code.py:689` 渲染它。

渲染走 `print_proof_scope` → `root.print`（`model.py:14558-14559`）。首次刷新时节点已经在树上（`fill` 先挂节点再刷新，`:6504-6511`），status 是 `EVALUATION_NOT_YET`——一种 FAILURE（`:1235`、`:4407`），打印成 "Error: Not yet evaluated"（`:4581-4586`）。此时 `Tactic_Like` 的两个 derived goal 打印辅助函数在 `len(sub_nodes) <= 1`（还没有子节点）时读 `dest` 的首个目标、不看 status（`:10813-10836`）：今天 `dest` 是空的、不打印；C24 下会在 "Error: Not yet evaluated" 下打出 `derived goal: PP ?x`——这个 op 派生的是两个子目标而不是一个，`PP ?x` 又是中间 round 的结果。这就是 D8 从可选变成必须的原因（§4.9）。其余读者按 status 或 `opening()` 门控（§5.6），不变。

其它方面：改动类工具一律被拒（`:266-274`、`:306-310`），树与 `sub_nodes` 不会变、不会开始新的刷新；worker 只在调度者 `await` 它时推进（`_run_worker_on`，`:1707-1729`），而启动/恢复 worker 的 `subagent` 正是被拒的改动类工具。`query` 的 `context_at`：首次刷新时 status 是 NOT_YET，`resolve_context_at` 返回它的 `ml_state`，不碰 `dest`；再刷新时节点仍带着上次的 SUCCESS，返回 `_state_after_beginning()`（`:13587-13588`）也就是 `dest`——今天是上一次上游留下的旧状态，C24 下是当前上游的 round k 状态，两者都已初始化，golden 看不到，后者内容更相关。forking 模式下交互 fork 的工具限于答题与 `query`（`fork_allowed_tools`，`model.py:4125`；`mcp_http_server.py:294-304`），分析同上。先例："节点 status 还没赋值、after-beginning state 已初始化、同时有 inline 交互挂起"今天就存在：`_orchestrate_proofs`（`model.py:7123` 起，调用于 `:7316`）里子节点的交互（如 `Interaction_MapCase`）发生在父节点的 beginning op 已执行进 `dest` 之后、`StdBlock._refresh_me_alone` 赋 status（`:6135-6147`）之前。交互本身不加守卫（D10）。

### 5.8 `CaseSplit_Like` 的再执行（`model.py:7650-7659`）

它只在 `super()._refresh_the_beginning_opr()` 返回 `None` 时运行，而 D22 之后 `super()` 就是 `SubgoalMaker._refresh_the_beginning_opr`，它返回 `None` 意味着 the probe 已收敛（或本类不探测）。再执行调的是纯执行的 `_execute_opr`，没有任何覆写会探测——由形状保证，不必像第一稿那样从"唯一的正常返回"推导。向已初始化的状态执行是覆盖（`Agent/agent_server.ML:1106`；`model.py:2047-2060`）；失败时 `except IsabelleError: pass` 留下第一次执行的结果，与今天相同。今天在 §3.4 第 3 条的情形下这个"永不探测"不成立。

`_on_upstream_change`（`:6836-6840`）不变：下次刷新从 round 0 重新探测进 `dest`，覆盖其中的任何东西，不需要 reset。

### 5.9 不变式

由形状保证的：

1. `_post_insts` 非 `None` 当且仅当 the probe 收敛过（自上次 `_on_upstream_change` 起）；全文件对它的赋值只有 `__init__`、`_on_upstream_change`、收敛处三处（grep 可证）。
2. `_run_the_probe` 正常返回 ⟹ `_post_insts` 已设，且 `dest` 里是"`beginning_opr()` 当前返回的那个 op"的执行结果（`assemble` 打包、重放执行的就是它，`Tactic` 的 `assembled_beginning_opr` 另在第五个参数带上记录的时间；round 0 收敛时两者相等依赖 `_pack_post_insts(None) == _pack_post_insts([])`，`model.py:1674-1675`，由 §8.4 钉住）。收敛之后不再有任何执行。
3. 没有"节点报告成功但保留的 op 没经过 the convergence check"的情形：`_run_the_probe` 里没有 `except`，也没有任何一行在某个 round 之后执行不带已累积 rounds 的 op。
4. the convergence check 收到的 `dest` 与 `opr` 都带着全部已累积 rounds，且紧跟在"把这个 op 执行进 `dest`"之后（round 0 时，`StdBlock._refresh_the_beginning_opr` 的执行（`:6040`）与检查之间只有 `return None`、`fail` 的判断与 `self._probes_post_insts and self._post_insts is None` 这个判断）。作废计划的 blocker 缺的正是这一条（§7）。
5. 只有 beginning op 会进 the probe：`_run_the_probe` 只由 `SubgoalMaker._refresh_the_beginning_opr` 调用；footer、`Leaf`、`CaseSplit_Like` 的再执行调的是纯执行的 `_execute_opr`。
6. `dest` 的 ML 条目与 Python 字段始终一致：成功时一起覆盖（`Agent/agent_server.ML:1106`、`model.py:2047-2060`），失败时都不变（`Agent/agent_server.ML:1100-1122`、`model.py:2030-2041`）。
7. 每次执行进树所拥有的状态都写 `proof_oprs.yaml`；C24 之后 `log=False` 只剩 `_rewrite_trial`。
8. D21 之后：一次 `proof_opr` 的结果只含本 op 自己的消息，所以 `dest.messages` 恰是收敛那个 op 的消息。
9. `dest` 在类型上非 `None`（D5）。

靠 assert 检查、而非由形状排除的：

1. `beginning_opr()` 的退化与 instantiation rounds 无关（§4.1 `built` 的 assert；§5.4）。
2. `from_state is not dest`（§4.1，D6）。
3. 设了 `_probes_post_insts` 却没实现 `_beginning_opr_with_insts` 的类，在首次刷新时经 `SubgoalMaker` 的默认实现抛 `InternalError`（§4.2）。

留给记忆的：

1. 四个命令（RULE、TACTIC、CASE_SPLIT、INDUCT）不推进任何会话共享的计数器，否则少执行一次会让 agent 可见的名字移位。证据：它们的分派（`Agent/agent.ML:1591-1653`）从不碰 `counters`；`prem_counter` 只由 AUTO_INTRO、SIMPLIFY、HAVE、SUFFICES、SETUP_REWRITING 推进（`:703`、`:943`、`:1679`、`:1702`、`:2005`）；Minilang 的计数模式是 `"none"`（`Agent/agent_server.ML:622`）；计划记录了实测（`AOA_SCHEMATIC_VARIABLE_PLAN.md:868`、`:875-876`）。服务端预跑本来也要求它（`model.py:2761-2769`）。写在 `_probes_post_insts` 的注释里（§4.7）。
2. 设了 `_probes_post_insts` 的类，其 instantiation rounds 只经 `_beginning_opr_with_insts` 的参数 `insts` 进入 op；`Tactic.assembled_beginning_opr` 是构造方法之外唯一的构造点，它必须继续经 `_tactic_opr`。在构造方法里读 `self._post_insts`、让 `assembled_beginning_opr` 绕过 `_tactic_opr`、或在子类里覆写 `beginning_opr`，会让 the probe 执行的 op 与 `StdBlock._refresh_the_beginning_opr` 检查、`assemble` 打包的 op 不一致。今天没有类继承这四个类。四个类的构造方法与 `Tactic` 的装配 op 由 §8.4 的纯 Python 构造测试钉住（复审 R10）；经 Isabelle 的端到端覆盖对 RULE 是 §8.4 的其余用例、对 TACTIC 是 `Tactic5`，对 CASE_SPLIT/INDUCT 没有 golden 到达 round 1。
3. the convergence check 还收到 `from_state`——那个从未接收任何 round 的状态；覆写只能把它用作预跑 `opr` 的起点（`model.py:10782`）；直接查 `from_state` 就重现了作废计划的 blocker（§7.1）。
4. 在 `SubgoalMaker` 与 `StdBlock` 之间的 MRO 位置插 `_refresh_the_beginning_opr` 覆写，会看到 round 0 的状态（§4.1）。
5. 失败的 `SubgoalMaker` 的 `dest` 没有哪个读者依赖它"未初始化"（§5.6）；D8 之后也没有读者不看 status 就把它当结果显示——`GoalNode` 的目标头部与删除时的存档行除外。

---

## 6. 执行次数、日志与时间记账

### 6.1 beginning op 的执行次数（经 `Minilang_State.execute`）

| 情形 | 今天 | C24 |
|---|---|---|
| 常见情形（round 0 收敛） | 2 | 1 |
| round 0 的执行失败 | 2 | 1 |
| round 0 的 the convergence check 失败 | 1 | 1 |
| k 个 instantiation round 后收敛 | k+2 | k+1（交互仍是 k 次） |
| round k ≥ 1 的执行失败 | k+2，最后一次不带 rounds，节点报告成功 | k+1，节点如实失败 |
| 16 轮上限 | 16（全进 scratch state） | 16（全进 `dest`） |

运行例子：第 1 步今天 2 次、C24 1 次；第 2 步今天 3 次、C24 2 次。`CaseSplit_Like` 成功后的再执行（`model.py:7650-7659`）两种设计下都多 1 次，它从不探测。

### 6.2 `Tactic_Like` 的服务端预跑（不变）

每个整体扫描 `dest` 非空的 round 预跑一次（`Agent/agent_server.ML:1415-1460`）：每个不收敛的 round，加上"收敛时只剩只出现在一个派生子目标里的变量"的那个 round（七个 PostInst golden 里有五个是这种形状，`Tactic5` 的 `rule exI` 一步也是）。`CaseSplit_Like` 的 the convergence check 没有预跑。计划记录的最坏情形 B6（闸门预跑 + the probe 的执行与预跑 + 循环后的执行，同一个 op 至多 4 次服务端执行，`AOA_SCHEMATIC_VARIABLE_PLAN.md:872-873`）降为 3 次。带 prove-in-time 事实的 op 每次执行都做自己的最多 10 s 的 MePo 搜索，没有缓存（`Agent/agent.ML:1166-1225`），所以搜索次数随执行次数一起下降。

### 6.3 `proof_oprs.yaml`（D9）

每个 round 现在都经过记日志的 `execute`：一条 PROOF_OPERATION "execute" 记录（`model.py:2011-2020`），失败时再加一条 OPERATION_ERROR 记录（`:2033-2038`）。

| 情形 | 今天 | C24 |
|---|---|---|
| 常见情形 | 1 条 execute（来自循环后的那次执行） | 1 条 execute |
| round 0 的执行失败 | 1 execute + 1 error | 相同 |
| round 0 的 the convergence check 失败 | 0 | 1 条 execute，无 error 记录 |
| k 个 round | 1 | k+1 条 execute |
| round k ≥ 1 的执行失败 | 1 条 execute（记的是不带 rounds 的 op，与实际不符） | k+1 execute + 1 error |
| 16 轮上限 | 0（十六次执行毫无痕迹） | 16 |

这是想要的：规则变成"凡执行进树所拥有的状态都记日志，只有用完即弃的执行（`_rewrite_trial`）用 `log=False`"。每条记录的 `operation` 串带着该 round 已烘焙的实例化（`Minilang_Operation.__str__`，`:1700-1701`），失败的 op 也有记录。没有代码读这个文件：Python 里只有 `model.py` 写它，`test_log_sink_surrogate_immunity.py:59` 只碰文件句柄；文档里只在 `IsaMini/AoA/CLAUDE.md:143`、`IsaMini/AoA/AGENTS.md:142`、`IsaMini/AoA/docs/DEVELOP.md:497` 被列出。文件里后续的 `$N` 状态名会整体前移，因为不再为 scratch state 分配名字（`model.py:1979-1982`）。

### 6.4 时间记账

每次执行仍无条件调用 `on_operation_start`/`on_operation_end`（`model.py:2021`、`:2031-2032`、`:2042-2043`），后者把 Python 侧测得的 RPC 墙钟秒数加进 `total_isabelle_time`（`:14806-14808`）。这个总数因此恰好减少被删掉的那些执行的时间，体现在 `_log_cost` 那一行（`:13891`）和 toplevel 返回的成本元组里（`toplevel.py:383`），评测统计会显示更少的 Isabelle 时间。服务端预跑不经 `execute`（`model.py:2760-2776`），两种设计下都不计入。

工作时间预算（`elapsed_working_time` 对 `timeout_seconds`，`model.py:13741-13743`）消耗变慢：例如一个 15 s 超时的 Tactic 现在花 15 s 而不是 30 s。

不变的：重放时间（`replayed_ms`，`toplevel.py:87-125`）。Tactic 装配时记录的时间来自收敛那个 round 的 `TACTIC_TIMES`（`model.py:11159-11163`）；常见情形下那是第一次运行，而不是今天的第二次（可能更"热"的）运行，见 §10 第 2 条。

### 6.5 `dest.messages`（D21）

D21 之前，校验答案时发出的 hint NOTICE 会进入下一次 `proof_opr` 的结果（§4.10）；D21 之后一次 `proof_opr` 的结果只含本 op 自己的消息，`dest.messages` 恰是收敛那个 op 的消息（§5.9 第 8 条）。

---

## 7. 收敛机制为什么仍然成立

### 7.1 作废的那份计划错在哪里

它的循环（`AOA_INITIAL_GOAL_SCHEMATIC_PLAN.md:146-161`）每轮查 `init_state.schematic_variables_of(whole=True)`，却从没有把收集到的 rounds 作用到 `init_state` 上，所以每轮看到的都是同一批变量。它自称"照抄 `model.py:6500-6533`，去掉 scratch 双执行"（`:146`）——实际去掉的不只是 scratch state，而是每轮的那一次执行。这与 C1 的失败同形（`AOA_SCHEMATIC_VARIABLE_PLAN.md:854-858`："已实例化的变量每轮重复被提供 → 烧满 16 轮交互后硬报错"）：检查读的是从未接收 rounds 的东西。owner 那句约束（`:526-527`）说作废计划"正是在这里出的 blocker"；那次评审的明确记录不在计划文件里，上面的诊断是从循环的形状推出来的，本文不把它写进 owner 的文档。

### 7.2 收敛需要的两个条件

(a) 在 round k，the convergence check 读的状态必须是"带着 round 0 到 k−1 的 beginning op，从同一个 from_state 执行"的结果。
(b) the convergence check 读的必须是实例化之后的数据。

### 7.3 C24 满足 (a)

round 0 由 `StdBlock._refresh_the_beginning_opr` 把不带 rounds 的 beginning op 从 `ml_state` 执行进 `dest`（`:6040`）；round k ≥ 1 由 `_run_the_probe` 把 `_beginning_opr_with_insts(rounds)`（`rounds` 里是迄今收集的全部 round）从同一个 `from_state` 执行进 `dest`。ML 侧在 base op 之后真正施加这些 rounds：`apply_post_insts` 是一个左折叠（`Agent/agent.ML:1424-1442`），RULE、TACTIC、CASE_SPLIT、INDUCT 四个分支都在最后调用它（`:1593`、`:1624`、`:1626-1627`、`:1650`）。紧接着的语句就在同一个 `dest` 上运行 the convergence check（round 0 时中间只有 `return None`、`fail` 的判断与 `self._probes_post_insts and self._post_insts is None` 这个判断）。各 round 不会叠加：每个 round 都从 `from_state` 执行，`dest` 只被覆盖，从不作为输入（这正是 D6 的 assert 守住的）。the convergence check 还收到 `from_state`，但只作为 `Tactic_Like` 预跑同一个带 rounds 的 op 的起点（§7.4）。

### 7.4 C24 满足 (b)

这里什么都没变。`SubgoalMaker` 的默认判据以 `whole=True` 读 `dest`。`Tactic_Like` 先做同样的整体扫描，非空时把**同一个带 rounds 的 op** 交给服务端预跑，从 `from_state` 重跑；`derived_subgoals_of` 走"栈深不变"那一支，读终态而不读 Goals 消息（`library/proof.ML:826-840`，该支在 `:836-839`），终态是施加了 rounds 之后的。所以 `Tactic_Like` 的判据不是"只读 `dest`"，而是"整体扫描读 `dest`，逐子目标的查询读预跑的终态"——两者看到的都是已累积的 rounds（评审 C9 要求如实写明）。`CaseSplit_Like` 保留默认判据，因为它的 Goals 消息发于实例化之前（`model.py:6862-6867`）。

### 7.5 为什么这只是换了存放位置

scratch state 从来没有为收敛出过力，它只是执行结果存放的地方。施加 rounds 的是执行本身，而 C24 保留了每个 round 恰好一次的真实执行；去掉的是循环后那第二次执行和用完即弃的目的地。交互在 `dest` 上校验 agent 的答案，`dest` 里是施加了 round 0 到 k−1 的状态——与 scratch state 当时存的值相同；校验用的 `apply_post_insts` 原语（`Agent/agent_server.ML:1890-1903`）正是下一个 round 的执行要折叠进去的那个。所以 owner 在 `AOA_SCHEMATIC_VARIABLE_PLAN.md:526-527` 保护的循环结构——"每轮把已累积的 rounds 真正作用到目标上，好让下一轮看见还剩什么"——字面上没有变；只是 round 0 那次执行属于 `StdBlock._refresh_the_beginning_opr`，循环读作"检查、问、重跑"。

一个推论（§5.2 已用）：一个校验过的 round 本身不会让下一次执行失败，因为校验与执行在同一个 base 结果上施加同一个折叠；一个 round 失败只能来自墙钟上限。

---

## 8. golden 与测试

### 8.1 既有 golden 全部逐字节不变：理由

(1) **同样的 op、同样的顺序、同样的 from_state**。round 0 是 `StdBlock._refresh_the_beginning_opr` 执行的闸门检查过的 op，与今天 round 0 的 `scratch_op` 是同一个值（`_pack_post_insts` 把 `None` 与 `[]` 同样打包，`model.py:1674-1675`）；round i ≥ 1 执行 `_beginning_opr_with_insts(rounds_i)`，`rounds_i` 也相同（答案相同，见 (3)）。今天循环后的那次执行是收敛那个 round 的 op。所以新的执行序列就是今天的序列去掉那次重复的执行（收敛时），或去掉那次重复的、失败的执行（round 0 执行失败时）。

(2) **各次执行互不影响**。`proof_opr(from, to, op)` 只读 `from`，只在成功时写 `to`（`Agent/agent_server.ML:1100-1106`）。四个命令不推进会话共享的计数器（§5.9 留给记忆的第 1 条）。prove-in-time 事实的名字在取事实时由 `next_pit_name` 分配（`model.py:2112-2115`、`:12449-12452`），不是每次执行分配——`RetrieveFact2.yml` 里的 `P__I__T__0` 因此不变。prove-in-time 搜索没有缓存（`Agent/agent.ML:1166-1225`）。所以少执行一次不改变之后任何结果；唯一的副作用是之后状态名 `$N` 的编号（`model.py:1979-1982`），而没有任何 golden 含 `$<数字>`（grep `Tests/*.yml`）。消息方面：D21 先于 C24 落地，之后一次 `proof_opr` 的结果只含本 op 自己的消息（§4.10）；在 D21 之前，校验答案留下的 hint NOTICE 会被下一次 `proof_opr` 带走——今天带走它的是被丢弃的 scratch 执行，C24 下会是保留下来的 round，这正是 D21 要先落地的原因。

(3) **读到的值相同**。整体扫描、`Tactic_Like` 是否预跑及其结果、提示文字（`model.py:4135-4158`）、校验（`Agent/agent_server.ML:1890-1903`）在 `dest` 名下读到的 ML 值，与今天在 scratch state 名下读到的相同。于是交互、答案、rounds、预跑次数都相同；后者要紧，因为 `Tactic2`、`Tactic5` 打印预跑次数（`Tests/Tactic2.yml:13`、`Tests/Tactic5.yml:17`、`:51`）。

(4) **最终的树相同**。收敛后 `dest` 里是收敛那个 op 的状态，全部字段都被重写（`model.py:2047-2060`），与今天循环后那次执行存下的值相同；消息也来自同一个 op，所以回填、`new_subgoals_count`、`Consider_Case_Msg`、derived goal 的打印都相同。

(5) **golden 里的失败路径都是 round 0 的执行失败、且是确定性的**。文字来自同一个 op 在同一个 from_state 上的执行，`dest` 在两种设计下都不变。没有既有 golden 含 round k ≥ 1 的失败或 the convergence check 的失败——会触发 round 的三个 golden 打印的是已实例化的派生目标（`PostInstRuleShared.yml:27`/`:31`、`PostInstValidation.yml:36`/`:40`、`Tactic5.yml:44`/`:48`，以及 `Tactic5.yml:52` 的 `schematic variables left: False`，它读的是节点自己的 after-beginning state）；今天这种失败会让这些行显示未实例化的目标。注意 `_assert_schematic_free` 打印的 "residual … schematics" 行读的是**规则之前**的状态（`test.py:1136-1141` 读 `root.sub_nodes[1]._state_after_beginning()`，即主 `GoalNode` 第一个子节点的 `ml_state`；`PostInstRule.yml:25` 显示 `goal: Q ?c` 而 `:41` 仍打印 `residual term schematics: []`），它不能检测残留，第一稿引它作证据是错的（评审 C12）；C24 不改它。没有 golden 达到上限（grep "Could not eliminate" 无结果）。

### 8.2 各路径由哪些 golden 覆盖（grep 核对）

- **k ≥ 1 个 round**：只有 `PostInstRuleShared` 与 `PostInstValidation`（`InferenceRule`，一个 term round，`interaction kinds fired: ['term']`）和 `Tactic5`（`rule conjI`，一个 round）——它们也是仅有的含 "Post-rule instantiation prompt" 的 golden。其余五个 PostInst golden（`PostInstRule`、`PostInstRuleType`、`PostInstRuleMultiTerm`、`PostInstRuleTermPinsType`、`PostInstRuleTermThenType`）打印 `interaction kinds fired: []`，而树里仍可见只出现在一个派生子目标里的 schematic 变量（如 `Tests/PostInstRule.yml:25` 的 `goal: Q ?c`）：它们在 round 0 带着这样一个变量收敛，整体扫描非空、因而有一次预跑，`Tactic5` 的 `rule exI` 一步也是（其预跑数直接打印，`Tests/Tactic5.yml:17`）。没有 `CaseSplit`/`Induction` golden 触发事后实例化的 round。`PostInstValidation` 有五个答案被校验拒绝，校验现在针对 `dest`，内容相同。
- **round 0 的执行失败**：`Tactic4`（三种失败）、`Tactic6` 的 `FACT_IN_TIME_FAIL`、`RetrieveFact2`（prove-in-time 规则的 `InferenceRule`，之后尝试 autoconvert）、`AutoRewriteFallback`、`AutoRewriteFallbackCascade`（失败的 RULE 被换成 Rewrite）、`CaseSplitUndeclared`、`InductionUndeclared`、`Induction_IllTypedBoundVar`。
- **根本不执行**（beginning op 本身是 `FailureReason`，`_refresh_me_alone` 在执行之前处理，`model.py:6105-6108`；或闸门先拒绝）：`Tactic6` 的"事实找不到"（`_tactic_opr` 返回 `FailureReason`，`:11150-11154`，`Tests/Tactic6.yml:8` 没有执行过任何东西）；`GateSchematic`，C24 前后都打印 `state landed on target: False`（`Tests/GateSchematic.yml:21`、`:36`、`:50`）。
- **必须逐字节不变**：`test_AoA.py` 里除 `IMO_1966_p5`、`HavePowerParsing`、`UnfoldCertJoin` 之外的全部（397 个被跟踪的 golden）；重点看 `InferenceRule*`（9 个）、`PostInst*`（7 个）、`GateSchematic`、`CaseSplit*`（28 个）、`Induction*`（19 个）、`Amend*Induction*`、`Tactic1`–`6`、`TacticPrompt`、`TacticSync`、`TacticQuery`、`UserOp_*`（8 个）、`Nested_InferenceRule_Leak`、`Define_CaseSplitInductionRedirect`、`RetrieveFact2`、`AutoRewriteFallback*`、13 个打印 "derived goal" 的（D8）、26 个打印 `notice:` 的（D21）。已知与本线无关的失败：`SemanticKNN_patterns`、`SemanticKNN_induction_rule`、`QueryNullFields`、`QueryScalarStringField`、`QuerySearchSummary`、`ReferFactByProposition`、`ForkProviderConflict`（`TACTIC_DESIGN.md:385`、`:387`）。
- **代码阅读无法排除的一点**：成败取决于运行顺序或冷热的 op——任何接近自己墙钟上限的 op（§5.2 的时限清单），不只是 Tactic 与 prove-in-time 搜索。今天它们偶然多得一次运行（冷的 scratch 运行之后是热的那次执行）。`Tactic3`、`InferenceRule_ProveInTime_Backfill`、`RetrieveFact2` 是例子；哪些步接近时限不测量不知道，所以不预先列名单。规则（D17）：任何以 "Timeout" 或 `FACT_IN_TIME_FAIL` 翻转的 golden 先按 §10 第 1 条看、单独重跑一次排除抖动，再报 owner。

### 8.3 运行方式

REPL（`contrib/Isa-Mini` 下；本线用自己的一对端口，不占 goal hints 那条线在 6688 上的 REPL）：

```
RPC_Host=127.0.0.1:27190 isabelle REPL -l Minilang_AoA -o threads=8 -o document=false -T 900 127.0.0.1:6690 <out-dir>
```

改了 `.ML`（D21）后起 REPL 的办法：Isa-REPL 工具在启动时自己重建 logic heap（`contrib/Isa-REPL/src/scala/repl_tool.scala:103-110`，`Build.build_logic(…, build_heap = true)`），而设了 `RPC_Host` 却没有 host 在听时这次重建失败（2026-10-10 23:48 实测），所以先 `env -u RPC_Host isabelle build -b Minilang_AoA`（约 20 s；永不加 `-c`/`-f`），再起 REPL。这与主仓库 `CLAUDE.md:35`（改 `.ML` 只重启 REPL、不重建 heap）、`IsaMini/AoA/CLAUDE.md:122`、Isa-Mini `CLAUDE.md:9` 相抵触：§8.8 第 1 步请求授权时必须说明这个抵触与上面的证据，owner 明确同意后才跑。REPL 会缓存已加载的测试 theory：改了 `Tests/User_Operation_Test_Base.thy` 之类的基座也要重启。

运行器（`IsaMini/AoA` 下，一次只跑一个，输出必须重定向；`-f NAME` 跑单个用例；全量回归 `-x IMO_1966_p5,HavePowerParsing,UnfoldCertJoin`；运行器的 `timeout` 从 1500 s 提到 3600 s，因为 isolated-db 用例真正跑起来后单个就要几十秒；`EMBEDDING_API_KEY` 在 Isabelle 的用户设置里（`~/.isabelle/<Isabelle 版本>/etc/settings`），经 `isabelle env` 进入运行器的环境——运行器在自己的进程里起 RPC host（`test_AoA.py:73`），所以运行器与 pytest 永远经 `isabelle env` 启动、不用裸 python）：

```
timeout 3600 isabelle env ../../../../.venv/bin/python -u ../../test_AoA.py \
  -x IMO_1966_p5,HavePowerParsing,UnfoldCertJoin --repl-addr 127.0.0.1:6690 --rpc-addr 127.0.0.1:27190 > <file> 2>&1
```

单元测试：`isabelle env python -m pytest IsaMini/AoA/test_post_inst_probe.py IsaMini/AoA/test_user_operations.py -q`。

### 8.4 新单元测试 `IsaMini/AoA/test_post_inst_probe.py`（D11）

照 `test_user_operations.py` 的写法（`object.__new__` 构造节点，假状态，`bare_session` 绑定会话，`:77-83`、`:236-245`）。节点是真实的 `InferenceRule`，入口是真实的 `SubgoalMaker._refresh_the_beginning_opr()`（经 `StdBlock._refresh_the_beginning_opr` 执行 round 0、经覆写的 `except` 转换失败），the convergence check 是真实的 `Tactic_Like._probe_residual_schematics`（不替换），整体扫描与服务端预跑由假状态回答——这样改名后的覆写与调用形状 `(from_state, dest, opr)` 也被钉住。假节点要设 `rule_ref`、`_post_insts`、`ml_state`、`sub_nodes = []`、`_state_before_ending_`、`_first_time = True`、`_supplied_proofs = None`（首次运行时确认这个清单够用）；假状态要有 `leading_goal = None`（`_beginning_opr_err_msgs` 读）、`new_subgoals_count = None`（`_should_open_proof_block` 据此不开块，`model.py:7240-7243`）、`initialized()`、`messages = []`。假状态的 `execute` 接受 `log=`、在 `dest` 为 `None` 时返回一个能 reset 的新状态，`reset` 清掉全部字段（照 `model.py:2090-2096`，评审 C2），所以旧代码能跑到断言处、因断言失败，而不是崩溃。失败用例断言覆写返回的 `FailureReason.reason`（头行来自 `InferenceRule._fail_header`，`:10847`，经 `Tactic_Like._beginning_opr_err_msgs` `:10798-10801` 拼接，例如 `"Fail to apply the inference rule.\nthe op failed"`）。最后一个用例是纯 Python 的构造方法测试（复审 R10）：四个类用 `object.__new__` 建、只设各自构造方法读的字段，断言 `_beginning_opr_with_insts([R0, R1])` 等于直接的工厂调用、`beginning_opr()` 在 `_post_insts=[R0]` 下等于 `_beginning_opr_with_insts([R0])`、`Tactic.assembled_beginning_opr()` 与 live op 只差第五个参数；它在 dd7707d 上也通过（那里的 `beginning_opr` 读的是字段），所以是"在旧代码上失败"的第二个例外。各类构造方法读的字段名在首次运行时按代码确认。

```python
"""Unit tests of the post-instantiation probe (docs/TACTIC_DESIGN.md section
13, C24): `SubgoalMaker._refresh_the_beginning_opr` runs `_run_the_probe` after
`StdBlock._refresh_the_beginning_opr` executed round 0 into the destination
state; every later round executes into it again, the convergence check reads
it, the converged round's state is the node's result, and any failing round is
the node's failure.  A real `InferenceRule` with its real convergence check,
over stand-in states.  No REPL, no RPC."""
import asyncio
import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from Isabelle_RPC_Host import IsaTerm                                        # noqa: E402
from IsaMini.AoA.model import (                                              # noqa: E402
    FailureReason, InferenceRule, Interaction_InstantiatePostSchematics, IsabelleError,
    Minilang_Operation, _MAX_POST_INST_ROUNDS)
from IsaMini.AoA.test_user_operations import bare_session                    # noqa: E402

X, NAT = IsaTerm.from_isabelle("?x"), IsaTerm.from_isabelle("nat")
R0, R1 = [("?x", "0")], [("?x", "1")]
FAILED = "Fail to apply the inference rule.\nthe op failed"


def rule(*rounds):
    """The beginning op of `rule_node()` carrying `rounds`."""
    return Minilang_Operation.RULE(None, list(rounds))


class State:
    """A stand-in Minilang_State for a RULE that leaves ?x until it carries
    `converges_at` rounds (None: never).  `execute` records (op, destination,
    log) and raises on the calls numbered in `fails` (from 0); the server-side
    prerun puts ?x in both derived subgoals, or in one when not `shared`, and
    raises when `prerun_fails`."""
    def __init__(self, converges_at=0, fails=(), shared=True, prerun_fails=False):
        self.converges_at, self.fails, self.shared = converges_at, set(fails), shared
        self.prerun_fails = prerun_fails
        self.runs: list = []
        self.preruns = 0
        self.rounds: 'int | None' = None
        self.leading_goal = None
        self.new_subgoals_count = None
        self.messages: list = []
        self._initialized = False
    def initialized(self) -> bool:
        return self._initialized
    def _left(self, n: int) -> bool:
        return self.converges_at is None or n < self.converges_at
    async def execute(self, opr, dest, *, log=True):
        if dest is None:                       # the scratch state of the pre-C24 probe
            dest = State(self.converges_at)
        self.runs.append((opr, dest, log))
        if len(self.runs) - 1 in self.fails:
            raise IsabelleError(["the op failed"], None)
        dest.rounds, dest._initialized = len(opr.arg[1]), True
        return dest
    async def schematic_variables_of(self, whole=False):
        return ({X: NAT} if self._left(self.rounds) else {}), {}
    async def schematic_vars_of_derived_subgoals(self, opr):
        self.preruns += 1
        if self.prerun_fails:
            raise IsabelleError(["the prerun failed"], None)
        left = ({X: NAT} if self._left(len(opr.arg[1])) else {}), {}
        return [left, left if self.shared else ({}, {})]
    async def reset(self):
        self.rounds, self._initialized = None, False
        self.leading_goal, self.new_subgoals_count, self.messages = None, None, []


def rule_node(src: State, dest: State, post_insts=None):
    """A bare InferenceRule whose beginning op is a RULE with no rule, with
    `src` as its ml_state and `dest` as its after-beginning state."""
    node = object.__new__(InferenceRule)
    node.rule_ref, node._post_insts = None, post_insts
    node.ml_state, node.sub_nodes, node._state_before_ending_ = src, [], dest
    node._first_time, node._supplied_proofs = True, None
    return node


def probe(converges_at=0, fails=(), shared=True, prerun_fails=False, post_insts=None):
    """A from_state, a destination state, and the node over them."""
    src = State(converges_at, fails, shared, prerun_fails)
    dest = State(converges_at)
    return src, dest, rule_node(src, dest, post_insts)


def agent(*answers) -> list:
    """Bind a bare session whose agent answers the k-th interaction with
    `answers[k]`; returns the interactions asked."""
    asked: list = []
    async def launch_interaction(interaction):
        assert isinstance(interaction, Interaction_InstantiatePostSchematics)
        asked.append(interaction)
        return answers[len(asked) - 1]
    bare_session().launch_interaction = launch_interaction
    return asked


def refresh(node) -> 'FailureReason | None':
    return asyncio.run(node._refresh_the_beginning_opr())


def test_the_common_case_is_one_execution_into_dest():
    src, dest, node = probe(converges_at=0)
    asked = agent()
    assert refresh(node) is None
    assert src.runs == [(rule(), dest, True)] and src.preruns == 0
    assert node._post_insts == [] and asked == []
    assert node.beginning_opr() == src.runs[0][0]      # round 0 is the op assemble packs


def test_a_confined_variable_converges_after_one_prerun():
    src, dest, node = probe(converges_at=1, shared=False)
    asked = agent()
    assert refresh(node) is None
    assert src.runs == [(rule(), dest, True)] and src.preruns == 1
    assert node._post_insts == [] and asked == []


def test_k_rounds_are_k_plus_1_executions_into_dest():
    src, dest, node = probe(converges_at=2)
    asked = agent(R0, R1)
    assert refresh(node) is None
    assert src.runs == [(rule(), dest, True), (rule(R0), dest, True), (rule(R0, R1), dest, True)]
    assert src.preruns == 2 and node._post_insts == [R0, R1]
    assert len(asked) == 2 and all(i.state is dest and i.kind == "term" for i in asked)
    assert node.beginning_opr() == src.runs[-1][0]


def test_a_failing_first_round_runs_once():
    src, dest, node = probe(fails={0, 1})
    asked = agent()
    assert refresh(node) == FailureReason(FAILED)
    assert len(src.runs) == 1 and not dest.initialized() and node._post_insts is None


def test_a_failing_later_round_is_the_failure():
    src, dest, node = probe(converges_at=1, fails={1})
    asked = agent(R0)
    assert refresh(node) == FailureReason(FAILED)
    assert src.runs == [(rule(), dest, True), (rule(R0), dest, True)]
    # D7: no reset -- dest keeps round 0's state (flips if the owner picks D7's alternative)
    assert node._post_insts is None and dest.initialized() and dest.rounds == 0


def test_a_failing_convergence_check_in_round_0_is_the_failure():
    src, dest, node = probe(converges_at=1, prerun_fails=True)
    asked = agent()
    assert refresh(node) == FailureReason("Fail to apply the inference rule.\nthe prerun failed")
    assert src.runs == [(rule(), dest, True)] and asked == []
    assert node._post_insts is None and dest.initialized() and dest.rounds == 0


def test_the_round_cap():
    src, dest, node = probe(converges_at=None)
    asked = agent(*[R0] * _MAX_POST_INST_ROUNDS)
    assert refresh(node) == FailureReason(
        f"Fail to apply the inference rule.\nCould not eliminate the residual schematic "
        f"variables of this RULE operation within {_MAX_POST_INST_ROUNDS} rounds of instantiation.")
    assert len(src.runs) == len(asked) == _MAX_POST_INST_ROUNDS
    assert all(d is dest for _, d, _ in src.runs) and node._post_insts is None


def test_a_probed_node_executes_its_op_once():
    src, dest, node = probe(converges_at=None, post_insts=[R0])
    asked = agent()
    assert refresh(node) is None
    assert src.runs == [(rule(R0), dest, True)] and asked == []


def test_each_builder_packs_the_rounds_it_is_given():
    """The builders of the four probing classes (passes on dd7707d too): the
    op carries exactly the rounds passed in, `beginning_opr()` passes
    `_post_insts`, and Tactic's assembled op differs from the live op only in
    its fifth slot.  The fields each builder reads are set and nothing else."""
    from IsaMini.AoA.model import CaseSplit, Induction, Tactic, Tactic_Times_Msg
    def bare(cls, **fields):
        node = object.__new__(cls)
        for name, value in fields.items():
            setattr(node, name, value)
        return node
    cases = [
        (bare(InferenceRule, rule_ref=None, _post_insts=[R0]),
         lambda insts: Minilang_Operation.RULE(None, insts)),
        (bare(CaseSplit, target_isabelle_term="t", _resolved_rule_str=None, no_simp=False,
              _post_insts=[R0], _case_vars_of_child=lambda i: None),
         lambda insts: Minilang_Operation.CASE_SPLIT("t", None, None, False, insts)),
        (bare(Induction, target_isabelle_term="t", variables=[], fact_refs_to_generalize=[],
              _resolved_rule_str=None, no_simp=False, _post_insts=[R0],
              _case_vars_of_child=lambda i: None),
         lambda insts: Minilang_Operation.INDUCT("t", None, [], [], None, False, insts)),
        (bare(Tactic, tactic_full="HOL.simp", arguments=None, fact_refs=[], _post_insts=[R0]),
         lambda insts: Minilang_Operation.TACTIC("HOL.simp", None, [], insts, None)),
    ]
    for node, factory in cases:
        assert node._beginning_opr_with_insts([R0, R1]) == factory([R0, R1])
        assert node.beginning_opr() == node._beginning_opr_with_insts([R0])
    tactic = cases[-1][0]
    tactic.sub_nodes, tactic._state_before_ending_ = [], State()
    tactic._state_before_ending_.messages = [Tactic_Times_Msg((1, 2))]
    assert tactic.assembled_beginning_opr() == Minilang_Operation.TACTIC("HOL.simp", None, [], [R0], (1, 2))
```

它钉住：常见情形一次执行进 `dest` 且记日志，round 0 的 op 就是 `assemble` 打包的 op（D2）；只剩只出现在一个派生子目标里的变量时一次执行加一次预跑、不发交互；k 个 round 是 k+1 次执行、全进同一个 `dest`、每次带着已累积的 rounds、交互建在 `dest` 上、节点保留的 op 等于最后执行的 op；round 0 执行失败只跑一次、`dest` 未初始化；round k ≥ 1 失败如实返回 `FailureReason`、没有不带 rounds 的重跑、`_post_insts` 为 `None`、`dest` 留着 round 0 的状态（D7）；round 0 的 the convergence check 失败同样如实、`dest` 已初始化（评审 C7）；上限是 16 次执行、16 次交互、文字逐字相同；已探测过的节点只执行一次。`FailureReason` 的相等比较与 `_beginning_opr_err_msgs` 的拼接（`model.py:10798-10801`：ML 没给 "Fail to apply" 头时加 `_fail_header`，没有当前目标时不附目标）在首次运行时确认。在旧代码上，除 `test_a_probed_node_executes_its_op_once` 与 `test_each_builder_packs_the_rounds_it_is_given` 外每一项都失败（§8.6）。

### 8.5 模型测试里的执行计数（D12；`IsaMini/AoA/test.py`，只断言、不打印，golden 不变）

`Minilang_State.execute` 在 RPC 之前、`try` 之外调用 `session.on_operation_start(self.name, opr.command, opr.arg)`（`model.py:2021`），失败的执行也报；基类钩子是空操作（`:14802-14804`）；每个模型测试用例有自己的 Session，测试本来就在它上面替换方法而不恢复（`test.py:89`、`:1104`、`:1150`、`:18945`）。所以计数放在用例自己的 session 上，随 session 消失，不需要 restore，忘记恢复就污染同进程后续测试的可能性在形状上消失（评审 C15）。`_count_derived_subgoal_preruns`（`test.py:18811-18821`）与它的两个调用点原样保留：服务端预跑不经 `execute`（`model.py:2760-2776`）。

```python
def _count_operations(session: Session, command: str) -> dict:
    """Count the executions of `command` the session starts (failing ones
    included), through its own `on_operation_start` hook; no restore is
    needed, the session belongs to this case alone."""
    runs = {"n": 0}
    def on_operation_start(step_id, operation, args):
        if operation == command:
            runs["n"] += 1
    session.on_operation_start = on_operation_start
    return runs
```

`_test_Tactic2`（取代 `test.py:18869-18884`）：

```python
@model_test("Tactic2", "Test_Tactic2.thy", 9, isolated_db=True)
async def _test_Tactic2(root: Root, file: MyIO):
    """The probe's short-circuit: a Tactic leaving no schematic variable
    converges on the read-only whole scan, with no server-side prerun and one
    execution."""
    calls = {"n": 0}
    restore = _count_derived_subgoal_preruns(calls)
    runs = _count_operations(root.session, "TACTIC")
    try:
        root.session.age += 1
        await root.fill("1", [Tactic.gen_single({"thought": "simp closes it", "tactic": "simp"})])
    finally:
        restore()
    print_header("After simp", file)
    root.print(0, file)
    file.write(f"derived-subgoal preruns: {calls['n']}\n")
    assert calls["n"] == 0 and runs["n"] == 1, runs
    assert _count_unfinished(root, file) == 0
```

`_test_Tactic4`（取代 `test.py:18907-18924`）：

```python
@model_test("Tactic4", "Test_Tactic4.thy", 10, isolated_db=True)
async def _test_Tactic4(root: Root, file: MyIO):
    """The errors of the arguments come verbatim from Isabelle: the method's
    own parser, the lexer, and a method that does not apply.  Each failing op
    runs once."""
    runs = _count_operations(root.session, "TACTIC")
    first = True
    for thought, tactic, arguments in [
            ("a bad argument", "simp", "foo"),
            ("an unclosed cartouche", "simp", "‹junk"),
            ("a rule that does not match", "rule", "conjI")]:
        before = runs["n"]
        root.session.age += 1
        gns = [Tactic.gen_single({"thought": thought, "tactic": tactic, "arguments": arguments})]
        await (root.fill("1", gns) if first else root.amend("1", gns))
        first = False
        print_header(f"Tactic {tactic} {arguments}", file)
        root.print(0, file)
        node = root.locate_node("1")
        file.write(f"status: {node.status.status.name}\n")
        assert node.status.status == EvaluationStatus.Status.FAILURE
        assert runs["n"] - before == 1, runs
```

`_test_Tactic5`（取代 `test.py:18927-18976`；只改 docstring、计数器的安装与两处断言）：

```python
@model_test("Tactic5", "Test_Tactic5.thy", 14, isolated_db=True)
async def _test_Tactic5(root: Root, file: MyIO):
    """The shared-variable criterion of Tactic_Like, with the prerun and
    execution counters cumulative: `rule exI` leaves ?x in its one subgoal --
    no interaction, one prerun, one execution; `rule conjI` on it shares ?x
    between two subgoals -- one term interaction answered `?x := 0`, one more
    prerun, two more executions (the round's own each time), no schematic
    left; the two cases close by the sorried facts."""
    calls = {"n": 0}
    kinds: list[str] = []
    restore = _count_derived_subgoal_preruns(calls)
    runs = _count_operations(root.session, "TACTIC")
    async def stub(interaction):
        if isinstance(interaction, Interaction_InstantiatePostSchematics):
            kinds.append(interaction.kind)
            print_header(f"Post-rule instantiation prompt (kind={interaction.kind})", file)
            await interaction.prompt(0, file)
            insts = [(n, "0::nat") for n, _ in interaction.schematic_vars]
            return await interaction.answer(AnswerInstantiate(instantiations=insts))
        raise NotImplementedError(f"Unstubbed interaction in Tactic5: {type(interaction).__name__}")
    root.session.launch_interaction = stub
    try:
        root.session.age += 1
        await root.fill("1", [Tactic.gen_single({"thought": "a witness, picked later",
                                                 "tactic": "rule", "arguments": "exI"})])
        print_header("After rule exI", file)
        root.print(0, file)
        file.write(f"interactions: {kinds}, preruns: {calls['n']}\n")
        assert kinds == [] and calls["n"] == 1 and runs["n"] == 1, runs
        # one derived subgoal opens no GoalNode: the next step is the sibling step 2
        root.session.age += 1
        await root.fill("2", [Tactic.gen_single({"thought": "split the conjunction",
                                                 "tactic": "rule", "arguments": "conjI"})])
        print_header("After rule conjI", file)
        root.print(0, file)
        file.write(f"interactions: {kinds}, preruns: {calls['n']}\n")
        assert kinds == ["term"] and calls["n"] == 2 and runs["n"] == 3, runs
        conj = cast(Tactic, root.locate_node("2"))
        tvs, tyvs = await conj._state_after_beginning().schematic_variables_of(whole=True)
        file.write(f"schematic variables left: {bool(tvs or tyvs)}\n")
        assert not (tvs or tyvs)
        cases = [c for c in conj.sub_nodes if isinstance(c, GoalNode)]
        assert len(cases) == 2
        for case, fact in zip(cases, ["p0", "q0"]):
            root.session.age += 1
            await root.fill(f"{case.id}.1",           # the case's hole
                            [Tactic.gen_single({"thought": fact, "tactic": "rule", "arguments": fact})])
        print_header("Closed", file)
        root.print(0, file)
    finally:
        restore()
    assert _count_unfinished(root, file) == 0
```

`_test_PostInstRuleShared`（取代 `test.py:1210-1226`）：

```python
@model_test("PostInstRuleShared", "Test_PostInstRuleShared.thy", 21)
async def _test_PostInstRuleShared(root: Root, file: MyIO):
    # ?c spans TWO derived subgoals (Q ?c, R ?c) — the S4-relaxed convergence
    # (interact only on variables shared by ≥2 derived subgoals) must still
    # fire here, keeping the interaction covered now that the confined-variable
    # fixtures no longer trigger it.  One instantiation round: two executions.
    print_header("Initial", file)
    root.print(0, file)
    kinds: list[str] = []
    root.session.launch_interaction = _post_inst_stub(file, {"?c": "0::nat"}, kinds)
    runs = _count_operations(root.session, "RULE")
    root.session.age += 1
    await root.fill("1", [InferenceRule.gen_single({
        "thought": "apply sharedrule (residual ?c spans both derived subgoals)",
        "rule": {"name": "sharedrule"}})])
    print_header("After InferenceRule (?c instantiated across both subgoals)", file)
    root.print(0, file)
    await _assert_schematic_free(root, file, kinds)
    assert runs["n"] == 2, runs
```

预期值（C24 后 / 今天）：`Tactic2` 1 / 2；`Tactic4` 每次 1 / 2；`Tactic5` 1 与累计 3 / 2 与累计 5；`PostInstRuleShared` 2 / 3。**这些数是读代码推出来的，必须在首次运行时确认**（§8.6）。计数放在打印之后、只断言，所以四个 golden 逐字节不变。`Tactic5` 的第二个断言在两个 case 的收尾填入之前，收尾的两个 TACTIC 不计入。

### 8.6 红灯先行与变异检查

1. **红灯先行**（D24）：先只落 §8.4、§8.5、§8.7 的测试，在未改的 `model.py` 上跑：四个计数断言应在第一处失败并显示今天的值（`Tactic2` 为 2，`Tactic4` 第一次为 2，`Tactic5` 第一处为 2，`PostInstRuleShared` 为 3——每条断言以计数字典作 assert 的消息，失败时能看到实际值）；`PostInstRoundFailure` 应在"节点 FAILURE"处失败（今天节点 SUCCESS、3 次 TACTIC）；pytest 里除 `test_a_probed_node_executes_its_op_once` 与 `test_each_builder_packs_the_rounds_it_is_given` 外每一项失败。断言在 golden 比对之前，所以不会写出任何 golden。若某个计数与预测不同，停下来报 owner。再落 §4，四个测试通过（`Tactic2` 1；`Tactic4` 每次 1；`Tactic5` 1 与累计 3；`PostInstRuleShared` 2），golden 逐字节不变。实际看到的计数写进 C24 的 git 提交信息（§8.8 第 11 步）。
2. **单元测试的变异检查**（按记忆里的规则：变异作用于测试本身，每条被守护的性质一个变体）：在 `ai-artifacts/` 下写一次性的 pytest 插件（不进 git；用环境变量选变体），在内存里把 `SubgoalMaker._run_the_probe`（或相应的构造方法）换成变体，跑 §8.4 的文件，首次运行时确认每个变体让预测的那几项变红、把结果写进 C24 的 git 提交信息。变体里写 `super(SubgoalMaker, self)`，零参数 `super()` 在类体外会 `RuntimeError`。变体与预测（test 1–9 按 §8.4 的顺序）：
   - 旧行为（round k ≥ 1 失败时捕获并不带 rounds 重跑、节点成功；round 0 的 the convergence check 失败也捕获）：test 5、6 失败。
   - 某个 round 失败时 reset `dest`：test 5、6 失败（D7 的备选）。
   - the probe 的 round 用 `log=False`：test 3、5 失败（round 0 由基类执行、`log=True`，test 1、2 不受影响）。
   - 交互建在 `from_state` 上：test 3 失败。
   - 在 `_run_the_probe` 的 `while True:` 循环体第一行写 `self._post_insts = rounds`：test 5、6、7 失败。
   - 只执行最新的那个 round（`_beginning_opr_with_insts([rnd])`）：test 3 失败。
   - 从不做 the convergence check（round 0 后直接 `_post_insts = []`）：test 2、3、5、6、7 失败。
   - `CaseSplit` 的构造方法读 `self._post_insts` 而不是参数 `insts`：只有 test 9 失败。
   test 8 在每个变体下都通过；test 9 除最后一个变体外都通过。

### 8.7 注入故障的模型测试 `PostInstRoundFailure`（D13）

真实走 `StdBlock._refresh_the_beginning_opr`、`SubgoalMaker._refresh_the_beginning_opr` 与 `StdBlock._refresh_me_alone` 的失败头部路径，钉住 C24 的头号性质——round k ≥ 1 失败是节点如实的失败——而不只靠 §8.4 那个把待验证语义编进 `execute` 的假状态。用 `Tactic`（没有 autoconvert，`model.py:11137-11148`）。

- 夹具 `Tests/Test_PostInstRoundFailure.thy`：抄 `Test_Tactic5.thy` 的 `consts`、两条 sorry 的事实、lemma 与 `AoA_tactics` 声明，driver 名改为 `test.PostInstRoundFailure`；`by aoa` 在第 14 行（与 `Test_Tactic5.thy` 同形）。
- 注册 `@model_test("PostInstRoundFailure", "Test_PostInstRoundFailure.thy", 14, isolated_db=True)`（夹具声明了 `AoA_tactics`）。
- 正文：填第 1 步 `rule exI`；stub 交互答 `?x := 0`（答法同 `Tactic5`，但不向用例的 `file` 写任何东西——提示文字渲染进同一个用完即弃的 `MyIO`——否则会进 golden）；填第 2 步 `rule conjI` 之前，在用例自己的 session 上装一个 `on_operation_start`：数 TACTIC 的启动，第 2 个 TACTIC 启动时抛 `IsabelleError(["injected"], None)`（钩子在 `execute` 的 `try` 之外、RPC 之前被调用，`model.py:2021`，异常从 `_execute_opr` 穿出、由 `SubgoalMaker._refresh_the_beginning_opr` 转成节点失败；per-session，不需要恢复）。
- 断言：第 2 步的节点 status 为 FAILURE；`_post_insts is None`；窗口内恰好 2 次 TACTIC 启动（round 0 与被注入失败的 round 1）；`FailureReason.reason` 含 `injected`。`root.print` 与 quickview 渲染进一个用完即弃的 `MyIO(io.StringIO())`（走一遍打印路径但不进 golden），golden 只写一行 `status: FAILURE`。
- golden `Tests/PostInstRoundFailure.yml` 手写，内容恰为 `status: FAILURE` 加换行（`Tests/Tactic4.yml:23` 同格式；只断言的 golden 已有先例 `DeleteBreaksDependent.yml`、`CancelledNodeMayKeepLiveState.yml`）。owner 2026-10-11 批准夹具与这个 golden。
- 今天的代码上：第 2 个 TACTIC 启动是 round 1 的 scratch 执行，异常被 `:6894` 的 `except` 接住、`break`，循环后的那次执行（第 3 次启动）成功，节点 SUCCESS——红。

不加新机制就钉不住的：真实走 Isabelle、非注入的 round k ≥ 1 失败（只能由墙钟上限造成，会抖）；墙钟与 `total_isabelle_time` 的节省、`proof_oprs.yaml` 的内容（没有测试读它们；决定它们的执行次数已被 §8.4、§8.5 钉住，单元测试还钉住了每次执行都 `log=True`）；交互挂起时被深度重启或关闭打断、交互挂起时的并发读者（没有现成的测试设施）。

### 8.8 git 提交顺序与回归（D24）

**前提**：goal hints 那条线先把它自己的工作作 git 提交（它的 `model.py`、`test.py`、`Agent/agent_server.ML` 改动只能整文件进 git 提交，否则会被本线的 git 提交扫进去）；之后用它那次全量回归（2026-10-10 20:06–20:30，375/395，失败全为已知或环境所致、重跑通过）作基线，前提是从那以后没有别的代码变动（用 `find -newer` 核对）；否则先跑一次基线。本线用自己的 REPL 端口对（§8.3）。

**第一段：D21 与 D8**（不等 C24 的复审）
1. 改 D21 那一行（§4.10）；向 owner 请求 `env -u RPC_Host isabelle build -b Minilang_AoA`（约 20 s）的授权，请求里写明 §8.3 所述与三处 CLAUDE.md 的抵触及其证据，owner 明确同意后才跑；起本线的 REPL。这是全程唯一一次重建与重启，之后所有运行用同一个 REPL 进程。
2. 手改 D8（§4.9）与 `TACTIC_DESIGN.md` §13 第 17 条（§9.2）；跑 `pytest test_user_operations.py`。
3. 可选的快查：13 个打印 "derived goal" 的用例与 `Hint*` 用例用 `-f` 各跑一遍。
4. **第一次全量回归**。开始前记下开始时刻（第 9 步与第二次回归之后的 `find -newermt` 用它）和校验和（`git diff HEAD -- <已跟踪的待 git 提交路径>` 的 sha256）；开始时与每 10 分钟的检查都 `pgrep -af test_AoA.py`，有别的运行器在跑就暂停；结束后把每个 `Tests/*.diff` 与 `*.actual.yml` 拷进 `contrib/Isa-Mini/ai-artifacts/c24_regression_1/`（不进 git；运行器在下次跑同一用例时会删掉它们，`test.py:62-65`）。
5. 向 owner 报结果与两条 git 提交信息；owner 说「提交」后再核一次校验和，先读 `git diff HEAD -- <路径>`、把别的工作线的 hunk 在 git 提交信息里如实描述（Isa-Mini `CLAUDE.md:7`），然后 `git commit -- Agent/agent_server.ML`（D21；信息里写它的机制与重建 heap 的原因）、`git commit -- IsaMini/AoA/model.py IsaMini/AoA/docs/TACTIC_DESIGN.md`（D8）。两者之间不再改 `TACTIC_DESIGN.md`。

**第二段：C24**（复审通过、owner 批准实现之后）
6. 不碰 `model.py`，先写测试：§8.5 的计数、§8.4 的文件、§8.7 的用例与夹具、手写的 golden。新文件此时不暂存，第 11 步才 `git add`（显式路径；`IsaMini/AoA/CLAUDE.md:131` 禁的是不带路径的 add，owner 2026-10-11 确认）。从这一步起 `test.py` 里带着会在未改代码上失败的断言，直到第 11 步——这个窗口里别的 agent 的 git 提交若扫进 `test.py`，会在共享的 main 上留下失败的测试；第 11 步前的 `git diff HEAD` 检查能发现、不能阻止。
7. 在未改的 `model.py` 上跑 `-f 'Tactic2|Tactic4|Tactic5|PostInstRuleShared|PostInstRoundFailure'` 与 pytest：按 §8.6 第 1 条变红；计数与预测不符就停下来报。
8. 落 §4.1–§4.7，再跑同一批：变绿；跑 §8.6 第 2 条的变异检查。
9. 手改 `TACTIC_DESIGN.md`（§9.1、§9.2 第 14 条与第 18 条）与主仓库的 `AOA_SCHEMATIC_VARIABLE_PLAN.md`（§9.3）；用第 4 步记下的时刻跑 `find contrib/Isa-Mini contrib/Isabelle_RPC -newermt <时刻> -type f`，去掉本线自己的输出与 C24 自己的文件集，剩下的任何文件先报 owner，再决定翻转能否归给 C24；确认第 1 步之后没有 `.ML` 改动（有则重启再跑）。
10. **第二次全量回归**，校验和为 `git diff HEAD -- <已跟踪路径>` 的 sha256 加 `sha256sum <新文件>`，`pgrep` 与归档（`ai-artifacts/c24_regression_2/`）同第 4 步；回归之后再跑一次第 9 步的 `find -newermt`；既有 golden 必须逐字节不变，新 golden 与手写的一致（运行器只在 golden 不匹配时写 `.actual.yml`，`test.py:99-106`）。
11. 向 owner 报：测试在未改代码上与 C24 后的表现、变异结果、回归结果、git 提交信息；owner 说「提交」后：读 `git diff HEAD -- <路径>` 并在 git 提交信息里描述别的工作线的 hunk；写 D25 的 `BUG_DELETE_SKIPS_UPSTREAM_CHANGE.md`（主仓库根目录，untracked）；把本文搬进 `docs/archive/` 并按 §9.5 改；然后 `git add -- <三个新文件与归档的本文> && git commit -- <C24 的全部路径>`（`model.py`、`test.py`、`test_post_inst_probe.py`、夹具与 golden、`TACTIC_DESIGN.md`、`docs/archive/C24_PROBE_IN_DEST_DESIGN.md`）；git 提交信息里写红灯先行的实际计数与各变异变体的实际结果；最后主仓库 bump 一次子模块指针（`git add -f contrib/Isa-Mini`，先例 `5a2ab24e`）——C24 自己的 hash 只出现在这个 bump 的 git 提交里，Isa-Mini 树内没有任何文件写它。只推 origin，且只在被要求时。

**翻转怎么归因**：第一次回归对照基线：isolated-db 用例以 "served by another RPC host" 或 "needs an embedding model" 失败是环境问题，修环境重跑；新失败读它的 `.diff`——只碰 13 个 "derived goal" golden 里 derived goal 行的 hunk 是 D8 的，成为向 owner 的 golden 变更请求；其它 hunk 按排除法是 D21 的（不假定 D21 只能影响 `notice:` 行：别的回调也可能往缓冲里推别的消息）；仍含糊时手工去掉 D8 的几行（Python，不用重启）只重跑翻转的用例，绝不为归因回退 D21（要重建重启）；每个新翻转单独重跑一次排除抖动。第二次回归的任何翻转都是 C24 的，除非校验和或 `find -newermt` 显示别的 agent 改了代码——还剩一个看不见的缺口：别的 agent 对 C24 自己那几个文件的改动，只能在 git 提交前读 `git diff HEAD` 时发现；以 Timeout 或 `FACT_IN_TIME_FAIL` 翻转的按 D17。整个流程不用 stash/checkout/reset/revert；回归还可能翻转 golden 时不提交任何东西。

**预计**：两次全量回归各 25–40 分钟；一次重建、一次重启；两次五个用例的定向运行；向 owner 汇报 4 次。git 历史：goal hints → D21 → D8 → C24；单独 revert C24 在文本上是干净的（它的 `model.py` hunk——the probe 与构造方法在 `:10791` 之前，`Tactic`、`CaseSplit`、`Induction` 的构造方法在 `:11150` 之后——都不与 D8 的 `:10813-10836` 重叠；D21 在另一个文件；第 18 条只以第 17 条作上下文）。

---

## 9. 文档改动（手改，不用脚本；D15、D16 的逐字文本）

术语（D14）：两份宿主文档各用自己已有的词，本文的英文术语不进去。

| 概念 | 本文 | `TACTIC_DESIGN.md` | `AOA_SCHEMATIC_VARIABLE_PLAN.md` |
|---|---|---|---|
| the probe | the probe | 探测 | 探针 |
| `dest` | destination state / `dest` | 目标状态（`dest`） | 目标状态 `dest` |
| round | round | 探测轮次 / 第 k 轮 | 每轮 / 该轮 |
| instantiation rounds | instantiation rounds / `_post_insts` | 实例化轮次 | rounds |
| 节点保留的那次执行 | （描述句） | （描述句，不用"提交"） | （描述句，不用"提交"） |
| 首次刷新 / 再刷新 | 首次刷新 / 再刷新 | 首次刷新 / 再刷新（`:187` 已在用） | （不出现） |
| the convergence check | the convergence check | `_probe_residual_schematics` | 收敛判据（`:516` 已在用） |
| scratch state | scratch state | scratch（`:381` 已在用） | scratch（`:520` 已在用） |
| beginning op | beginning op | beginning op（代码库的通用词） | beginning op |
| 自动换成 Rewrite | `_autoconvert_to_rewrite` | `_autoconvert_to_rewrite` | （不出现） |
| 本工作的主人 | owner | owner（`:381` 已在用） | 用户 |
| C24 | C24 | C24（§13 第 14 条已定义） | 首次出现处写全：C24（`contrib/Isa-Mini/IsaMini/AoA/docs/TACTIC_DESIGN.md` §13 第 14、18 条） |

### 9.1 `IsaMini/AoA/docs/TACTIC_DESIGN.md` §6.1、§6.2

以下替换文字一律放在代码块里，以便逐字照抄。

**第 164 行**：保留开头到"结果等价，`InferenceRule` 的答案与 golden 不变；"为止，把其后的

```text
常见情形两次执行（scratch + 正式），只有 scratch 终态仍有 schematic 时才有第三次。
```

换成

```text
探测的每一轮都把 beginning op（连同已累积的实例化轮次）直接执行进节点自己的目标状态（`dest`），收敛那一轮的执行结果就是节点保留的结果：常见情形一次执行，k 个实例化轮次共 k+1 次；某一轮执行后 `dest` 仍有 schematic 变量时，该轮另加一次服务端预跑（C24，见 §13 第 18 条）。
```

**第 166 行**（docstring 规定）不改：其中"预跑终态"指服务端预跑，C24 不碰它。

**第 168 行**：在"`SubgoalMaker._execute_opr` 判 `self._probes_post_insts and self._post_insts is None`"之后插入括号（这一行记录的是 dd7707d 的改法，所以加注而不重写）：

```text
（C24 起，这个判断连同探测移入 `SubgoalMaker._refresh_the_beginning_opr`：在 `StdBlock._refresh_the_beginning_opr` 把 beginning op 执行进目标状态之后运行，那次执行就是探测的第 0 轮；见 §13 第 18 条）
```

**第 188 行**（§6.2 的 `beginning_opr` 一条）整条改为：

```text
- `_beginning_opr_with_insts(insts)`（`beginning_opr()` 由 `Tactic_Like` 定义为以 `self._post_insts` 调它；C24，见 §13 第 18 条）：任一 `IsabelleFact_Unfound` → `FailureReason`，用现有 "Fact … not found" 文案（硬失败）；否则 `Minilang_Operation.TACTIC(self.tactic_full, self.arguments, facts, insts, None)`——LIVE op 永远带 `NONE`。
```

### 9.2 `TACTIC_DESIGN.md` §13

第 14 条（`:381`）末尾追加"（已落地，见第 18 条）"。第 16 条（`:383`）之后、"状态："（`:385`）之前加两条。第 17 条随 D8 的 git 提交写入：

```text
17. **失败节点不显示 derived goal**（<日期>，单独的 git 提交，C24 的准备）：`Tactic_Like` 的两个 derived goal 打印辅助函数改为经 `_derived_goal()` 读目标，它只在节点 status 为 SUCCESS 且派生子目标不多于一个时返回 `self.goal()`。修掉再刷新失败后在 "Error:" 下显示旧 derived goal 的既有问题；也挡住 C24 会让首次刷新中失败的节点显示一个从来不是它结果的中间目标（探测挂起期间 `refresh`、API driver 的自动 compaction、深度重启后的新对话都会重新渲染树）。再刷新期间节点仍带着上一次的 SUCCESS，那个窗口与今天同类、不在此例内；`GoalNode` 的目标头部与删除节点时的存档行也不看 status，未改。golden 不变（全量回归 <日期>，与前一个 git 提交——`proof_opr` 装上 reporter 后清空消息缓冲——合跑）。
```

第 18 条随 C24 的 git 提交写入：

```text
18. **C24 落地**（第 14 条；owner 2026-10-10 采纳方向、2026-10-11 批准形状；单独的 git 提交；设计、owner 的逐项裁定与被驳回的评审意见（已归档）见 `IsaMini/AoA/docs/archive/C24_PROBE_IN_DEST_DESIGN.md`）：探测从 `SubgoalMaker._execute_opr` 移进 `SubgoalMaker._refresh_the_beginning_opr`（`StdBlock._refresh_the_beginning_opr` 成功返回之后调用 `SubgoalMaker._run_the_probe`），`SubgoalMaker` 不再覆写 `_execute_opr`；不再先跑 scratch。探测的第 0 轮就是 `StdBlock._refresh_the_beginning_opr` 把 beginning op 执行进节点自己的目标状态（`dest`）的那一次，此后每一轮把 `_beginning_opr_with_insts(rounds)` 执行进同一个 `dest`（`_probes_post_insts` 为 True 的四个类各自实现它、以参数接收实例化轮次；`beginning_opr()` 在 `Tactic_Like` 与 `CaseSplit_Like` 各定义一次、以 `self._post_insts` 调它；`SubgoalMaker` 的默认实现抛 `InternalError`；`Tactic.assembled_beginning_opr` 仍经 `_tactic_opr`）；整体扫描与 `Interaction_InstantiatePostSchematics` 读的都是 `dest`，`InferenceRule`/`Tactic` 的服务端预跑仍从执行前的状态重跑同一个带实例化轮次的 op；收敛那一轮的执行结果就是节点保留的结果，`_post_insts` 只在收敛处赋值；每一轮仍把已累积的实例化轮次真正作用到目标上，收敛机制不变。执行次数：常见情形 1 次（原 2 次），第 0 轮执行失败 1 次（原 2 次），k 个实例化轮次 k+1 次（原 k+2 次）；服务端预跑次数不变。任何一轮失败都是节点的失败：第 0 轮执行失败与原来相同，`dest` 不动；某一轮（含第 0 轮）的 `_probe_residual_schematics` 失败时，`dest` 留着该轮的执行结果；第 k ≥ 1 轮执行失败原先会不带实例化轮次重跑、节点报告成功而保留的 op 没经过 `_probe_residual_schematics`，现在节点失败，`dest` 留着最后一次成功执行的状态，不加 reset（再刷新时，与成功过的节点再刷新失败后留着旧状态是同一种情形；首次刷新时这是 C24 新引入的情形，其显示由第 17 条按节点的 status 门控）。第 k ≥ 1 轮的执行失败只能来自墙钟上限（RULE 8 s、CASE_SPLIT/INDUCT 10 s、TACTIC 的 `mini_single_cmd_timeout`、每轮 `INST_GOAL_VARS` 8 s、prove-in-time 搜索 10 s）；首次刷新中的 `InferenceRule` 在第 k ≥ 1 轮失败后进入既有的 `_autoconvert_to_rewrite`（与第 0 轮超时同一事件，不单独排除）。每一轮都写 `proof_oprs.yaml`（执行记录，失败时另有错误记录），`log=False` 只剩 `_rewrite_trial`。`Node._execute_opr` 与 `UserNode._execute_opr` 两处的 `dest` 收窄为非 `None`。既有 golden 全部逐字节不变（全量回归 <日期>）；新增单元测试 `test_post_inst_probe.py`（执行次数、第 k ≥ 1 轮失败、`_probe_residual_schematics` 失败、16 轮上限、四个类的 `_beginning_opr_with_insts`）、注入故障的模型测试 `PostInstRoundFailure`（只断言，golden 一行 `status: FAILURE`）；`Tactic2`、`Tactic4`、`Tactic5`、`PostInstRuleShared` 加执行计数断言（经 session 的 `on_operation_start`，不打印，golden 不变）。若有 golden 以 Timeout 或 FACT_IN_TIME_FAIL 翻转，先按"失去偶然的第二次运行"排查。未采纳的评审意见（裁判驳回）见归档设计 §11。
```

（若 D21 的 git 提交也要留记录，它属于 ML 侧的消息语义，不进 `TACTIC_DESIGN.md`；记在 git 提交信息里。）

### 9.3 `AOA_SCHEMATIC_VARIABLE_PLAN.md`（主仓库根目录；untracked，不进 git）

`:520-521` 原文：

```text
  实施为**双执行**——scratch 循环照旧 + M2 预跑查询：scratch 终态看不见 `CASE_SPLIT`
  未物化的 case，别无选择。
```

改为（这里的"双执行"指本轮的执行 + M2 预跑，C24 后对 `InferenceRule` 仍然成立）：

```text
  实施为**双执行**——探针循环照旧（C24（`contrib/Isa-Mini/IsaMini/AoA/docs/TACTIC_DESIGN.md` §13 第 14、18 条）起
  每轮直接执行进节点自己的目标状态 `dest`，不再另开 scratch）+ M2 预跑查询：执行后的 `dest` 看不见 `CASE_SPLIT`
  未物化的 case，别无选择。
```

`:522` 原文：

```text
- **`CASE_SPLIT` / `INDUCT`**：保留保守判据"scratch 终态无任何 schematic 变量"。
```

改为：

```text
- **`CASE_SPLIT` / `INDUCT`**：保留保守判据"该轮执行后的 `dest` 无任何 schematic 变量"。
```

`:526-527` 原文：

```text
**scratch 双执行的循环结构必须保留**——它是收敛的全部机制（每轮把已累积的 rounds
真正作用到目标上，好让下一轮看见还剩什么）。作废的那份计划正是在这里出的 blocker。
```

改为（粗体只把"scratch 双执行的"换成"探针的"；括号与 blocker 那句一字不动；末尾追加 C24 的事实，不写对 blocker 原因的推断）：

```text
**探针的循环结构必须保留**——它是收敛的全部机制（每轮把已累积的 rounds
真正作用到目标上，好让下一轮看见还剩什么）。作废的那份计划正是在这里出的 blocker。
C24（用户 2026-10-10 采纳方向、2026-10-11 批准形状）去掉的是一次性的 scratch 和循环之后那次重复的执行，
不是每轮的那一次执行：每轮把带着已累积 rounds 的 op 直接执行进节点自己的目标状态 `dest`；收敛判据先对 `dest`
查 `whole=True`，仍有 schematic 变量时 `InferenceRule`/`Tactic` 再对同一个带 rounds 的 op 做 M2 预跑；两者看到的
都是已累积的 rounds。收敛那一轮的执行结果就是节点保留的结果。
```

`:606`（T4 行）中的

```text
`CASE_SPLIT`/`INDUCT` 保留保守的"scratch 终态全消"判据
```

改为

```text
`CASE_SPLIT`/`INDUCT` 保留保守的"执行后的 `dest` 全消"判据
```

`:515`、`:838`、`:857`、`:880`、`:1043` 是带日期的历史记录或"原先"的描述，不动。

### 9.4 代码里的注释与 docstring

全文见 §4：`_probes_post_insts` 与 `_post_insts` 的注释（§4.7）；`Node._execute_opr` docstring（§4.5）；`SubgoalMaker._probe_residual_schematics` docstring（§4.3）；`_run_the_probe` docstring 与 `_beginning_opr_with_insts` 默认实现的注释（§4.1、§4.2）；`Tactic_Like` 覆写里的两处注释与闸门注释（§4.4）；`Interaction_InstantiatePostSchematics` docstring 的一处方法名（§4.5）；`proof_opr` 里的一行注释（§4.10）。`Tactic_Like` 的类 docstring 不改（§4.4 末段）。

### 9.5 本文归档时的改动（D23）

git 提交 C24 时（§8.8 第 11 步）：`mv ai-artifacts/C24_PROBE_IN_DEST_DESIGN.md IsaMini/AoA/docs/archive/`（文件未跟踪，`mv` 后在 git 提交的同一条命令里 `git add`）；状态行改为仓库现成的 ARCHIVED 头，照 `archive/D1_FIX_PLAN.md:3-5` 的格式——以符号为锚、不写任何 hash（那份先例也没有）：

```text
> **Status:** ARCHIVED — this design shipped. Historical record, no longer maintained;
> the code is the authority (`SubgoalMaker._run_the_probe`, `_beginning_opr_with_insts`,
> `test_post_inst_probe.py`, the `PostInstRoundFailure` model test); the current description
> is `TACTIC_DESIGN.md` §6.1 and §13 item 18.
> **Date:** 2026-10-11
```

第 4 行改为只说"行号是 dd7707d 的，用 `git -C contrib/Isa-Mini show dd7707d:<path>` 核对"（删掉关于工作树偏移的那句）；§0 的裁定列已是最终的；§11 已写全；§12 填一行；绝对路径（`/home/qiyuan/…`）改成相对主仓库根目录（§8.3 的解释器路径已是相对的）；§10 第 8 条指向 `BUG_DELETE_SKIPS_UPSTREAM_CHANGE.md`；§4 的代码与行号锚保留，作为被评审内容的冻结记录。交接文件 `ai-artifacts/C24_PROBE_IN_DEST_HANDOFF.md` 不进 git、留在盘上（它指向 `/tmp` 与 `~/.claude`，状态行已过时；它里面有用的命令已在 §8.3）。

---

## 10. 风险

1. **失去偶然的第二次运行**。今天一个冷运行失败的 op 仍可能在热的第二次运行里成功：任何接近自己墙钟上限的 op（§5.2 的时限清单）。round 0 的 scratch 运行失败后，循环后的那次执行再试一次，若成功就不经 the probe 直接保留（§3.4 第 3 条）。C24 去掉了这次机会，这正是目标 2 要的。按 D17 处理翻转；读代码排除不了，全量回归会说话。
2. 常见情形下 Tactic 记录的时间来自第一次运行（`model.py:11159-11163`），可能比今天的第二次运行更冷。记录偏高只会放宽重放封顶（`embedded_replay_limits`，`Agent/agent.ML:1152-1155`），方向是安全的。
3. 交互挂起期间（§5.7）、round k ≥ 1 失败后、某个 round 的 the convergence check 失败后、16 轮上限后，`dest` 里是一个从来不是节点结果的状态。首次刷新时唯一会把它显示出来的读者由 D8 按 status 门控；再刷新期间节点仍带旧的 SUCCESS，那个窗口的显示与今天同类；`GoalNode` 的目标头部与删除时的存档行不看 status，D8 不覆盖。
4. 首次刷新中的 `InferenceRule` 在 round k ≥ 1 失败后进入 `_autoconvert_to_rewrite`（`model.py:10906-10915`），可能把一条作为规则本可用的规则换成 Rewrite，agent 的 k 个答案随被替换的节点一起丢弃，旧节点 `dest` 的 ML 条目不会被 reset。只经墙钟上限可达、只对 Presented 的规则（D18）。
5. 交互期间的检索：再刷新时，`query` 的 `context_at` 若指向正在运行 the probe 的节点（它还带着上次的 SUCCESS）或任何解析到 `dest` 这个对象的位置，现在解析到当前 round 的状态而不是旧状态。golden 看不到，语义上更好，但确是一个行为差异。
6. 留给记忆的不变式（§5.9）：将来有人让 `_probes_post_insts` 为 True 的类推进会话共享的计数器、在构造方法里读 `self._post_insts`、让 `Tactic.assembled_beginning_opr` 绕过 `_tactic_opr`、在子类里覆写 `beginning_opr`、在 `SubgoalMaker` 与 `StdBlock` 之间插 `_refresh_the_beginning_opr` 覆写，C24 的前提就被破坏；今天都不存在。
7. 失败节点的 `dest` 已初始化时占着 ML 状态表里的一个条目；若该节点随后被丢弃（autoconvert 换掉、删除），条目泄漏。与今天任何带活状态被丢弃的节点相同；节点留在树里时，其 `_cancel` 或下一次刷新会回收它。总体上 the probe 分配的状态变少了：不再每个 round 调 `assign_name()`。
8. **既有缺口，与 C24 无关，记为独立 bug（D25）**：删除一个节点只重刷它后面的兄弟，不调 `_on_upstream_change`（`delete`/`_delete_me`/`_delete_child`，`model.py:5174-5182`、`:5223-5237`、`:5846-5851`；只有 insert `:5730` 与 amend `:5869` 调它）。所以一个已收敛的、`_probes_post_insts` 为 True 的节点在前面的兄弟被删除后，会带着按旧目标算出的 instantiation rounds 重跑、不再探测。C24 前后相同。维护记录是主仓库根目录的 `BUG_DELETE_SKIPS_UPSTREAM_CHANGE.md`（D25，git 提交 C24 前写）；本条只是冻结的记述。
9. D21 会丢掉其它回调留下的残留消息；若某个 golden 今天恰好显示这种残留，第一次回归会翻转，按 §8.8 归因后报 owner（那是修复，但 golden 仍需 owner 逐个批准）。

---

## 11. 评审中被驳回的意见（裁判的理由，供后续会话不再重提）

两轮对抗评审（2026-10-10）的裁判驳回：

- **C4 的核心子主张**（D16 与 D20 暗中耦合，应向 owner 提供"`:526` 只删 scratch"的选项）：`:526` 管四个类的 the probe 循环，`CaseSplit_Like` 从不做服务端预跑，它的判据只有整体扫描（`model.py:6856-6868`），所以 C24 后在 `:526` 保留"双执行"对它为假，无论取哪个意思；"探针的"是精确措辞而不是放松保护。R1 每轮仍有一次真实执行，不触及 `:526` 的含义。C4 的两处真实缺陷（误引、R1 的编造历史）已修。
- **C8 里 documentation 路的改法**（"C24 后中断变成普通的节点失败、刷新随后在已关闭的连接上取消子节点"）：AoA 运行里中断是 `CancelledError`（`model.py:80-104`，`toplevel.py:192-193`），`except IsabelleError` 接不住，不会记 `FailureReason`、不会取消子节点；这个改法以假换假。只采纳 skeptic 路的改法（§3.4 第 4 条）。
- **C11 里的 `SessionQuit` 假状态测试作为必需项**：`SessionQuit` 的传播 C24 前后相同（今天 `launch_interaction` 在没有 `except` 的 `try/finally` 里，新代码没有 `except`）；C24 唯一改变的中止行为（`dest` 留着 round 0 的状态）已由 test 5 钉住。可以加，不必须。
- **C13 的两个过度主张**（钩子让 D2 消失、让 §5.8 新获安全）：钩子仍收到闸门检查过的 op，round 0 用它还是重建的选择仍在；§5.8 的保证本来就从唯一的正常返回推出，再执行只在 `super()` 返回 `None` 之后。`Leaf` 不在同一继承树上，从未有风险。真正的收益——把"只有 beginning op 进 the probe"从记忆变成形状——由 D22 以不加接口的方式实现。
- **C5 的选项 (b)**（把英文术语作为同义词加进宿主文档的术语表）：`AOA_SCHEMATIC_VARIABLE_PLAN.md:38` 明文"不引入其它同义词"；写一条"X 等于 Y"是把术语缺陷变成被认可的缺陷。
- **C3 里"按代码阅读列出慢 RULE/CASE_SPLIT/INDUCT golden 的监视名单"**：哪些步接近墙钟上限不在回归机器上测量就不知道；读代码列的名单是把猜测当事实。一般规则（任何 Timeout 或 `FACT_IN_TIME_FAIL` 翻转先按 §10 第 1 条看）覆盖全部而不假装知道是哪些。
- **C16 里"若 D8 先 git 提交则第 17 条的引用断裂"**：按第一稿隐含的方案引用不会断；真正的缺陷（方案没写明、而且是较弱的安排）已按 C16 修（D8 自带第 17 条，C24 为第 18 条）。

四个 agent team（2026-10-11）否决的候选，各一句决定性理由：

- the probe 位置：评审 C13 的专用入口 `StdBlock._execute_beginning_opr`（现成的覆写点已有它要划的范围；基类实现与 `CaseSplit_Like` 再执行那一行逐字相同而那一行不能走它）；维持 `_execute_opr` 覆写并加 `assert opr == …`（按 op 的值识别调用方；`AssertionError` 不被接住、崩掉整个刷新）；在 the probe 的触发条件里加 `opr == self.beginning_opr()`（外来 op 会静默跳过 the probe，又回到按 op 的值触发）；删除 `_execute_opr` 这个入口（`UserNode` 对 Leaf 的"至多一个子目标"规则要在 `Leaf._refresh_me_alone` 的 `try` 里抛，`test_user_operations.py:242-245`、`USER_OPERATIONS.md:432`，去掉入口只是换成一个 Leaf 钩子）；footer 直接调 `execute`（其余调用方的 `from_state` 变成不变的参数，且绕过了本节点自己的 op 的入口）。
- op 的构造：`beginning_opr()` 的委托放在 `SubgoalMaker` 上（`SubgoalMaker.beginning_opr` 变具体，把 `SubgoalMaker` 排在 `UserNode` 前的插件类不再在导入时被拒，`helper.py:286`）；构造方法在两个基类上 `@abstractmethod`（`UserNode` 不定义它，排序正确的插件类会变成抽象类）；只在两个基类上声明、不在 `SubgoalMaker` 上（the probe 循环在 `SubgoalMaker` 上，会调一个它没声明的方法）；`beginning_opr` 加可选参数（`None` 已有两个意思，需要新哨兵；五个不探测的类与 `StdBlock` 的抽象签名都要改）；循环每轮先 `self._post_insts = rounds`（删除节点不触发 `_on_upstream_change`，失败留下的半截 rounds 会在之后的刷新里被当作已收敛；每个不收敛的出口都要 `except BaseException: reset; raise`，等于把存—设—恢复搬到每个 `await` 上）；往已构造的 op 里拼 rounds 或把 rounds 交给执行（`Minilang_Operation` 没有按槽替换的办法、`arg` 是 `Any`，TACTIC 的 rounds 在五个参数的第四个，要一张按命令的位置表，重复四个工厂与 ML 解包器）；永不退化的构造方法（`Tactic` 的失败检查要写两遍）。
- 设计文档的去处：留在 `ai-artifacts/` 提交；不提交并删掉链接；放 `docs/` 顶层；并入已跟踪文档而文件不提交（见 D23）。
- git 提交与回归：三次回归（基线已存在，归因读 diff 即可；C24 之后那次回归会在批准前自动记下新 golden）；代码后再写测试（golden 从 `.actual.yml` 批——运行器根本不会写它，直接写 `Tests/<name>.yml`，违反 golden 规则；注入故障的测试从未在旧代码上跑过）；D8 与 D21 合成一个 git 提交（失去分别 revert 的能力）；全部一个 git 提交；失败的测试单独一个 git 提交（在共享的 main 上留下测试失败的提交；它要的可复现证据改记在 C24 的 git 提交信息里）。

复审（2026-10-11）的裁判驳回：

- R3 里"beginning op 也是本文的词、宿主文档里该换掉"：它是代码库的通用词（`IsaMini/AoA/CLAUDE.md:21`、`:30`、`:32`，`DEVELOP.md:65`，`model.py` 约 19 处注释），`TACTIC_DESIGN.md` 没有与之竞争的词；换成描述句只会更长、不更正确。
- R13 辩护方"在宿主文本里保留'收敛检查'并在 §9 的表里声明"：给本文的英文术语声明一个中文替身等于认可一个造出来的词；宿主文档已用方法名 `_probe_residual_schematics` 指这个检查，就用它。
- R8 辩护方"在第 17 条里引用 D21 的 git 提交 hash"：要在第 5 步的两个 git 提交之间改 `TACTIC_DESIGN.md`，破坏第 4–5 步的校验和；也偏离 `D1_FIX_PLAN.md` 与 §13 第 1–16 条不写 hash 的先例。
- R5 里"用 HEAD + `git diff HEAD` + `git status --porcelain` 作指纹"：porcelain 只列未跟踪文件的名字、不哈希内容，看不见对未跟踪夹具的改动；而且是第三套机制，把现成的 `find -newer` 检查放宽覆盖更多。
- R15 里"把归档的 .md 改动也纳入校验和、为 §9.3 加回退说明"：校验和的用途是发现会让回归结果失效的代码改动，文档改动做不到这一点；§9.3 已声明计划未跟踪并逐字引了原文。
- R16 里"先重启 REPL、失败了再问"：失败已在会话记录里（2026-10-10 23:48）并由代码解释（`repl_tool.scala:103-110`），重演一遍只会回到同一个要问 owner 的问题。
- R9 里"给 `Tactic` 的构造方法加 `recorded_times` 参数、删掉 `_tactic_opr`"：为了让一句注释字面成立去改 D3 已批准的代码，防的是一个不存在的 `Tactic` 子类；改措辞就补上了同一个缺口。
- R12 里"维护记录必须放在 `TACTIC_DESIGN.md` §13 的'待办'段"：那一段是带日期的、关于 Tactic 夹具的 owner 原话；任何归档文件指向的维护记录都满足 owner"记为独立 bug"的裁定。
- R10 里"构造方法测试必须含 `InferenceRule` 一行"：RULE 已由 §8.4 的 test 1、3 钉住；必须加的是 `CaseSplit`、`Induction` 与 `Tactic` 的装配 op（本文仍把 `InferenceRule` 列进去，作为对照）。
- R17 里"推迟 `git add` 就关掉了'失败测试进 main'的风险"：言过其实——`test.py` 是已跟踪的，从第 6 步起就带着会失败的计数断言；推迟只是缩小窗口。
- R2 的"major"级别降为 minor：它只是把逐字文本改到与已批准的 §5.6、第 17 条一致的两处措辞，不改裁定、代码、测试或 golden；它自己提议的替换措辞还为"首次刷新"造了第三个说法。

---

## 12. 实施记录

已于 2026-10-18 落地，见 `TACTIC_DESIGN.md` §13 第 19 条（第 18 条已于 2026-10-14 被白名单的 ML 入口占用，所以本文冻结正文里的"第 18 条"都指第 19 条）；红灯先行的实际计数、变异检查与代码对抗评审的结果记在 C24 的 git 提交信息里。
