# 设计文档：AoA 的 `Tactic` 系统操作（施加白名单内的 Isabelle proof tactic）

> 状态：第七稿。第六稿吸收四轮对抗评审（22 + 18 + 17 + 12 条）、三位复核读者的意见与 owner 的全部裁定，第四轮裁判判定"达到开工条件（附条件）"，条件已全部落实；owner 2026-10-10 批准开工后按本文实现，实现中与原文不同的几处记在 §13，正文已同步改正。
> 基线：user operation 插件系统提交（`62f6b89`）之后的工作树。
> 术语：`Tactic` = 操作名；`TACTIC` = ML 构造函数；agent 可见文本一律说 tactic（Isabelle 自己叫 proof method，引用其 API 时保留原名）；**白名单** = `AoA_tactics` 声明的全部条目；**query 条目 / prompt 条目** = 白名单按 `shown_in` 分成的两半；**interpretation** = 声明里为每个 tactic 写的一句英文说明；**agent 可见名** = 经 `Name_Space.extern_shortest`（辅助函数 `agent_method_name`）得到的、能解析回全名的最短名（`simp`），agent 看到的一律是它的 Unicode 显示形式，agent 写来的两种记法都接受（§5.1）；**全名** = `Method.check_name` 得到的名字空间内部名（`HOL.simp`）；**常驻操作** = 基础 `cc_edit.jsonc` 里有 `$defs` 条目的系统操作；**白名单顺序** = 按 agent 可见名排序。
> 引用以符号名为主；行号指工作树当前状态，会漂移。

---

## 0. 审批状态（务必先看）

| 项 | 裁定 | 出处 |
|---|---|---|
| 操作名 / 字段 | `Tactic`；字段 `tactic`（**枚举**，值 = 本次调用白名单内全部 agent 可见名）、`arguments`（参数文本，可空）、`facts`、`thought`、`proofs` | owner 2026-10-08/09 |
| 白名单声明 | `declare [[AoA_tactics add: simp ‹rewrite the goal with the simplifier› induction ‹prove by induction on a variable› shown_in: prompt]]`；模式 `add:`/`del:`，省略即 `add:`；条目 = `name ‹interpretation›`，interpretation **必填且必须是 cartouche**；`shown_in: prompt \| query` 是**单个条目**的可选后缀，只作用于紧前面那个条目（例中 `simp` 为 query、`induction` 为 prompt），省略即 `query`；同名以最后一次声明为准；默认空；**只是 theory data，声明时不做任何 RPC** | owner 2026-10-09/10 |
| 语义信息来源与 DB 同步 | 唯一来源是声明里的 interpretation。**每次 AoA 调用启动时**白名单随参数到 Python，Python 逐条与 Semantic DB 比对：记录已存在且文字相同则不写；否则写入（覆盖时清掉 `expr`，作废该键的向量，向量按 DB 的惰性缓存重嵌）。不做哈希预检。同步是调用里**独立的一步**，在 `Runtime` 构造与 `Context.unpack` 之后、`_ensure_semantic_db` 的空库提示之后、驱动分支之前；**同步失败即本次 AoA 调用失败**（异常原文可见） | owner 2026-10-10（第四轮 C1） |
| `aoa` 进白名单 | 不处理：声明者的责任 | owner 2026-10-09 |
| 启用 | **白名单非空 ⟺ `Tactic` 在本次调用的操作表与 schema 里**；没有单独开关；ML 始终支持 `TACTIC`；`Tactic` 永不是 user operation 选择项 | owner 2026-10-08/09 |
| 白名单检查 | 在 Python 的 `Tactic.gen_single` 查表，**所有驱动**都经过；枚举只是能做 schema 校验的路径上的提前拒绝；ML 不查（REPLAY 必须接受任何已录得的 `TACTIC`） | 第二轮 C1 |
| 名字 | AoA 自己生成的文本（schema 枚举、prompt 段落、query 显示、节点打印、自己的报错）一律用 agent 可见名；Isabelle 原话例外（§10）；操作流与重放 blob 携带全名 | 第二轮 C2；owner 2026-10-10 收窄（代码评审 C27） |
| ML 执行 / oracle | agent 只能经白名单里**参数为 ML**（`tactic`、`raw_tactic`）或**参数含 method 文本**（Pure `subproofs`、`use … in`，Eisbach `match`/`all`/`determ`/`changed`/`fails`/`succeeds`/`catch`/`timeit` 及带 `methods` 参数的 Eisbach method）的 method 触及 ML；放不放是声明者的责任。不做扫描、不做 oracle 白名单、不加警告文字 | owner 2026-10-09 |
| chained facts | 任一事实找不到 → 这一步硬失败（"Fact … not found"），不像 `Obvious` 那样丢弃并警告 | owner 2026-10-09 |
| 超时 | `mini_single_cmd_timeout`（默认 15 s）在 LIVE 与无记录的 REPLAY 生效；保留实况耗时记录，带记录的 REPLAY **只**受 `embedded_replay_limits` 封顶（与 HAMMER 的缓存证明相同，内层限时不叠加） | owner 2026-10-09；2026-10-10 放宽（代码评审 C6） |
| 计时消息 / 文案 | `TACTIC_TIMES`，标签 22；重放超限文案 `Tactic replay timed out` | owner 2026-10-09 |
| 探测短路 | `Tactic_Like._probe_residual_schematics` 先做基类的只读整体扫描，无 schematic 即收敛 | owner 2026-10-09 |
| schematic 目标 | 允许；收敛条件"只有被 ≥2 个派生子目标共享的变量才实例化"，与 `InferenceRule` 共用基类 `Tactic_Like` | owner |
| prompt 段落 | 草案 B（§7.3）；按白名单顺序逐条渲染；接在 **system prompt 末尾**；无 system prompt 时接在 **initial prompt 末尾**（task 给出的整段 initial prompt 之后）；对自写 system prompt 的 task 同样附加；**交互 fork 收到发起方的 system prompt，段落随之可见** | owner 2026-10-10 定为交互 fork 不显示；2026-10-16 改为统一到发起方（`Session.system_prompt` 向 `parent` 委托） |
| query 工具 | kind `"proof tactic"` 只在白名单含 query 条目时出现（白名单只有 prompt 条目时不出现，见 §7.4）；**排序检索**的候选集 = query 条目；**`exact_name`** 在**整个白名单**里查，不在即 Undefined；**显示的 interpretation 一律来自白名单**，DB 只提供排序向量 | owner 2026-10-10；第四轮 C5 |
| 覆盖已有记录 | `Main` 之外的 method 已有流水线记录时，同步写入清掉其 `expr`，其它字段（如 `position`）保留 | owner 2026-10-10 |
| 非法 kind 标签 | 沿用各查询路径现有行为（直接路径报 "Invalid entity kind" 警告，fork 过滤路径静默丢弃），不改 fork 路径 | owner 2026-10-10（第四轮 C7） |
| 改名范围 | "proof tactic" 只出现在 agent 可见接口；内部一律 "proof method" | owner 2026-10-09 |
| Codex driver | 不在支持范围 | owner 2026-10-09 |
| `Agent_Hint` 盲区 | 接受：`arguments` 内的名字不过 hint 检查 | owner |
| 测试 | 凡夹具里声明了 `AoA_tactics` 的**模型测试**一律在一次性 Semantic DB 上运行；ML theory 测试不碰 DB，无需夹具 | 第三轮 C6，第四轮 C11 |

---

## 1. 执行摘要

内核侧已经做完：`Minilang.APPLY''`（`library/proof.ML`）接收一个 `Method.text`、`using` 事实与超时，把 method 作用在当前目标上，经 `Goals` 消息报告新子目标。本设计给 AoA 加一个系统操作 `Tactic`：agent 从白名单里选一个 tactic、给出参数文本与 chained facts；ML 侧把全名和参数组装成 `Token.src`，直接交 `Method.evaluate_runtime` 求值。`proof.ML` 一行不动。

与 `InferenceRule`（`RULE`）同形：同一个 `raw_apply`、同样发 `Goals`、新子目标留在同一 frame。`Tactic` 与 `InferenceRule` 共用新基类 `Tactic_Like`。

运行例子：theory 里 `declare [[AoA_tactics add: induction ‹prove by induction on a variable› shown_in: prompt simp ‹rewrite the goal with the simplifier›]]`。目标 `rev (rev xs) = xs`，agent 写 `Tactic{tactic:"induction", arguments:"xs"}`，ML 报 `Goals [base, step]`，节点下开两个子目标节点；各子目标写 `Tactic{tactic:"simp"}`，`Goals []`，目标关闭。操作流里记录的是 `HOL.induction`、`HOL.simp`。

---

## 2. 实测结论（脚本与原始输出在 `ai-artifacts/`，不提交）

**2.1 兄弟子目标（`tactic_restrict_probe/`，2026-10-07）。** Minilang 用 `protect_goals` 把除第一个之外的子目标嵌进**结论**（`x + 0 = x ⟹ Minilang.GOAL (1 + 1 = 2 ⟹ …)`），`Thm.nprems_of st = 1`，method 看不到兄弟。`auto`、`simp_all`、`force`、`clarsimp`、`simp`、`fastforce`、`linarith`、`(rule refl)`、加 `GOAL_def` 的 `simp`/`simp_all`：兄弟一律不动，`Goals` 长度与实际新子目标数一致，`raw_apply` 的 `n_new` 从未为负；新子目标落在最前面。`Goal.restrict` 包装与裸版逐项相同——**不加**。唯一能改到兄弟的情形是 schematic 变量跨子目标共享，由 post-instantiation 机制负责。

**2.2 method 文本里的 ML（`tactic_ml_method_probe/`，2026-10-09）。** Pure 的 `tactic`/`raw_tactic` method 编译并运行其参数里的 ML：走 `Method.read_closure_input` 时在读取阶段就运行，嵌套的 `subproofs ‹tactic ‹…››`、`use … in ‹…›` 同样；走无闭包的 `Method.read` 时延后到求值；`OS.Process.system` 真的写出了文件。源码清查：`src/Pure` 与 `src/HOL` 内，method 文本编译用户 ML 的途径只有这两个 method。结论见 §0"ML 执行 / oracle"行。

**2.3 Semantic DB 对 method 的覆盖（第三轮评审核实）。** `Main` 及其祖先 theory 里声明的 method（`simp`、`auto`、`induction`、`rule`……）被刻意排除在索引之外（`infra_filter.ML` `is_infra_method`；`semantic_store.ML` 的 `method_entries`），method 枚举回调也以此过滤；AoA 的 `retrieve_entity` 原本没有 METHOD 一支。所以这些 tactic 的语义只能来自白名单（§7.2 的同步）。METHOD 记录没有门控字段（`semantics.py` 的 `Record` 注释），解释流水线不会改写已有 interpretation 的 METHOD 记录。

---

## 3. 语义

`Tactic` = 对当前目标（frame 的 subgoal 1）施加白名单内的一个 proof method，带可选的 chained facts 与参数文本，受 `mini_single_cmd_timeout` 限时；留下的子目标成为待证目标。失败即 `OPR_FAIL (PROOF_FAIL, …)`，agent 看到 Isabelle 原话。

白名单同时回答三个问题：agent 能用什么（枚举 + 解析时查表）、agent 怎么知道（prompt 或 query）、agent 看见什么（interpretation）。白名单为空时 `Tactic` 不存在。

---

## 4. 内核改动

**无。** `Minilang.APPLY''`、`raw_apply`、`protect_goals`、`mini_single_cmd_timeout` 原样复用。

---

## 5. agent 层接线（ML）

### 5.1 白名单声明（`Agent/agent_server.ML`，放在 `AoA_enable_read_memory` 旁）

- **数据**：`Generic_Data`，`Symtab` 从**全名**到 `{interpretation : string, in_prompt : bool}`；合并取并集，同名右侧优先。**纯 theory data，声明时不碰 Python。**
- **解析器**（照 `simproc_att`，`Pure/simplifier.ML`）：
  ```sml
  val mode = Args.del -- Args.colon >> K false || Scan.optional (Args.add -- Args.colon >> K true) true
  val add_entry =
    Parse.name_position -- Parse.cartouche
    -- Scan.optional (Args.$$$ "shown_in" -- Args.colon |-- (Args.$$$ "prompt" >> K true || Args.$$$ "query" >> K false)) false
  val del_entry = Parse.name_position
  val tactics_att =
    (Args.context -- Scan.lift mode) :|-- (fn (ctxt, is_add) =>
      Scan.repeat1 (Scan.lift (if is_add then add_entry >> … else del_entry >> …)))
    >> (fn decls => Thm.declaration_attribute (fn _ => fold … decls))
  ```
  名字经 `Method.check_name ctxt (name, pos)` 解析成全名，拼错在 `declare` 处定位到该名字报错；interpretation 必须是 cartouche，漏写就是解析错误（`Parse.embedded` 会把下一个名字当 interpretation，故不用）；interpretation 原文存储，归一化在 Python 侧一处完成（§7.2）。
- **导出** `tactics_of : Proof.context -> tactic_entry list`，每条记录 `{name, full, interpretation, in_prompt, key}`（agent 可见名、全名、interpretation、in_prompt、universal key）：agent 可见名 = `Name_Space.extern_shortest`（辅助函数 `agent_method_name`：能解析回全名的最短名。普通的 `extern` 会因 Pure 与 HOL 各声明了一个 `simp` 而给出 `HOL.simp`，虽然 `simp` 本就解析到 `HOL.simp`——实测 2026-10-10），universal key = `Universal_Key.key_of_method`，都在 **`IsaMini.AoA` 调用的 context** 里计算；按白名单顺序。`retrieve_entity` 的 METHOD 分支显示的名字用同一个辅助函数。ML 发出的 agent 可见名是 Isabelle 的 ASCII 记法（如 `\<phi>safe_simp`）；Python 侧把它装进 `IsaTerm`（`TacticEntry.name`）：`.ascii` 是白名单的键，agent 看到的（enum、prompt 段落、节点打印、拒绝文案、`query` 的显示）一律是 `.unicode`（`φsafe_simp`）；agent 写来的名字（`Tactic.gen_single`、`exact_name`）先经 `ascii_of_unicode` 再查表，两种记法都接受——与其它所有实体名在边界上的处理相同（owner 2026-10-10 裁定）。注意 universal key 在 ML 进程内按（实体, theory 名）缓存（`Universal_Key.ML` `cached_key`），theory 尚在处理中时算出的 WIP 键要到下一个 ML 进程才换成最终键；同步、流水线、检索读的是同一份缓存，所以不会不一致。**实现不得绕过这个缓存。**
- **ML 入口**（2026-10-14）`add_tactics : (xstring * {interpretation, in_prompt}) list -> Context.generic -> Context.generic`：给手里拿着 context 这个 ML 值、而不是在写 theory 的调用方——TAT 的 `Define` job，它为一次 AoA 调用在 goal 的 proof context 上声明白名单。每项的名字经同一个 `Method.check_name` 解析成全名（拼错同样报 Undefined method），同名后写的覆盖先写的，与声明一致；`add_entry` 与它共用 `add_tactic` 这一步。

### 5.2 `Agent/agent.ML`

1. **构造函数**（datatype 两份都加，`USER` 旁）：

   ```sml
   | TACTIC of string                              (*tactic: full method name*)
            * string                              (*arguments, as written after the name in Isar*)
            * ('term, 'fact) extended_fact list   (*chained facts (Isar `using`)*)
            * (string * string) list list         (*post-rule schematic instantiation rounds, as RULE*)
            * Phi_Proof_Store.times option        (*standard-machine times of the live run; NONE until assembled*)
   ```

2. **`check_command_i`**：`TACTIC (name, args, facts, insts, recorded) => TACTIC (name, args, map (check_extended_fact s ctxt) facts, insts, recorded)`。不查白名单：Python 在解析入口对所有驱动检查（§6.2），REPLAY 必须接受任何已录得的 `TACTIC`。**接受的盲区**：`arguments` 内的事实名与项由 Isabelle 的参数解析器消化，不经 `Agent_Hint`；原因是覆盖不全（Isabelle 给 token 标了 Fact/Term 值，但 `of`/`where`/`rule_tac` 的字符串参数晚读），不是"猜名字会误判"。只写代码注释。

3. **参数词法**：`read_method_text` 本来就把切词（`Parse.read_embedded ctxt (Keyword.no_major_keywords (Thy_Header.get_keywords' ctxt)) (Scan.many Token.not_eof) input`）与读 method 表达式（`Method.parser 0`）分成两步，所以抽出的辅助函数 `lex_embedded ctxt input` 只做切词、不带解析器参数，两处共用；`TACTIC` 只切词，不读 method 表达式。用严格词法器而不是 `Token.explode`；词法错误（"Outer lexical error: …"）经 `proof_opr` 的 `ERROR` 分支原话到达 agent。

4. **`interpret_i`**，照 `RULE` 分支复用 `with_resolved_refs`，照 `HAMMER` 分支复用计时与封顶：

   ```sml
   | TACTIC (name, args, facts, insts, recorded) =>
       with_resolved_refs exec_mode s facts (fn s' => fn refs =>
         let val ctxt = Minilang.context_of s'
             val toks = lex_embedded ctxt (Input.string args)
             val text = Method.Source (Token.make_src (name, Position.none) toks)
             val timeout = Config.get ctxt Minilang.mini_single_cmd_timeout |> Time.fromMilliseconds
             fun run limit () = Minilang.APPLY'' limit refs text s'
             val s'' =
               case (recorded, exec_mode) of
                 (SOME times, REPLAY) =>
                   (Thread_CPU.apply (embedded_replay_limits times) (run NONE) ()
                    handle Timeout.TIMEOUT _ =>
                      raise Minilang.OPR_FAIL (Minilang.PROOF_FAIL, "Tactic replay timed out"))
               | _ =>
                   let val (time, s'') = Phi_Proof_Store.timing (run (SOME timeout)) ()
                       val _ = Minilang.get_reporter ()
                                 (Minilang.Internal (TACTIC_TIMES (Phi_Proof_Store.standard_time time)))
                   in s'' end
         in apply_post_insts insts s'' end)
   ```

   要点：
   - **不读 method 表达式**：没有组合子、没有嵌套文本；`Method.evaluate_runtime`（`APPLY''` 内部）对 `Source src` 自己做名字解析（接受全名）并调用该 method 的参数解析器，"Undefined method"/"Bad arguments for method …" 原话到达 agent。
   - **只计量 `APPLY''`**：事实先由 `with_resolved_refs` 解析（prove-in-time 的证明各有 `FACT_PRF` 记录与封顶，在 `Thread_CPU.apply` 之外），实例化在计时之外；写入点 `standard_time` 归一一次，与 `HAMMER_i` 同一纪律。
   - **记录值只在 REPLAY 生效**：LIVE 永远实跑并重新计量。
   - **封顶超限是裸 `Timeout.TIMEOUT`**（`Thread_CPU.apply` 以中断触发，穿过 `Minilang.apply`——它的处理器只接 TIMEOUT——到 `Thread_CPU.apply` 自己的栈帧里才变成 TIMEOUT），处理器直接套在 `Thread_CPU.apply` 表达式上。带记录的 REPLAY 不传内层限时（`run NONE`）：照 HAMMER 的 `try_cached_apply`，封顶包住整个操作，`APPLY''` 自己的限时只是墙钟、还会压过封顶的余量；其它运行传 `SOME mini_single_cmd_timeout`，超时变成 `OPR_FAIL (PROOF_FAIL, "Timeout")`。
   - 封顶公式（`cache_file.ML` `replay_limits_with`，`embedded_replay_limits = replay_limits_with 3s`）：线程 CPU 1.5 × 记录 CPU + 3 s，墙钟 2 × 记录墙钟 + 3 s，名义时间，`Thread_CPU.apply` 内乘本机 `timeout_scale`。

5. **新异常** `exception TACTIC_TIMES of Phi_Proof_Store.times`，放 `FACT_PRF` 旁。

### 5.3 `Agent/agent_packer.ML`

- 从 `pack_recorded_proof`/`unpack_recorded_proof` 抽出 `pack_times`/`unpack_times`（毫秒对 ↔ `times`，含单值回退），在 `MINILANG_AGENT` 签名里导出 `pack_times`（`pack_bindings` 旁），`SH_PRF`/`FACT_PRF`/`TACTIC_TIMES` 三处复用。
- `xcmd_unpacker`：`"TACTIC" => apfst TACTIC o unpackTuple5 (unpackString, unpackString, unpackList unpack_extended_fact, unpack_post_insts, unpackOption unpack_times)`；`xcmd_packer` 镜像。

### 5.4 `Agent/agent_server.ML`

- `pack_opt` 加一个 `Internal` 分支：`TACTIC_TIMES times => SOME (packPair (packInt, pack_times) (22, times))`，放在 user operation 的 21 号兜底分支**之前**。缺分支的后果是消息静默丢失，测试要断言它到达（§9）。
- `IsaMini.AoA` 的参数元组已是 `packTuple12`（mlmsgpack 上限）：把 `enable_write_memory`、`enable_read_memory` 嵌成一个 `packPair (packBool, packBool)`，腾出的槽位放白名单 `packList (packTuple5 (packString, packString, packString, packBool, Universal_Key.pack_universal_key))`（agent 可见名、全名、interpretation、in_prompt、universal key），按白名单顺序；`toplevel.py` 解包同步改。
- 本次调用的 user operation 名单**不**包含 `Tactic`；Python 按白名单自行把 `Tactic` 放进操作表（§7.2）。
- **method 枚举回调注册为空**：`raw_AoA` 的回调列表里用 `Context_Callbacks.make_methods_callback (SOME (K false)) au` 取代解构出来的 `methods`——AoA 调用里 method 名字空间不再贡献任何检索候选（它会过滤掉 `Main` 的 method、放出其它 method），候选只来自白名单（§7.4）；顺带使 `_get_definition_with_pos` 不会给 tactic 打印 `method_setup` 源码。
  - 2026-10-27 注：`_get_definition_with_pos` 已删除，实体的定义位置改由 `IsaMini.retrieve_entity` 按名字解析给出。tactic 不打印 `method_setup` 源码，现在由 `retrieval.py` 里 `_format_fetched_entity` 对 METHOD 的显式跳过保证，不再依赖这里的 method 枚举为空。
- **`retrieve_entity` 加 METHOD 一支**，照 `TypeK` 的写法：`(Universal_Key.MethodK, name) => (SOME (agent_method_name ctxt name, [], [], [], false), NONE)`（§5.1 的辅助函数）。

### 5.5 加载顺序

无新文件；`Minilang_AoA.thy` 不动；改 `.ML` 后重启 REPL。

---

## 6. `model.py` 节点建模

### 6.1 `Tactic_Like(SubgoalMaker)`：新基类，`InferenceRule` 与 `Tactic` 共用

从 `InferenceRule` **上提**：`can_operate_on_schematic_goal`（返回 `None`）、`_probe_residual_schematics`（共享计数 ≥ 2）、`_supplied_proofs` 的初始化，以及两者逐字相同的 `_beginning_opr_err_msgs`（头行文案是类属性 `_fail_header`）、`_child_refresh_failure_err_msgs`、`_title_of_children` 与 "derived goal" 的两个打印辅助函数（`_quickview_derived_goal`、`_print_derived_goal`）；`gen_single` **不**上提（它的工厂只适配 `InferenceRule` 的构造函数，`Tactic` 自己写）；`InferenceRule` 改为继承 `Tactic_Like`。`_probe_residual_schematics` 加一个前缀：先调 `super()._probe_residual_schematics`（只读的整体扫描）；两个映射都空即收敛返回；否则落入原有的服务端预跑。结果等价，`InferenceRule` 的答案与 golden 不变；探测的每一轮都把 beginning op（连同已累积的实例化轮次）直接执行进节点自己的目标状态（`dest`），收敛那一轮的执行结果就是节点保留的结果：常见情形一次执行，k 个实例化轮次共 k+1 次；某一轮执行后 `dest` 仍有 schematic 变量时，该轮另加一次服务端预跑（C24，见 §13 第 19 条）。

docstring 写性质："派生的子目标全部留在当前 frame 的终态里（`derived_subgoals_of` 的单帧形），因此探测可读预跑终态、只要求被两个以上子目标共享的变量实例化；开块形（`CaseSplit_Like`）的 `Goals` 消息发于实例化之前，不能用。"

**探测触发改为类属性**：`SubgoalMaker._probes_post_insts: ClassVar[bool] = False`，`Tactic_Like` 与 `CaseSplit_Like` 为 `True`，**`UserNode` 钉死为 `False`**（注释：`USER` 命令不带实例化轮次；插件类把 `UserNode` 列在最前，所以无论它选哪个基类都进不了探测）；`SubgoalMaker._execute_opr` 判 `self._probes_post_insts and self._post_insts is None`（C24 起，这个判断连同探测移入 `SubgoalMaker._refresh_the_beginning_opr`：在 `StdBlock._refresh_the_beginning_opr` 把 beginning op 执行进目标状态之后运行，那次执行就是探测的第 0 轮；见 §13 第 19 条）；删除 `_POST_INST_COMMANDS`，其注释移到属性上。

### 6.2 `Tactic` 节点

```python
class Tactic_ToolArg(TypedDict):
    thought: NotRequired[str]
    tactic: str                       # agent 可见名；schema 里是枚举
    arguments: NotRequired[str]
    facts: NotRequired[list[FactByName | FactByProposition]]
    proofs: NotRequired[list[raw_proof] | None]

@proof_operation("Tactic", Tactic_ToolArg)
class Tactic(Tactic_Like):
    construct_schema: ClassVar[dict] = …   # §7.1 的模板
```

- **白名单检查在 `Tactic.gen_single`**：`wanted = ascii_of_unicode(arg["tactic"])`（agent 的拼法两种记法都接受），`validate(Literal[tuple(各条目 name.unicode)], pretty_unicode(wanted), f"{path}.tactic")`，不在即现有的 Literal 文案、列的是 Unicode 名（例："`proof_operations[0] (Tactic).tactic` must be one of `induction` or `simp`"）；通过后以 `wanted` 从 `the_session().runtime.tactics` 取出**条目**，用 `_parse_positional_proofs` 解析 `proofs`，自己构造 `Parsed_Opr`（工厂把条目作为构造参数传给 `Tactic.__init__`：节点存 `name`（`IsaTerm`，打印用 `.unicode`）与全名，不再查表）。此检查在任何 Isabelle 调用之前、所有驱动都经过。不抽文案辅助函数。
- 字段：`tactic_full: str`（全名，进 op）、`tactic`（agent 可见名，用于显示）、`arguments`、`_raw_facts`、`fact_refs: list[IsabelleFact] | None`、`_post_insts`（继承）。没有 `_recorded_times` 字段。
- `_refresh_me_alone`：首次 `fetch_facts(self._raw_facts)`，结果每项都是 `IsabelleFact`（schema 与 `ToolArg` 不收描述型事实；描述型事实在 `Parse_Nodes` 的 `validate` 处被拒）；再刷新 `refresh_facts`；`await super()._refresh_me_alone(auto_intro)`；成功后 `_backfill_recorded_fact_proofs(self.fact_refs, self._state_after_beginning())`。
- `_beginning_opr_with_insts(insts)`（`beginning_opr()` 由 `Tactic_Like` 定义为以 `self._post_insts` 调它；C24，见 §13 第 19 条）：任一 `IsabelleFact_Unfound` → `FailureReason`，用现有 "Fact … not found" 文案（硬失败）；否则 `Minilang_Operation.TACTIC(self.tactic_full, self.arguments, facts, insts, None)`——LIVE op 永远带 `NONE`。
- **记录值只在装配时装入**（照 `Obvious`）：`StdBlock` 加钩子 `assembled_beginning_opr()`（默认返回 `beginning_opr()`），`StdBlock.assemble` 改调它（唯一消费者）；`Tactic` 覆写为从 `self._state_after_beginning().messages` 取最后一条 `Tactic_Times_Msg` 填入第五分量。
- `_beginning_opr_err_msgs`：照 `InferenceRule`——ML 已有 "Fail to apply the tactic" 头就不再加；附当前目标。
- `print`：`operation: Tactic` / `tactic: <agent 可见名>` / `arguments: <text>`（有则）/ `with facts:`；`quickview_title`：`Tactic (<agent 可见名> <arguments>)`。

### 6.3 `Minilang_Operation.TACTIC` 工厂

```python
@staticmethod
def TACTIC(tactic_full: str, arguments: str, fact_refs: 'list[IsabelleFact]',
           insts: 'list[list[tuple[str, xterm | xtyp]]] | None' = None,
           recorded_times: 'tuple[int, int] | None' = None) -> 'Minilang_Operation':
    return Minilang_Operation("TACTIC", (tactic_full, ascii_of_unicode(arguments), [r.pack() for r in fact_refs],
                                         _pack_post_insts(insts), recorded_times))
```

### 6.4 消息

`class Tactic_Times_Msg(Message)`（`times_ms: tuple[int, int]`，docstring 照 `SH_PRF_Msg`）；`unpack_message` 加 `case (22, (cpu_ms, wall_ms))`。

---

## 7. schema、文案、白名单的三个出口

### 7.1 `Tactic.construct_schema`（基础 `tools/cc_edit.jsonc` **不动**）

模板是类属性 `construct_schema`（与 `UserNode` 同名同义），导入时经与插件相同的注册检查（把 `proof_operation` 里的 schema 检查抽成带消息前缀的辅助函数，对 `Tactic` 也调一次）：

```jsonc
{
  "additionalProperties": false,
  "description": "apply an Isabelle proof tactic to the goal. Do not use this operation unless you are explicitly instructed or advised to.",
  "properties": {
    "operation": { "const": "Tactic", "type": "string" },
    "thought": { "$ref": "#/$defs/Thought" },
    "tactic": { "type": "string", "enum": [] },
    "arguments": {
      "type": "string",
      "description": "the tactic's arguments, written as they would follow its name in Isar; empty if none"
    },
    "facts": {
      "description": "facts chained into the tactic (as by `using` in Isar); instantiations and discharging premises can be helpful",
      "items": { "anyOf": [ { "$ref": "#/$defs/FactByName" }, { "$ref": "#/$defs/FactByProposition" } ] },
      "type": "array"
    },
    "proofs": { "$ref": "#/$defs/GivenLater" }
  },
  "required": [ "operation", "thought", "tactic" ],
  "type": "object"
}
```

类方法 `schema_for_call(runtime)` 定义在 `Node` 上，默认返回 `cls.construct_schema` 的深拷贝（只有非常驻类会被调用，它们都有该属性）；`Tactic` 覆写为把 `properties.tactic.enum` 填成白名单各条目 agent 可见名的 Unicode 形式（`name.unicode`，白名单顺序）。

### 7.2 按调用装配：`Runtime` 与 `activate_tactics`，DB 同步

- **常驻操作只定义一次**：`BUILTIN_OPERATIONS`（`model.py` 里冻结 `OPERATION_REGISTRY` 的那行）= 注册表减去 `Tactic`（按名字）：`MappingProxyType({n: m for n, m in OPERATION_REGISTRY.items() if n != "Tactic"})`；原有的双向导入期检查 `_check_builtins_advertised` 原样保留（`Tactic` 永远不可能有 `$defs` 条目——注册检查拒绝基础 schema 里已有的名字），不加断言；注释说明 `Tactic` 是唯一在基础 schema 之外的注册操作、由 `Runtime` 按调用放置。`test_user_operations.py` 里 `rt.operations == BUILTIN_OPERATIONS` 的断言仍成立；要改的注释是 `test_a_builtins_subclass_registered_later_is_not_a_builtin` 里"frozen when the last of them registered"那句。
- **构造**：`Runtime.__init__(self, user_operations=(), tactics=())`——照现有方式把 user operation 校验进 `_user_operations`（原序）、再调 `self.activate_tactics(tactics)`，于是白名单总是存在；不建任何表。`toplevel.py` 在解包白名单槽位后以 `Runtime(user_operation_names, tactics)` 构造。
- **`Runtime` 只存两个输入**：`_user_operations`（构造时校验、原序）与白名单（私有字段 `_tactics`，`tactics` 是它的只读视图 `MappingProxyType`，`activate_tactics(entries)` 是其**唯一**写入者；按 agent 可见名的 ASCII 记法索引、白名单顺序，值 `TacticEntry` 为（agent 可见名的 `IsaTerm`、全名、interpretation、in_prompt、universal key），interpretation 在此用 §7.2 末尾的归一化辅助函数处理一次）。`operations`（常驻操作 → `Tactic`（白名单非空时）→ user operation 原序）与 `tactics_by_full`（同一批值按全名的索引，供 §7.4 的显示覆盖）是由这两个输入**推导的只读属性**，顺序与"白名单非空 ⟺ `Tactic` 在表里"按构造成立，再次激活（如测试里）亦然。
- `_edit_schema_for(runtime)`（签名改为取 runtime，`_tool_schemas_for` 相应改）：对表里每个**非常驻**条目，把它的 `schema_for_call(runtime)` 放到 `$defs/<name>` 并追加 `{"$ref": "#/$defs/<name>"}`——与 user operation 同一两行，没有按类型的分支。
- 枚举只是能对工具参数做 schema 校验的路径（Claude Code 的 MCP 路径）上的提前拒绝；API 驱动直接执行工具调用不做校验，真正的检查是 §6.2 的 `validate`。四种驱动变体（Claude Code、Gemini、OpenAI、DeepSeek）是传入 schema 的纯函数，自动跟随。
- **DB 同步**：`semantics.py` 里只有 `Semantic_DB.declare_interpretation(key, text)`（`_Semantic_DB` 的方法，与 `update_expr`、`delete` 同列为写入者，`__setitem__` 的写入者名单里登记）；`toplevel.py` 在原位对 `runtime.tactics` 的值逐条调用它（三行循环；不在 Semantic_Embedding 子模块里放 AoA 命名的包装函数）。`IsaMini_AoA` 的顺序：构造 `Runtime` → 算 `is_test_driver`（纯字符串判断）→ 非 test driver 时先调 `_ensure_semantic_db`（它靠"库是否为空"决定要不要提示安装预建 DB，必须在同步写入之前读到空库，否则没装 DB 的机器永远看不到提示）→ **同步，独立一步、不包 try：失败即本次调用失败**，异常原文可见 → 其余按原样。`declare_interpretation`：先归一化文字；从 key 用 `destruct_key` 取 kind 与全名，非 METHOD 键即抛错；在一个写事务里 `_raw_for_update` 取现有记录，若存在且 interpretation 与归一化文字相同则**不写不作废**；否则 `invalidate_vectors([key])`，再 `_put_fields(key, {kind: METHOD, name: 全名, expr: None, interpretation: 归一化文字}, create=True)`——新建与覆盖传同一个字典，覆盖时保留记录的全部其它字段（流水线写的 METHOD 记录带 `position`；门控字段对 method 恒为 `None`）。写入发生在 AoA gate 之后，批量 build 从不碰 DB；用户层 DB 按需创建，不依赖是否装了预建 DB。**后调用者生效。** 同步在 `update_interpretations` 之前的好处：流水线对已有 interpretation 的 METHOD 记录不会再付费调 LLM。
- **归一化辅助函数**（`semantics.py`，`declare_interpretation` 旁）：`' '.join(pretty_unicode(s).split())`——`\<…>` 转 Unicode、换行变空格、连续空格压一；`activate_tactics` 与 `declare_interpretation` 共用（后者对已归一化的输入是幂等的），DB 与 prompt 的文字逐字节相同。

### 7.3 prompt 段落（草案 B，owner 已定）

一个 `Session` 辅助函数 `_tactic_prompt_block()`（照 `_lemma_guidance` 的样子）从 `Runtime.tactics` 按白名单顺序渲染 prompt 条目，自带门控：无 prompt 条目时返回空串，否则自带前导换行。交互 fork 没有自己的 system prompt：driver 发给它的是发起方的；它自己的 `Session.system_prompt()` 向 `parent` 委托、返回同一份（在 ClaudeCode 和 API driver 不带上下文模式下，由它再起的 fork 收到的就是这份）；段落随之可见。**只在两个分发点调用**：`Session.system_prompt()`（`sp = await self.task.system_prompt(role, self); return sp if sp is None else sp + block`）和 `_compute_initial_prompt`（`text = await self.task.initial_prompt(role, self, sp is not None); return text if sp is not None else text + block`——在 task 给出的整段 initial prompt **之后**）。于是对任何 task——包括自写整段 system prompt 的插件 task——段落恰好出现在两者之一的末尾；驱动若自行覆盖 prompt 则绕过（已知并接受）。

```
You may use the `Tactic` operation with these tactics:
- induction: prove by induction on a variable
- simp: rewrite the goal with the simplifier
```

（示例对应两个条目都带 `shown_in: prompt` 的声明，按白名单顺序。）

### 7.4 `query` 工具里的 "proof tactic"

- 基础 `cc_semantic_search*.jsonc` **不含** `"proof tactic"`。`_tool_schemas_for` 在 read-memory 门控之后、仅当 `Runtime.tactics` 有 query 条目时，把它追加进 `query` schema 的 `kinds` 枚举（`retrieval.py` 里 `_without_enum_value` 的加法对偶，重建而非改写）。白名单只有 prompt 条目时该 kind 不出现：这些 tactic 的 interpretation 已在 prompt 里，agent 无需再查；不校验 schema 的驱动若仍送来该标签，按下面的规则处理。
- **标签**：`retrieval.py` 里一个函数取代两处 `EntityKind.from_label` 调用（直接查询与 fork 过滤路径），把 `"proof tactic"` 映射到 METHOD，任何其它解析到 METHOD 的标签（如内部标签 `"proof method"`）视为非法；非法时**抛 `KeyError`**，这样两条路径的现有处理原样保留（直接路径报 "Invalid entity kind" 警告，fork 过滤路径静默丢弃），fork 路径不动。
- **规则落在 `Minilang_State.semantic_knn_counted`**（所有查询路径——直接查询、候选扩展、fork 过滤、`exact_name`——都到这里），紧挨现有的 read-memory 剥离，按 METHOD kind、读 `the_session().runtime.tactics`：
  - `exact_name`：在**整个白名单**里按 agent 可见名或全名查（agent 写来的名字先经 `ascii_of_unicode`；owner 2026-10-10 赞同全名也可），命中则构造 `SemanticRecord(METHOD, 全名, None, None)`（不读 DB、不经 `universal_key_and_name_of`），不在即现有的 Undefined 文案；
  - 带描述的查询（`query` 非 `None`；fork 过滤路径传的是 `""`，也走这一支）：对每个 **query 条目**加一个 `ExtraKey(key, 全名)` 进 `ContextExtended` 域（与 THEOREM 已在用的额外候选机制同一套，两者同时出现时合并），混合 kind 一次联合排序；
  - 无描述的查询（`query is None`）：把 query 条目按白名单顺序放在**最前面**（`k` 封顶因此不可能挤掉它们——其它 kind 的条目 agent 可以靠调整 `kinds` 顺序找回，query 条目不行），其后才是 `entities_of` 结果按模式分数排序并截到 `k_fetch` 的部分；query 条目直接构造 `SemanticRecord(METHOD, 全名, None, None)`，不读 DB，计入 `total`；
  - `name_contains` **作用于** query 条目（与 ML 对其它 kind 的枚举过滤相同：模式先经 `ascii_of_unicode`，每个模式都是全名的大小写不敏感子串），排序检索与无描述查询用同一份过滤后的列表；term/type 模式与 `theories_include` 不作用于白名单条目；
  - **显示文字统一覆盖**：三条分支的结果建好后，凡 `rec.name`（全名）在 `runtime.tactics_by_full` 里的 METHOD 记录，其显示文字一律替换为白名单里（已归一化的）interpretation——DB 只为白名单条目提供排序向量，agent 看到的文字与 prompt 逐字节相同，与他人是否改写 DB 无关。
- 显示：名字（agent 可见名，来自 §5.4 的 METHOD 分支）+ 白名单里的 interpretation；不打印 `method_setup` 源码。
- 不用 `Semantic_Vector_Store.Restricted`（它会丢掉混合查询里的其它 kind）；不改 `Isabelle_RPC`。

### 7.5 改名范围

内部一律 "proof method"：`EntityKind.METHOD` 标签、Semantic DB、解释模型提示词、isabelle-rpc 全部不动。agent 可见的只有：`query` 的 kind 枚举值、`Tactic` 的 schema 与 description、§7.3 的段落。

---

## 8. 已锁定决策汇总

见 §0。补充实现级裁定：记录值只在 REPLAY 封顶、LIVE 实跑重计；记录值只在装配时装入；探测触发是类属性；`Tactic` 不是选择项、不读 method 表达式；白名单在 `Tactic.gen_single` 查、ML 不查；`activate_tactics` 是白名单的唯一写入点，操作表与 `tactics_by_full` 由 `_user_operations` 与白名单推导，顺序与"白名单非空 ⟺ `Tactic` 在表里"按构造成立；DB 同步是独立一步、在空库提示之后、写前比对、失败即调用失败；AoA 调用的 method 枚举回调为空；显示文字一律来自白名单；交互 fork 收到发起方的 system prompt，prompt 段落随之可见。

---

## 9. 测试

遵守 `IsaMini/AoA/CLAUDE.md`"Test framework"：每个 `@model_test` 独占一个 `.thy`，第三个参数是 `by aoa` 所在行；`python -u ../../test_AoA.py -f NAME > /tmp/aoa.txt 2>&1`，一次一个。**golden**：夹具首次运行会自动写出 `Tests/NAME.yml`，把它当草稿交 owner 审阅，批准前不提交、不依赖；绝不改已有 golden。模型测试只能通过 `Runtime(…, tactics)`/`activate_tactics` 启用 `Tactic`；**每个夹具 `.thy` 必须声明它所用的全部 tactic**（否则 `gen_single` 的 `validate` 先拒绝，看不到 Isabelle 的错误）。凡走 `Parse_Op_List` 才有的校验（描述型事实被拒等），用例须经 `_edit_tool_logic` 发原始 JSON，不能直接 `gen_single`。

**一次性 DB**：凡夹具声明了 `AoA_tactics` 的**模型测试**都在一次性 Semantic DB 上运行。因为同步在调用启动时、在测试体之前执行，`_isolated_semantic_db` 要拆成进程级部分（`SEMANTIC_DB_DIR` 切换、单例关闭、释放 lmdb 环境；`run_all_tests` 对 `isolated_db` 用例在 `run_app` 与读结果外围进入——依赖 RPC host 线程与运行器同进程）与连接级部分（`_semantic_vector_stores`，留在 `ModelTestCase.run`）。**防呆**：进程级部分把一次性路径记进 `IsaMini.AoA.test` 的模块全局；`ModelTestCase.run`（在服务 AoA 调用的进程里跑）断言 `os.environ["SEMANTIC_DB_DIR"]` 等于它，不等即 `TestFailed`——REPL 指向别的 RPC host 时同步会写进真实 DB，这条断言让它当场暴露。确认 `ExperienceMemory`、`DedupOverwriteSameRun`、`DedupRejectThenAdjacent`、`ReadMemoryGate` 的 golden 逐字节不变。ML theory 测试只经 `repl.file` 求值、从不发起 AoA 调用，声明又只是 theory data，所以它们不碰 DB，不需要夹具。

| 用例 | 夹具 | 动作 | 断言 |
|---|---|---|---|
| `Tactic1` | `.thy` 声明 `induction`、`simp`；目标 `rev (rev xs) = xs` | 经 `_edit_tool_logic` 发原始 JSON：`induction` 步带内联 `proofs: [[{Tactic simp}], [{Tactic simp}]]`（照 `InferenceRuleProofsPerSubgoal`） | 两个子目标节点各有证明体；`unfinished: 0`；op 第一分量是全名 `HOL.induction`；`node.assemble()[0].arg` 第五分量非 `None`、LIVE op 第五分量为 `None` |
| `Tactic2` | 声明 `simp`；目标 `x + 0 = (x::nat)` | `Tactic{tactic:"simp"}`，把 `schematic_vars_of_derived_subgoals` 包上计数器 | 零子目标，完成；计数器为 0（短路生效） |
| `Tactic3` | 声明 `simp`；`assumes "x = 1" shows "x + 1 = (2::nat)"` 带 `Have h: x = 1` | `Tactic{tactic:"simp", facts:[{name:"h"}, {proposition:"…"}]}` | chained facts 生效；`FACT_PRF` 回填进 op 流；完成；最终状态为 `success`（装配后的验证重放在 REPLAY 分支通过） |
| `Tactic4` | 声明 `simp`、`rule`；目标形状使 `conjI` 不匹配（如 `x + 0 = (x::nat)`） | `simp` 配 `arguments:"foo"`；`simp` 配 `arguments:"‹junk"`（未闭合 cartouche）；`rule` 配 `arguments:"conjI"` | 三种错误原文（"Bad arguments for method …"、"Outer lexical error …"、"Fail to apply the tactic"），节点 FAILURE |
| `Tactic5` | 声明 `rule`；`∃x. P x ∧ Q x`，`P`、`Q` 不透明，sorry 掉的 `p0: P 0`、`q0: Q 0`；计数器为**累计值** | 第一步 `rule exI` → 单子目标仍含 `?x`，断言**无交互**、计数器 = 1（`?x` 在，短路不触发，预跑一次；无交互证明 `Tactic_Like` 的共享判据替代了保守默认）；第二步 `rule conjI` → 共享 `?x`，断言恰一次 term 交互、计数器 = 2、答 `?x := 0` 后无 schematic；收尾 `unfinished: 0` | `Tactic_Like` 判据；`_probes_post_insts` 与 `apply_post_insts` 接上 |
| `Tactic6` | 声明 `simp`；事实找不到 / 不可证 / 描述型 | 经 `_edit_tool_logic`：`facts:[{name:"nope"}]`；`facts:[{proposition:"False"}]`；`facts:[{english:"…"}]` | FAILURE "Fact … not found"；`FACT_IN_TIME_FAIL` 原话；Python 校验器的 `ArgumentError`（模型测试不经 MCP schema 校验） |
| 白名单检查 | `test_*.py`，`bare_session()` 加 `tactics=` 参数（条目可用 Python 拼的假 METHOD 键：16 字节 + 标签 + UTF-8 全名），直接 `Parse_Op_List` | 只声明 `simp` 时写 `tactic:"tactic"`、`tactic:"aoa"`、`tactic:"auto"`，顶层与 `Have` 体内各一次 | 都抛 `ArgumentError`（"must be one of …"），无任何 Isabelle 调用；另断言 `Runtime(["Tactic"])` 被拒（`Tactic` 不是 user operation） |
| 操作表与 schema | `test_*.py` | `Runtime([], [])` / `activate_tactics` 空与非空各一次；带 user operation 时再激活一次 | 表里 `Tactic` 的有无与 `edit` schema 里 `$defs/Tactic`、`anyOf` 成员的有无**同时**成立；顺序为常驻 → `Tactic` → user operation；枚举值是 `simp` 而非 `HOL.simp`；四种驱动变体一致；`BUILTIN_OPERATIONS` 恰为基础 `$defs` 里有条目的操作；模板通过注册检查；`"proof tactic"` 在 `query` schema 中的有无按 query 条目决定（只有 prompt 条目时不出现），与 `AoA_enable_read_memory` 真/假做叉积 |
| `TacticPrompt` | `@model_test`，照 `ReadMemoryGate`；**夹具 `.thy` 声明那条多行、含 `⟹` 与嵌套 cartouche 的 prompt 条目**（只有它会被启动同步写进 DB），其余情形在测试体里用 `activate_tactics` 复用 `runtime.tactics` 的键构造 | 五种情形：无 prompt 条目 / 一条 / 那条多行 interpretation / 一个自写 system prompt 的 `Task` / 一个 `system_prompt` 返回 `None`、`task_initial` 非空的 `StdTask` | 段落缺席 / 出现在 system prompt 末尾、按白名单顺序 / 出现且归一化、Unicode 无 `\<` 转义、与 DB 记录逐字节相同 / 自写 prompt 之后仍出现 / 出现在 initial prompt 末尾，task 的文字与框架的长版**之后**（用未缓存的 `_compute_initial_prompt()` 读）；major 与 worker 有；交互 fork 收到发起方的那份 |
| 声明 | ML theory 测试 `Tactic_Declaration_Test.thy`，经 `theory_test` 登记（照 `User_Operation_Replay_Test.thy` 用 `assert` 查 `tactics_of`；**反例写在 `ML ‹…›` 块里**用 `Attrib.attribute_cmd` 从源码文本施加属性并捕获 `ERROR`，否则顶层 `declare` 出错会使整个 theory 失败） | 恰好 §0 的示例；`add:` 省略；`add: simp auto`（漏写 interpretation）；`shown_in` 非法值；`del:`；同名重复；拼错名字 | `simp` in_prompt = false、`induction` = true；省略模式 = `add:`；漏写与非法 `shown_in` 报 `ERROR`（解析失败不产生任何上下文，部分写入按构造不可能，不另测）；省略 `shown_in` = query；`del` 生效；最后声明优先；拼错报 `ERROR` |
| DB 同步（端到端） | `@model_test`，全新一次性 DB | 调用启动 | 测试体内记录已存在：kind METHOD、名字 `HOL.simp`、interpretation 等于归一化文字（全新 DB 上事先不可能有记录，存在即证明启动同步写了） |
| DB 同步（单元） | `test_*.py`，一次性 DB，直接调 `declare_interpretation` | 相同文字再调；预置流水线形状的 METHOD 记录（带 `position`、`expr` 非 `None`，interpretation 不同）后调；非 METHOD 键；删掉记录后再调 | 相同文字不写、不作废向量；整条记录等于预置记录换掉 `expr`（`None`）与 interpretation（归一化文字）、向量已作废；非 METHOD 键抛错；记录重现 |
| 同步失败 | `test_*.py`，直接调 `IsaMini_AoA`（装饰器不改变函数；连接对象只需有 `callback` 属性；同步在 `Context.unpack` 之后、驱动分支之前，占位 `({}, {}, {})` 与 `0` 可被解包） | 把 `Semantic_DB.declare_interpretation` 打补丁使其记录调用并抛出，`_ensure_semantic_db` 打桩记录调用；白名单非空；驱动字符串 `"test.<nonexistent>"` 与一个未知驱动各一次 | 调用以**那个被打补丁的异常**失败（若同步被错放在驱动分支之后，看到的会是 "Test Not Found" 或未知驱动）；记录的顺序在 test driver 下是 `["sync"]`、其它驱动下是 `["hint", "sync"]`（钉住"同步在空库提示之后"） |
| 检索 | 端到端（一次性 DB）；白名单只含 `Main` 里的 method：一个 query 条目、一个 prompt 条目；夹具没有自己的 lemma、保留 `assumes h` 使陈述可证；空库上 lemma 候选是从上下文按 heap 顺序枚举的占位记录（`assumes` 在根状态不是候选），所以两个混合查询只把**形状**写进 golden 并断言（带描述的排序查询：`simp shown / lemmas shown`；无描述 `number: 1` 查询：`first entity / entities`），不把 heap 的枚举顺序钉进去（§13.15）；每个查询前用 `Session._reset_view_state()` 使结果各自独立；测试为 `Interaction_RetrieveForSearch` 打桩 | 见断言列 | `kinds:["proof tactic"]` 带描述只返回 query 条目、显示声明的 interpretation、不打印源码；`kinds:["lemma","proof tactic"]` 带描述两种都返回；同样两种、无描述、`number: 1` 时 query 条目仍在且在最前（直接路径：前置，不被 `k` 挤掉；fork 路径上无描述查询以 `""` 排序、50 个候选，§7.4）；无描述且 `name_contains ["aoa"]` 什么都不返回（query 条目也按 `name_contains` 过滤），`name_contains ["Simp"]` 恰好返回那个 query 条目（大小写不敏感），prompt 条目与 `aoa`/`hammer_or_aoa`/`aoa_replay` 均不出现；`exact_name` 查 prompt 条目 `auto` 返回其 interpretation、查白名单外的 `blast` 返回 Undefined；调用启动后把该 method 的 DB 记录改成别的文字再查，三种查询显示的仍是声明文字；`kinds:["proof method"]` 在直接路径报 "Invalid entity kind" 警告；**交互检索打开时**：前述各条相同（无描述查询的候选数除外，见前），唯 `kinds:["proof method"]` 带描述时静默丢弃（结果为 "No relevant entities found."），`exact_name` 仍走直接路径报警告 |
| 重放封顶与 REPLAY 接受 | **提交并经 `theory_test` 登记的** ML theory 测试 `Tactic_Replay_Test.thy`，夹具**不**声明 `AoA_tactics` | REPLAY 模式、记录值取极小、一个不终止的 tactic；另一例：记录为 `TACTIC ("HOL.simp", "", [], [], SOME 宽裕时间)` 的平凡目标；1 s 内层限时下 LIVE 跑不终止的 tactic、带宽裕记录的 REPLAY 跑一个 4 s 的 tactic | 封顶 → "Tactic replay timed out"；无记录运行的内层超时 → "Timeout"；带记录的 REPLAY 不受内层限时（4 s 的 tactic 跑完）；LIVE 带记录不封顶；白名单为空时 REPLAY 照样成功关闭目标（钉住"ML 不查白名单、REPLAY 照收"） |
| 插件标志 | `test_user_operations.py` | 插件类 `(UserNode, _Hooks, CaseSplit_Like)` | `_probes_post_insts` 为 `False` |
| 回归 | 全量 golden | `Tactic_Like` 上提、`_probes_post_insts` 替换、夹具改造、`BUILTIN_OPERATIONS` 收窄 | 无差异 |

**无法用测试钉住、靠评审守住的裁定**："声明时不做 RPC"、"不做哈希预检"（theory 测试里 RPC host 同进程、每个用例都是全新 DB，违反也看不出）；"`aoa` 不处理"、"ML 执行不扫描"、"hint 盲区"、"Codex 不支持"是"不建东西"的决定，无需测试。

---

## 10. 风险 / 提醒

- `TACTIC_TIMES` 若忘加 `pack_opt` 分支会静默丢失（§5.4），靠 `Tactic1` 的装配断言兜住。
- DB 同步不依赖是否装了预建 Semantic DB（用户层按需创建），`Isabelle_Semantic_Embedding` 是硬依赖；同步失败即调用失败（owner 裁定：这些失败都是环境坏了或代码错了）。**不得**按"DB 是否为空"或"是否装了 DB"给同步设闸；但 `_ensure_semantic_db` 的空库提示必须在同步之前读库（§7.2）。
- 一种例外：现有 `invalidate_vectors` 对向量存储的**写**失败只记日志不抛（打开失败才抛），所以这一种失败不会使调用失败，后果是一个过期的排序向量；显示文字仍来自白名单。沿用现有行为，不另写抛错变体。
- 写入的是共享的 Semantic DB，其它读 DB 的工具也会看到这些 interpretation；不同 theory 对同一 method 写不同文字时**后调用者生效**；但 AoA 自己显示的文字永远来自白名单（§7.4）。
- universal key 按 ML 进程缓存（§5.1）：WIP 键到下一个 ML 进程才换成最终键；不影响一致性。
- `arguments` 的错误原文来自 Isabelle 的词法器与该 method 自己的解析器，措辞不受我们控制；其中的 method 名按 Isabelle 默认的 extern 规则打印，可能是全名（golden `Tactic4`：`Bad arguments for method "HOL.simp"`）——这是 §0"名字"行的例外；agent 若照抄全名，会在白名单检查处、任何 Isabelle 调用之前被拒。
- `Tactic_Like` 上提改变 `InferenceRule` 的 MRO，行为不变；跑全量 golden 回归确认。
- 驱动若自行覆盖 prompt，§7.3 的段落会被绕过（已知并接受）。

---

## 11. 跨 fork 事项（`USER_OPERATIONS.md`，另一会话）

1. §3 登记消息标签 22 归 `TACTIC_TIMES`。
2. §4.1 提到 `_POST_INST_COMMANDS` 的两处改为"探测触发是类属性，`Tactic_Like`/`CaseSplit_Like` 为 True、`UserNode` 钉死为 False"。
3. §4.2：框架会把 §7.3 的 tactic 段落接在 task 自写的 system prompt 之后。
4. 注册记录的 `default : bool` 保持；`Tactic` 永不是选择项。
5. 样例插件的操作名 `Apply` 与 `Tactic` 不冲突。
6. §5.1/§5.2/§5.3：操作表 = 常驻操作 + （白名单非空时）`Tactic` + 本次的 user operation，顺序亦如此；"常驻"= 基础 `cc_edit.jsonc` 里有条目；`Runtime` 构造函数多一个 `tactics` 参数；`Tactic` 的 schema 按调用放置（与 user operation 同法）；手写证明在常驻操作加（白名单非空时）`Tactic` 下运行。
7. `IsaMini.AoA` 参数元组的布尔嵌套与白名单槽位（§5.4）影响其 §5.2 的描述。

---

## 12. 文件清单

| 文件 | 改动 |
|---|---|
| `Agent/agent.ML` | datatype ×2、`check_command_i`、`interpret_i`、`TACTIC_TIMES`、`lex_embedded` |
| `Agent/agent_packer.ML` | `pack_times`/`unpack_times` 抽出并导出 `pack_times`；`TACTIC` 分支 ×2 |
| `Agent/agent_server.ML` | `AoA_tactics` 数据与属性、`tactics_of`；`pack_opt` 22 号分支；参数元组嵌套 + 白名单槽位；method 枚举回调注册为空；`retrieve_entity` 的 METHOD 一支 |
| `IsaMini/AoA/model.py` | `Tactic_Like`（含 `InferenceRule` 改基类）、`_probes_post_insts`（`SubgoalMaker`/`Tactic_Like`/`CaseSplit_Like`/`UserNode`）、`SubgoalMaker._execute_opr` 与删除 `_POST_INST_COMMANDS`、`Tactic` 与 `construct_schema`、`Node.schema_for_call`、`Tactic_ToolArg`、`Minilang_Operation.TACTIC`、`Tactic_Times_Msg` 与 `unpack_message` 的 22 号分支、`BUILTIN_OPERATIONS` = 注册表减 `Tactic`（保留 `_check_builtins_advertised`，不加断言）、`TacticEntry`（名字是 `IsaTerm`）、`Runtime.__init__`/`activate_tactics` 与推导属性 `tactics`（只读视图）/`operations`/`tactics_by_full`、`_print_facts`/`_unfound_failure`（`Obvious`/`Chaining`/`Derive`/`Unfold`/`Rewrite` 改用，C19）、`StdBlock.assembled_beginning_opr` 与 `assemble`、`_tactic_prompt_block`、`Session.system_prompt`、`_compute_initial_prompt`、`semantic_knn_counted`（规则与显示覆盖）、`proof_operation` 的检查辅助函数 |
| `IsaMini/AoA/mcp_http_server.py` | `_edit_schema_for(runtime)`；`_tool_schemas_for` 追加 `"proof tactic"` |
| `IsaMini/AoA/toplevel.py` | 解包白名单与嵌套布尔；`Runtime(user_operation_names, tactics)`；同步步骤（原位循环，在空库提示之后、驱动分支之前；原 `if not is_test_driver` 块拆成两半以插入它） |
| `IsaMini/AoA/retrieval.py` | kind 枚举追加辅助函数；标签函数（非法抛 `KeyError`） |
| `Semantic_Embedding/.../semantics.py` | `declare_interpretation`（`_Semantic_DB` 的方法，登记进 `__setitem__` 的写入者名单）、归一化辅助函数 `normalize_interpretation` |
| `IsaMini/AoA/test.py` | 一次性 DB 夹具拆分（进程级 / 连接级）与防呆断言；进程级一半把系统库探测钉为"无"；新模型用例 `Tactic1`–`6`、`TacticPrompt`、检索、DB 同步（端到端） |
| `IsaMini/AoA/Tests/User_Operation_Test_Base.thy` | 共享基座（五个 `User_Operation_*` theory 测试与两个 Tactic theory 测试共用）：`message_of` 用 `Protocol_Message.clean_output` 剥掉 PIDE 标记——经运行器跑时报错里带引号的名字带标记，`fails_with` 匹配不到；解析不了的报错（自身含 chr 5/6 的文本）原样保留 |
| `IsaMini/AoA/test_user_operations.py` | `bare_session` 加 `tactics=`；`BUILTIN_OPERATIONS` 相关注释；§9 新增的单元测试 |
| `Tests/Test_Tactic*.thy`、`Tests/Tactic*.yml`、其它 `test_*.py`、ML theory 测试 | §9 |
| `library/proof.ML`、`Minilang_AoA.thy`、`tools/cc_edit.jsonc`、`tools/cc_semantic_search*.jsonc`、`Isabelle_RPC`、isabelle-rpc 标签表、`test_AoA.py` | **不动** |

---

## 13. 实现记录（2026-10-10）

按 §12 的顺序实现，正文已按实际改法改正。与第六稿不同的地方（含 2026-10-10 代码对抗评审后、owner 裁定的修改，编号 C 为该评审的质疑号）：

1. **agent 可见名**（§5.1）：普通的 `Name_Space.extern` 把 HOL 的 `simp` 外显为 `HOL.simp`（Pure 也声明了一个 `simp`），而 `simp` 本就解析到 `HOL.simp`；故用库函数 `Name_Space.extern_shortest`（辅助函数 `agent_method_name`），`tactics_of` 与 `retrieve_entity` 的 METHOD 分支共用（C4）。Isabelle 自己的报错里 method 名仍按默认规则打印，§0"名字"行据此收窄（C27）。
2. **`lex_embedded`**（§5.2）不带解析器参数：`read_method_text` 已把切词与读表达式分开。
3. **DB 同步的写入者**（§7.2）：`declare_interpretation` 是 `_Semantic_DB` 的方法（它用 `_ensure_env`、`_raw_for_update`、`_put_fields`，与其它写入者同列）；`toplevel.py` 原位循环调用，不在 Semantic_Embedding 里放 AoA 命名的包装（C26）。
4. **`Tactic_Like`**（§6.1）除了文中列的三项，还上提了 `InferenceRule` 与 `Tactic` 逐字相同的部分：`_beginning_opr_err_msgs`（头行文案是类属性 `_fail_header`）、`_child_refresh_failure_err_msgs`、`_title_of_children`、quickview 与完整打印里的 "derived goal" 段（`_quickview_derived_goal`、`_print_derived_goal`）；`gen_single` 不上提（C13）。`Tactic` 的 "with facts" 打印块与"事实找不到"检查是既有节点的第五份粘贴，改为与 `Obvious`/`Chaining`/`Derive`/`Unfold`/`Rewrite` 共用 `_print_facts`、`_unfound_failure`（C19）。`InferenceRule` 的行为与 golden 不变（全量回归 2026-10-10 确认）。
5. **同步步骤的位置**（§9）：在 `Context.unpack` 之后、驱动分支之前；单元测试传可解包的占位值，并钉住"在空库提示之后"（C16）。
6. **`semantic_knn_counted`**（§7.4）只在 `kinds` 含 METHOD 时读 `runtime.tactics`；query 条目按 `name_contains` 过滤（C25），在无描述查询里前置（C7）。
7. **`PlainAgent/`**：owner 2026-10-10 裁定不动（未跟踪目录，另一条线的工作）。
8. **声明的反例**（§9）用 `Attrib.attribute_cmd` 从源码文本施加属性，报错文案是 Isabelle 标准的 "Bad arguments for attribute "AoA_tactics"" 与 "Undefined method: …"。
9. **ML theory 测试**（§9）：`Tactic_Declaration_Test.thy`、`Tactic_Replay_Test.thy` 经 `theory_test` 登记进套件，由运行器跑（C1）；共享基座 `User_Operation_Test_Base.thy` 的 `message_of` 改为用 `Protocol_Message.clean_output` 剥掉 PIDE 标记（经运行器跑时报错里带引号的名字带标记，`fails_with` 匹配不到；先前手写的 `YXML.parse_body` 在 `User_Operation_Interpret_Test` 那条自身含 chr 5/6 的报错上崩，复审补跑发现，R10）；ML 侧编译验证用 `isabelle build -b Minilang_AoA`（owner 当日授权）。
10. **封顶**（§0、§5.2）：带记录的 REPLAY 只受 `embedded_replay_limits` 封顶，内层限时不叠加——与 HAMMER 相同（C6，owner 放宽）。
11. **`Runtime`**（§7.2）：`operations` 与 `tactics_by_full` 是由 `_user_operations`、白名单推导的只读属性（C18），`tactics` 本身是私有字段上的只读视图（R12）；`BUILTIN_OPERATIONS` = 注册表减 `Tactic`，保留原有双向检查、不加断言（C20）。
12. **测试基座**：夹具声明了 `AoA_tactics` 而未 `isolated_db=True` 的用例在 `ModelTestCase.run` 入口即 `TestFailed`（C11）；一次性 DB 夹具拆成进程级与连接级两半。评审中提出的"失败时把输出写到 `.actual.yml`"改动超出本设计范围，未纳入（C22，可另提）。
13. **未采纳的评审意见**（裁判驳回）：同步写入会压掉后续进程的空库提示（C2）、多行 `arguments` 的打印（C8）、TACTIC 编解码往返测试（C15）、声明的解释会随系统库发布（C17）。
14. **另行处理**（owner 2026-10-10）：探测轮次直接在目标状态上执行、不再先跑 scratch（C24，共享机制，等本批修复提交后单独做、单独提交）。（已落地，见第 19 条）
15. **C3 可选部分的替代做法**（§9 检索行）：owner 采纳的是"夹具加一条 lemma、混合查询用 `theories_include` 限定到夹具理论"。实测 `theories_include` 没有枚举出夹具自己的 lemma，而且给夹具加 lemma 会移动 `by aoa` 的行号；改为两个混合查询只打印并断言形状，夹具恢复原样。owner 2026-10-10 裁定测试相关由实现者自决，据此以重新生成的输出替换 `TacticQuery.yml`。
16. **复审轮（2026-10-10，编号 R）**：带 Isabelle 符号的 agent 可见名此前以 ASCII 记法作键并显示，而 `query` 的显示走 `IsaTerm` 成 Unicode，`exact_name` 按显示的拼法查会得到 Undefined——owner 裁定 agent 看到的一律是 Unicode、agent 写来的名字先转 Isabelle ASCII、名字纳入 `IsaTerm` 管理（R3，§5.1、§6.2、§7.2）；`exact_name` 也接受全名（R8，owner 赞同）；`name_contains` 的模式补上 C25 裁定里的 `ascii_of_unicode`（R7）；一次性 DB 夹具把系统库探测钉为"无"（R9）；`tactics` 只读视图（R12）；`TacticQuery` 改用 `Session._reset_view_state()`（R15）；theory 测试内部的旧名字面量、`Tactic` 与 `TacticQuery` 的 docstring、以及本文档术语表/§5.2/§5.4/§7.2/§8/§9/§12 中未随 C3/C4/C5/C18/C20/C26 更新的文字（R1、R2、R4、R5、R6、R13、R14）。R11（形状行钉住检索常量）裁判驳回。
17. **失败节点不显示 derived goal**（2026-10-13，单独的 git 提交，C24 的准备）：`Tactic_Like` 的两个 derived goal 打印辅助函数改为经 `_derived_goal()` 读目标，它只在节点 status 为 SUCCESS 且派生子目标不多于一个时返回 `self.goal()`。修掉再刷新失败后在 "Error:" 下显示旧 derived goal 的既有问题；也挡住 C24 会让首次刷新中失败的节点显示一个从来不是它结果的中间目标（探测挂起期间 `refresh`、API driver 的自动 compaction、深度重启后的新对话都会重新渲染树）。再刷新期间节点仍带着上一次的 SUCCESS，那个窗口与今天同类、不在此例内；`GoalNode` 的目标头部与删除节点时的存档行也不看 status，未改。golden 不变（全量回归 2026-10-13，与前一个 git 提交——`proof_opr` 装上 reporter 后清空消息缓冲——合跑；打印 derived goal 的用例全部通过；9 个失败都是语义库按 universal key 查不到 HOL 实体，起因是发行版的 `src/Pure/Pure.thy` 于 2026-10-12 被改、HOL 的 theory hash 随之改变，与本改动无关）。
18. **白名单的 ML 入口**（2026-10-14，TAT 的 `Define` 会话，owner 授权直接改 AoA 代码）：`add_tactics`（§5.1），`add_entry` 与它共用新抽出的 `add_tactic`；同日 `agent_hint.ML` 的 goal hint 得到同样的入口 `Agent_Hint.add_goal_hint`（GOAL_HINTS.md §1）。`Tactic_Declaration_Test.thy` 加第 7 节、`Goal_Hints_Test.thy` 加第 12 节。验证：在 `-l Minilang` 的 REPL 上（`Minilang_AoA` 连同改过的 ML 从源码加载）经运行器跑 `TacticDeclaration_Minilang`、`GoalHints_Minilang` 各 1/1 通过；另以探测 theory 确认 `whole_prop "Wellfounded.accp _ _"` 的 hint 在 `∀x. accp R x` 上触发、`relation`/`size_change`/`lexicographic_order`/`pat_completeness` 四个名字在 `Minilang_AoA` 的 context 里解析、未加白名单的 context 仍为空，以及一个写错标识符的 theory 被运行器判为失败（探测不提交）。heap 未重建，REPL 由该会话自起自停。
19. **C24 落地**（第 14 条；owner 2026-10-10 采纳方向、2026-10-11 批准形状；单独的 git 提交；设计、owner 的逐项裁定与被驳回的评审意见（已归档）见 `IsaMini/AoA/docs/archive/C24_PROBE_IN_DEST_DESIGN.md`）：探测从 `SubgoalMaker._execute_opr` 移进 `SubgoalMaker._refresh_the_beginning_opr`（`StdBlock._refresh_the_beginning_opr` 成功返回之后调用 `SubgoalMaker._run_the_probe`），`SubgoalMaker` 不再覆写 `_execute_opr`；不再先跑 scratch。探测的第 0 轮就是 `StdBlock._refresh_the_beginning_opr` 把 beginning op 执行进节点自己的目标状态（`dest`）的那一次，此后每一轮把 `_beginning_opr_with_insts(rounds)` 执行进同一个 `dest`（`_probes_post_insts` 为 True 的四个类各自实现它、以参数接收实例化轮次；`beginning_opr()` 在 `Tactic_Like` 与 `CaseSplit_Like` 各定义一次、以 `self._post_insts` 调它；`SubgoalMaker` 的默认实现抛 `InternalError`；`Tactic.assembled_beginning_opr` 仍经 `_tactic_opr`）；整体扫描与 `Interaction_InstantiatePostSchematics` 读的都是 `dest`，`InferenceRule`/`Tactic` 的服务端预跑仍从执行前的状态重跑同一个带实例化轮次的 op；收敛那一轮的执行结果就是节点保留的结果，`_post_insts` 只在收敛处赋值；每一轮仍把已累积的实例化轮次真正作用到目标上，收敛机制不变。执行次数：常见情形 1 次（原 2 次），第 0 轮执行失败 1 次（原 2 次），k 个实例化轮次 k+1 次（原 k+2 次）；服务端预跑次数不变。任何一轮失败都是节点的失败：第 0 轮执行失败与原来相同，`dest` 不动；某一轮（含第 0 轮）的 `_probe_residual_schematics` 失败时，`dest` 留着该轮的执行结果；第 k ≥ 1 轮执行失败原先会不带实例化轮次重跑、节点报告成功而保留的 op 没经过 `_probe_residual_schematics`，现在节点失败，`dest` 留着最后一次成功执行的状态，不加 reset（再刷新时，与成功过的节点再刷新失败后留着旧状态是同一种情形；首次刷新时这是 C24 新引入的情形，其显示由第 17 条按节点的 status 门控）。第 k ≥ 1 轮的执行失败只能来自墙钟上限（RULE 8 s、CASE_SPLIT/INDUCT 10 s、TACTIC 的 `mini_single_cmd_timeout`、每轮 `INST_GOAL_VARS` 8 s、prove-in-time 搜索 10 s）；首次刷新中的 `InferenceRule` 在第 k ≥ 1 轮失败后进入既有的 `_autoconvert_to_rewrite`（与第 0 轮超时同一事件，不单独排除）。每一轮都写 `proof_oprs.yaml`（执行记录，失败时另有错误记录），`log=False` 只剩 `_rewrite_trial`。`Node._execute_opr` 与 `UserNode._execute_opr` 两处的 `dest` 收窄为非 `None`。既有 golden 全部逐字节不变（全量回归 2026-10-18，391/402 通过；未通过的 11 个与第 17 条那次回归的输出逐字节相同、都与本改动无关：9 个是第 17 条所述语义库按 universal key 查不到 HOL 实体，2 个是只 `imports Main` 的夹具 `ReferFactByProposition`、`ForkProviderConflict` 找不到 task "usual"）；新增单元测试 `test_post_inst_probe.py`（执行次数、第 k ≥ 1 轮失败、`_probe_residual_schematics` 失败、16 轮上限、四个类的 `_beginning_opr_with_insts`）、注入故障的模型测试 `PostInstRoundFailure`（只断言，golden 一行 `status: FAILURE`）；`Tactic2`、`Tactic4`、`Tactic5`、`PostInstRuleShared` 加执行计数断言（经 session 的 `on_operation_start`，不打印，golden 不变）。若有 golden 以 Timeout 或 FACT_IN_TIME_FAIL 翻转，先按"失去偶然的第二次运行"排查。未采纳的评审意见（裁判驳回）见归档设计 §11。

状态：ML、Python、单元测试（`test_user_operations.py` 49 项，含 §13.16 的符号名用例）通过。复审轮（§13.16）的修复落地、heap 经 `isabelle build -b Minilang_AoA` 重建（owner 授权）、REPL 重启后，经运行器逐组重跑：两个 ML theory 测试与九个模型测试（`Tactic1`–`6`、`TacticPrompt`、`TacticSync`、`TacticQuery`）11/11；`UserOp` 组（五个 `User_Operation_*` theory 测试、八个 `UserOp_*` 模型测试）13/13；`ExperienceMemory`、`DedupOverwriteSameRun`、`DedupRejectThenAdjacent`、`ReadMemoryGate` 4/4。`TacticQuery.yml` 已按 owner 的 R2 授权换成重新生成的输出，重跑逐字节一致；其余八个新 golden owner 2026-10-10 批准。注意：REPL 会缓存已加载的测试 theory——改了 `User_Operation_Test_Base.thy` 之后不重启 REPL，跑的仍是旧代码。第一轮代码评审的修复（§13 列表）落地后重跑：`Obvious`/`Chaining`/`Derive`/`Unfold`/`Rewrite`/`InferenceRule` 名下全部 85 个既有 golden 逐字节不变。第一轮评审前的全量 golden 回归（REPL 用 `Minilang_AoA` heap、`RPC_Host` 指向运行器的 host）跑了 390/393 个：`IMO_1966_p5`、`HavePowerParsing`、`UnfoldCertJoin` 的夹具 `imports MathBench_Prover`，在该 heap 上要从源码加载整套 MathBench_Prover、20 分钟客户端超时，未跑；其余 390 个中 383 个通过，7 个失败都是既有问题、与本设计无关：`ReferFactByProposition`、`ForkProviderConflict`（夹具只 `imports Main`，user operation 那条线的 task 注册表在该上下文不存在），`SemanticKNN_patterns`、`SemanticKNN_induction_rule`、`QueryNullFields`、`QueryScalarStringField`、`QuerySearchSummary`（真实向量库内容/排序漂移，golden 写于 2026-08-24）。受本设计影响的既有 golden：`InferenceRule*`、`PostInst*`、`GateSchematic` 在第一轮修复后重跑逐字节不变（复审轮的改动不触及它们）；`ExperienceMemory`、`Dedup*`、`ReadMemoryGate`、`UserOp_*` 在复审轮修复后重跑逐字节不变。§11 的跨 fork 事项（`USER_OPERATIONS.md`）尚未落实（owner 2026-10-10：交给 user operation 那条线的会话；该会话当时已不在线，待转发）。

待办（owner 2026-10-10，"之后再说"）：`Tests/Test001.thy`（`ReferFactByProposition`）与 `Tests/Test_ForkProviderConflict.thy` 只 `imports Main`，自 `62f6b89` 起在 AoA 调用入口因 "User task "usual": no imported theory registers it" 失败；修法应是给夹具加 `Minilang_AoA.Minilang_AoA` 的 import。`PlainAgent/`：owner 裁定不动。
