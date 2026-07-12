# 设计文档:Minilang / AoA 的 locale interpret 操作(`Interpret_Locale`)

> **状态(2026-07-12):已实现并合入**(Isa-Mini `e8a6a99`,translator `d5206e2`,MLML `95ae7b0`)。
> 语义 = **Interpret(实例化)**。经**三轮对抗评审**(含执行前终审)+ 实测。§0 是权威审批状态。
>
> **本文档的价值在于记录 *why***:三轮评审抓出的 C1–C9(为什么 CB 不能用 `elim_conjunctions`、
> 为什么 instantiation 值必须 cartouche 包裹、为什么 `interpret_i` 不能走 `parse_cmds`、
> 为什么节点必须**无条件**开块)、实测证据、以及被否掉的方案。改这块代码前先读它。
>
> **⚠️ 已知缺口(见 §8)**:`Interpret_Locale` **没有正式回归测试**(`test.py` / `Tests/*.yml` 里没有用例)。
> 现有验证全部来自一次性探针脚本(未跟踪、不在测试套件里):
> `ScratchOpenModuleProbe.thy`(assert 门)、`ScratchInterpNSubgoals.thy`(义务恒为单谓词)、
> `ScratchStandardTac.thy`(tactic 选型)、`ScratchOpenModuleRoundtrip.thy`(P0 往返)、
> `ScratchP05Unfold.thy`(P0.5)、`ScratchP1Unfold.thy`(**P1 内核 unfold=true 端到端**)。

---

## 0. 审批状态(务必先看)

**用户已明确批准:**
- 语义 = Interpret;命令名 = `Interpret_Locale`;权限 = planner+worker 都能调、义务可委派;
  qualifier 撞名 = 可重试的 op 失败,消息(定稿):**`Qualifier "<q>" is already used in this proof. Pick a fresh one.`**
- **schema = `{thought, qualifier, locale, instantiations}`**(2026-07-12 定稿):`locale` = locale 名字(**结构强制单实例**);
  `instantiations` = 数组 of `Instantiation{name, value}`(复用 `cc_edit.jsonc:587` 的 `$def`,`name`=参数名、`value`=项),
  **可空**(不在 required);始终走 Named(`where …`)全名实例化。文案已定(见 §5)。
  **不含 `defines`/`rewrites`/位置参数/多实例(结构上就没有 → 原 B8、多实例问题消解)。**
- unfold 逻辑放 `proof.ML` 的 `OPEN_MODULE'`,默认 off;**agent 永远 unfold=true**。新参数用
  **record `{auto_unfold_locale: bool}`**(可读性,`OPEN_MODULE' {auto_unfold_locale=true} …`)【B5-record】。
- **C1**:unfold=true 分支报告侧仿 FUN(发 `Goals(goals_of' init_st)`、去掉尾部 `report_goal`)。
- **C2(经终审修正)**:unfold=true 分支用独立 CB,`refine_primitive`/`global_done_proof` 之前先做**单 thm 去壳**
  (`init_goal` 的逆:`Goal.conclude |> conclude_goal |> finalize_goal ctxt`)得**一个** state thm。
  **绝不要 `Conjunction.elim_conjunctions`** —— 那是 FUN 的 *fact 收获* 形状(返回 `thm list`),喂不进只吃单 thm 的 `refine_primitive`。
- **【B1】tactic** = `unfold_locales`(`{strict=false,eager=true}`)+ 无进展回退单谓词。
- **【B2】qualifier in-scope(per-branch)唯一**(放宽先前锁定的"全局唯一")。
- **【B3】qualifier mandatory**(bare `q:`)。
- **【B4】节点 = SubgoalMaker**(复用 Define 机制)。
- **【B5→(b) + C4-translator】**:`OPEN_MODULE''` 改签名收 record,并把 `translator.ML:2479/:2642` 改成
  `{auto_unfold_locale=false}`;§5 impact 表含 translator.ML。
- **C3(facts)**:**≤16** 复用现有 `New_Items → premises`(进 `_fixed_facts_after_me`,bounded,已批),
  successor 作用域自动满足两道显示门;**>16** 发**计数 N** 显示 "N facts available"(+query 提示);**阈值统一 16**(B9 消解)。
  **⚠ 终审修正:`>16` 的计数 N 确实需要 reporter 通道**(`New_Items` 无 int 槽),**不是"多半可免"**——
  见 §4.3:克隆现成 `DROPPED_INSERTION_FACTS` 模板的**四个改点**(含**必须加白名单**,否则被 `agent_server.ML:274` 静默丢)。
- **C7**:qualifier 唯一性在 **Isabelle/ML 侧**做,用 `Proof_Data(Symtab.set)`(§6.4)。
- **C9**:cache key 不含 qualifier(§6.5)。

**设计决策已全部批完。仅剩:**
- 【极小】`Instantiation` 复用共享 `$def`(默认 a,原样复用)vs 本工具单开带描述变体(b)。默认走 a。
- 【待写文案,实现期再批】`prompts.py` 用法说明;qualifier 撞名失败消息;两个未来交互(缺 instantiation 补全 / parse 失败提示)的措辞。用户可见文案不自拟。
- 【文档边界】仅保证顶层 `lemma … by aoa`(嵌套 context 未验,将来补测放宽)。

**缺参补全交互:马上会做(用户 2026-07-12);因此 `instantiations` 描述保持 "…you will be asked for any that are missing" 不变。**
locale 表达式 parse 失败 → 也规划 raise 交互让 agent 改。在交互到位前,缺参/parse 失败暂走**可重试 op 失败**。

---

## 1. 执行摘要

- **能力已存在于内核**:`proof.ML` 的 `OPEN_MODULE` 就是 locale interpretation(解析 `Parse_Spec.locale_expression`,
  witness 义务压块,证完 `Locale.add_registration` 注册并注入定理)。已注册进 `CMDS`(`proof.ML:5826`)。
- **断点在 agent 语言层**:AoA 走结构化命令 ADT,该 ADT 无 interpret 构造子;`model.py` 无 `@proof_operation`;无 schema。
- **工作量 = 接线 + 内核**:向上暴露 + 一个默认-off 的 `unfold` flag(§4.1)+ 一条 facts 名字 reporter 通道(§4.3)。
- **核心设计**:interpret 义务**恒为单个不透明谓词 `L args`**(实测,§3);agent 路径**主动 `unfold_locales`** 展成
  叶子假设,逐个报告为可证/可委派子目标;**unfold=true 分支 = 完整仿 FUN 延迟块**(C1+C2)。

---

## 2. 实测结论

| 验证 | 环境 | 结论 | 脚本 |
|---|---|---|---|
| assert 门 | Main | `by aoa` 类 proof/method context 过 `Local_Theory.assert`,`interpret_cmd` 能建 Proof.state | `ScratchOpenModuleProbe.thy` |
| 义务结构 | Main | 单 locale interpret(2/3 假设、含继承)**恒 1 个 subgoal = 谓词 `L args`**,不调拆分 tactic | `ScratchInterpNSubgoals.thy` |
| P0 往返 | Minilang | `OPEN_MODULE probe:` → 义务 → HAMMER → 注入 `probe.*` → `APPLY (rule …)` 闭合 | `ScratchOpenModuleRoundtrip.thy` |
| P0.5 unfold | Minilang | `APPLY unfold_locales` 展叶子 `0<1`,`0<2` → 逐个证 → `d.bp/d.dfoo/d.derived_axioms` 注册可用 | `ScratchP05Unfold.thy` |
| tactic | 官方+Main | `unfold_locales`(`{strict=false,eager=true}`)降到叶子;`intro_locales` 停父谓词;`standard` 启发式不用 | `ScratchStandardTac.thy` |

> **⚠️ P0.5 的盲区(评审 C1/C2 揭示)**:P0.5 用的是**手动 `APPLY unfold_locales`**(走 Minilang 正常
> tactic+收口路径),**没**验证 unfold flag 的**内核内部**组合(OPEN_MODULE 自身 `init_goal` 包装 + 复用 MAGIC-CB)。
> 所以 unfold=true 的内核实现(§4.1)**必须在 P1 端到端重验**,尤其谓词展成 HOL 结构化(合取)叶子的 locale。
> 另:仅覆盖顶层 `lemma … by aoa`;嵌套 `context begin`/更深 proof 未验(AoA 标准用法不受影响)。

---

## 3. 语义(锁定:Interpret)与义务结构

`Interpret_Locale`(内核 `OPEN_MODULE`)≈ Isar `interpret expr`:实例化 → witness 义务成子目标块 → 证完
`MAGIC` CB 做 `global_done_proof` + `Locale.add_registration` + 注入定理。

**关键事实(实测)**:单 locale 的 interpret 义务**恒为 1 个 subgoal = 谓词 `L args`**(不是 N 个拆开的假设;
`OPEN_MODULE'` 压 raw `#goal (Proof.raw_goal ps)`,不调拆分 tactic)。→ 评审首轮"多假设→多 subgoal→崩溃"顾虑
**证伪**;我们**主动** `unfold_locales` 把 `L args` 展成叶子假设(§4),故"多目标"是**设计**而非意外。唯一天然 >1
谓词的是**多实例**表达式 `L + M`(罕见,倾向只支持单实例)。

---

## 4. 内核改动

### 4.1 `unfold` flag —— `proof.ML` `OPEN_MODULE'`,默认 off,agent 恒 true

**归属 proof.ML(非 agent.ML)**:unfold 依赖 `ps`(interpret 的中间 `Proof.state`,只活在 `OPEN_MODULE'` 内),
且"压栈目标"须与"CB 里 `global_done_proof` 的 state"来自同一展开后的 `ps'`。

**flag 是一个开关、绑一整套。`unfold=true` 分支 = 完整仿 FUN 延迟块**(`proof.ML:5296-5353` 为模板):

- **背景:两层保护壳**。栈里 `st` 有 ① Isabelle 的 `Goal.init`(`#C`)② Minilang 的 `init_goal`=`iso_atomize`+`protect_goals`
  (把每个子目标包进 `Minilang.GOAL`)。Minilang 的 `goals_of'`/`num_goals_of'`(`proof.ML:567-602`)**靠走 `Minilang.GOAL` 链**
  数/取子目标;**未包装的多子目标链会 `raise BROKEN_INVARIANT`**。所以展出 N 个叶子后**必须 `init_goal` 包装**。
- **【C1,已批准】报告侧仿 FUN**:发一次 `get_reporter () (Goals (goals_of' init_st))`(报 N),**且 return tuple
  时不 `|> report_goal`**(现有尾部无条件 `|> report_goal`(`proof.ML:4911`)若保留会双发 Goals →
  `model.py:1869 raise InternalError`;若只留它则报 1 → SubgoalMaker 只开 1 子节点装 N 叶子 → 假完成)。
- **【C6 终审修正】N=0 的计数必须取自 `num_goals_of'`,不能取 `length (goals_of' …)`**:已解状态下
  `goals_of'` 返回 `[True]`(长度 **1**)而 `num_goals_of'` 返回 **0**(`proof.ML:567-602`)。若按长度上报,N=0 会开出一个
  **幻影已完成子节点**。→ N=0 时上报 `Goals []` / 计数 0;块仍照常压、照常 `END`(触发 CB → 注册),只是容器为空。
  **内核不特判 N=0(统一压块)**,配合 §6 模型侧的无条件开块/收尾,N=0/1/N 三种情形统一。
- **【C2,已批准 + 终审修正】CB 侧独立**:unfold=true 用**独立 CB**,`refine_primitive`/`global_done_proof` **之前**先
  **单 thm 去壳**(现有 CB `proof.ML:4888-4890` 无此步,因当前 push 未包装;直接复用会把 protected 态 thm 喂进 refine → THM 异常):
  ```
  val st' = Goal.conclude raw_st' |> conclude_goal |> finalize_goal ctxt   (* init_goal 的逆,得【一个】state thm *)
            |> singleton (Proof_Context.export ctxt' ctxtp)
  val ctxt'' = Proof.refine_primitive (K (K st')) ps' |> Proof.global_done_proof   (* 注册由 interpret 自己的 after_qed 触发 *)
  ```
  **绝不要 `Conjunction.elim_conjunctions`**:它返回 `thm list`,是 FUN/HAVE 的 *fact 收获* 形状;而 OPEN_MODULE 的 CB 是
  **refine 状态**形状,只吃**单个** solved state thm。并引 `ps'`(展开后)非捕获的 `ps`。
  确切去壳组合子在 P1 端到端验(§2 盲区)。
- **【B1,已批准】tactic** = `unfold_locales` = `Locale.intro_locales_tac {strict=false, eager=true}`;**无进展兜底**:
  施后比较目标是否变化,未变(仍 `L args`)则回退单谓词路径。
- **unfold=false 老分支**:压单谓词、尾部 `report_goal`、现有简单 CB,**一字不改**(裸 REPL / 文本 CMD / translator 走这)。

形状(threading 一个默认-off record `{auto_unfold_locale: bool}`)—— **【C4 终审修正】签名保持 `expr` 单参**:
```
fun OPEN_MODULE' {auto_unfold_locale} interp expr (lthy, HHF (st,items)::SK) = ...
val OPEN_MODULE = timed_OPR 60 o OPEN_MODULE' {auto_unfold_locale=false} interpretation   (* legacy,不变 *)
(* OPEN_MODULE'' 只多收 record;translator.ML:2479/:2642 传 {auto_unfold_locale=false};见 §5【B5(b)/C4】 *)
```
**qualifier 不是独立参数**:它是解析后 `Expression.expression` 里**头实例的 `locale_prefix (string*bool)`**
(`parse_spec.ML:134-137,152-153`,形如 `(l,(p,i))`、`p = (qualifier, mandatory)`)。所有调用者只传 `expr`——若给
`OPEN_MODULE'` 加独立 `qualifier` 参数,**全部调用者(含 translator)编译错且无 qualifier 可传**。
→ C7 检查用的 qualifier 由 `OPEN_MODULE'` **从 expr 头实例内部提取**(guard 空/多实例;单实例 schema 下只查头实例)。

### 4.2 tactic 依据

官方 `locales.pdf` §5、`isar-ref.pdf` §5.7 点名 discharge interpretation 义务用 `unfold_locales`(降叶子)/`intro_locales`(停父谓词);
`unfold_locales` 的 `strict=false`→`TRYALL` 永不抛异常(利于"展开后报告残余")。不用 `standard`(`class.ML:817` 启发式、动态作用域)。

### 4.3 facts 显示【C3 已批准:≤16 进 premises;B9 统一 16】

- **注册无条件、无上限**:`add_registration` 在 `after_qed`(`proof.ML:4807`),独立于 `:4898` 的 items trim;
  by-name / `query` 检索不受限。
- **≤16 条**:**复用现有 `New_Items → items`**(`proof.ML:4901` + `cat_items`)—— 作为 premises 显示、进
  `_fixed_facts_after_me`(**用户已批**;16 bounded,不构成"太多")。这条路的 **successor 作用域天然满足两道显示门**:
  items cat 进**块的结果 state** 向 successors 流 → **块结束后才现**;不进义务子树 → **证义务的 subagent 看不到**。
  **≤16 情形几乎不用改。**
- **>16 条【C3 终审修正】**:当前 `if length local_facts > 16 then []` 全丢、`New_Items` 又**没有 int 槽**,Python 收空
  **不知 N**。→ **必须新增一条带 `int N` 的 reporter 消息**(不是"可免")。**做法:克隆现成的
  `Minilang.DROPPED_INSERTION_FACTS` 端到端模板,把 `packList packString` 换成 `packInt`,共四个改点**:
  (a) ML 的 `Internal` exn + `agent_server.ML` pack 分支;
  (b) **`agent_server.ML` reporter `filter` 白名单加 `=> true`** —— **最易漏**:默认 `Minilang.Internal _ => false`(`:274`)
      会把未列入的消息**静默丢弃**(build/run 均不报错),正是我们对 C5 大声警告过的同类陷阱;
  (c) `agent_packer`;(d) Python `unpack_message` 新 tag + Message 子类(渲染 "N facts available")。
- **阈值统一 16**(不再有 20);显示门由 `_fixed_facts_after_me` 作用域天然保证,**无需 shown_hints / node.age 那套**。

---

## 5. agent 层接线

| # | 文件 | 改动 |
|---|---|---|
| 1 | `Agent/agent.ML` | `command` datatype 加 `INTERPRET of string (*qualifier*) * string (*locale*) * (string*string) list (*instantiations:(name,value)*)`;`check_command` 透传;`interpret_i` 结构化拼 `"<qualifier>: <locale> where n1 = ⟨v1⟩ and …"`(instantiations 空则只 `"<qualifier>: <locale>"`)→ **tokenize+parse**(§5 C5)→ 调 unfold=true 入口。**注意:是结构化拼 where 子句、非拼命令字符串**(不违反 memory)。**⚠ 每个 value 必须 cartouche 包裹,见下【C2】** |
| 2 | `Agent/agent_packer.ML` | `"INTERPRET"` tag + §4.3 的 facts-name Msg |
| 3 | `IsaMini/AoA/model.py` | `Minilang_Operation.INTERPRET` + `@proof_operation("Interpret_Locale")` 节点(§6) |
| 4 | **`tools/cc_edit.jsonc`**(**不是新工具**)+ `mcp_http_server.py` | `Interpret_Locale` 是 `edit` 工具的一个新 **operation 变体**:加一个 `$def`(`"operation":{"const":"Interpret_Locale"}` + `thought/qualifier/locale/instantiations`,复用 `Instantiation{name,value}` `$def`,instantiations 可空;§0 定稿文案),并加入 operation 联合。**分发是泛型的**:`model.py` 的 `@proof_operation("Interpret_Locale")` 会把它注册进 `OPERATION_REGISTRY`,`_edit_tool_logic` **没有** per-op switch,**无需改分发代码**(终审 C7-kill 纠正)。**权限继承 `edit`(planner+worker 按 scope),无需新工具/新权限项。** |
| ~~5~~ | ~~`prompts.py`~~ | **无需**:AoA 不给 proof operation 写 prompt 说明,文档 = 那个 `$def` 的 description |
| **6** | **`translator/library/translator.ML`【C4】** | **:2479/:2642 是 `OPEN_MODULE''` 的 live caller,签名一改就编译错;必须一并处理** |

- **【C4/B5→(b),已批准】签名方案**:`OPEN_MODULE''` 改签名收 record `{auto_unfold_locale: bool}`;把
  `translator.ML:2479/:2642` 改成传 `{auto_unfold_locale=false}`(保持 replay/cached Isar interpret 渲染不变)。
  **translator/replay 路径必须 unfold=false。**
- **【C5,已确认】禁一切"拼 Minilang 命令字符串"的路由**:把 `Interpret_Locale` 拼成 `"OPEN_MODULE d: …"` 文本再
  `parse_cmds (lex_cmds …)` 是**绝对禁止**的——它经 `CMDS`→`OPEN_MODULE_CMD`(`proof.ML:4917`)被**静默锁死**成
  `{auto_unfold_locale=false}`,违背 always-unfold 且 build/run 都不报错。**(通则:AoA 中永不拼接 Minilang 命令字符串,
  见项目 memory。)** `interpret_i` **唯一正道**(照抄 `find_theorems.ML:520-524` 规范写法):
  `Token.explode (Thy_Header.get_keywords' ctxt) Position.none str |> filter Token.is_proper`(`ctxt = Minilang.context_of s`)
  → `Scan.error (Scan.finite Token.stopper (Parse.!!! (Parse_Spec.locale_expression --| Scan.ahead Parse.eof))) |> #1`
  得 raw `Expression.expression` → 直调 `OPEN_MODULE'' {auto_unfold_locale=true} <expr>`。
  **`Token.explode` 是对的**(前提:传 theory 完整 keyword 表 `Thy_Header.get_keywords'` + `filter Token.is_proper`);
  **不要复用 `lex_cmds`**(返回 `Token.T list list` 按命令切分、缺 `+`/`rewrites`、假 position)。
- **【C2 终审,HIGH,必修】每个 instantiation value 必须 cartouche 包裹**:`where n = v` 里的 `v` 走
  `Parse.term = inner_syntax embedded`(`parse.ML:405,269-272`),**只吃一个 outer token**(cartouche/字符串/标识符/数字)。
  而 schema 要 agent 写带类型标注的项(`(0::int)`、`a + b`)——**多 token** → `where n = (0::int)` 读到 `(` 就断,
  **整个 locale_expression 解析失败**;常见输入全废、且 agent 无从自救。
  → `interpret_i` 拼 where 子句时**必须**发 `name ^ " = \<open>" ^ value ^ "\<close>"`(cartouche 是 `embedded` 的首选项,
  `Token.explode` 独立于 keyword 表词法化它,可把任意空格/unicode/符号/类型标注当**一个** inner-syntax token 送进 `Parse.term`)。
  (注:`Have`/`RULE` 用 `Syntax.read_term`(inner syntax)不需引号——interpret 是**唯一**走 outer-syntax 解析的,照抄它们会踩坑。)

> 改任何 `.ML` 后必须请用户重启 REPL server。

---

## 6. model.py 节点建模 + qualifier 唯一性 + replay

- **【B4,已批准 + C5 终审修正】节点 = `SubgoalMaker`,但需专门 override(不能用默认规则,也**不是**复用 Define 的 marker)**:
  - **为什么**:`OPEN_MODULE` **无条件**压 `ENDBLK + MAGIC` 延迟块(`proof.ML:4906-4910`),而**注册(`add_registration`)在 CB 里,
    只有该块被 `END` 收口时才触发**。默认 SubgoalMaker 规则是"`n>1` 才开容器"——**N=1(unfold 后最常见)就不开容器、不发 END**
    → ML 栈上那个 `ENDBLK` 永远没人收 → **CB 不触发 → 注册不发生 → 栈脱节**。
  - **override**:(1) `_should_open_proof_block` **无条件返回 `YES`**(**不是** `YES_AND_CLOSE_PARENT_BLOCK`——该块是内部
    END-bracketed 的,父证明行必须存活);(2) `has_ending_opr = True`、`ending_opr = Minilang_Operation.END()` **无条件**。
    这样 **N=0 / N=1 / N>1 统一**:总有容器、总有 END 收口触发注册。N=0 时容器为空(计数取自 `num_goals_of'`=0,见 §4.1 C6),
    立刻 END → 注册,不产生幻影子节点。
  - **删除**"复用 Define 的 block-opened marker"与"类比 `CaseSplit`":Define 的 marker(Termination / Pat_Completeness)
    对 interpret 语义不对、这里也不发;**不需要任何新 reporter 消息**(块恒存在)。只保留 Define 的**结构类比**
    (块内部、END 收口、父行存活)。
- **完成判定用 `is_proof_finished()`/`unfinished_nodes()`,绝不用 `status`**(#1 gotcha)。
- 每个叶子假设可委派 worker(`subagent`→`_nearest_goal_for_subagent`)——正是 unfold 的收益。
- **facts 渲染**:见 §4.3【C3】(从 close-state harvest,shown_hints 式只显示一次)。

### 6.4 qualifier 唯一性【C7 已批准;in-scope 放宽已批准】

**不维护任何 Python set**(评审 C7:re-refresh 自撞 / amend 撞 / delete 泄漏 / replay 不重填,全是"平行状态同步错")。
改用 **ctxt 即权威**——真相已在 proof-state 的 `Proof.context` 里,且随 ctxt 跨 refresh/amend/delete/replay 自动重建。

用户方案(采纳):**`structure Locale_Interpretation_Qualifiers = Proof_Data(type T = Symtab.set; fun init _ = Symtab.empty)`**,
在 ML 侧动态维护:
```
(* OPEN_MODULE' 开头:检查输入 lthy *)
val _ = if Symtab.defined (Locale_Interpretation_Qualifiers.get lthy) qualifier
        then error (* 文案待定 *) else ()
(* CB 里(close 时):把 lthy 的 set + qualifier 显式搬进 ctxt''(不赌 global_done_proof 保留 Proof_Data) *)
val ctxt''' = ctxt'' |> Locale_Interpretation_Qualifiers.put
                (Symtab.insert_set qualifier (Locale_Interpretation_Qualifiers.get lthy))
```
- **要点1**:close 时才 add;检查读**输入** `lthy`(不含自己的 q)→ 无自撞。
- **要点2**:显式 `get lthy → insert_set → put ctxt''`,保证 Proof_Data 连续。
- **兜底**:`Locale.add_registration` 的 duplicate-fact 报错作最终防线。
- **【C4 终审:qualifier 来源 + 门控】** qualifier **不是** `OPEN_MODULE'` 的独立参数,而是**从 `expr` 头实例的
  `locale_prefix` 内部提取**(§4.1)。且**唯一性检查与 `Proof_Data` 写入只在 `auto_unfold_locale=true` 时执行**——
  legacy(裸 REPL / 文本 CMD / translator replay,均 unfold=false)**既不检查也不改动** `Symtab`,守住"一字不改"。
- **【B2,已批准】** 该方案给的是 **in-scope(per-branch)唯一**(不同分支各用 `q` 互不可见、无歧义),**放宽了先前锁定的
  "全局唯一"**。in-scope 是让无状态方案成立的前提,且语义上更对(facts 只在分支内 in scope)。

### 6.5 replay / cache【C9,已批准】

- **删掉先前"qualifier 应进 cache key"的说法**(评审 C9):cache key 是 `goal_hash`(ML 算,`proof_cache.py:21` 唯一主键);
  qualifier 随 packed op **逐字 replay**(`set_replay_mode`+`proof_opr`),不进 key(进 key 会碎片化缓存且不可实现)。
- 变长叶子块 replay **无需重建 model 树**:N 个叶子随 `unfold_locales` 重执行确定性重现(`INTERPRET; p1; NEXT; …; END`)。
- qualifier 的 `Proof_Data` set 随 replay 重执行**自动重填**(§6.4),无需额外处理。

---

## 7. 已锁定决策汇总

**§0 是权威审批状态**(设计决策已全部批完;正文若有残留旧标签以 §0 为准)。核心:命令名 `Interpret_Locale`;schema `{thought, qualifier, locale, instantiations}`(mandatory bare `q:`【B3】)
+`thought`,不含 `defines`【B8】;tactic `unfold_locales`【B1】;facts 全注册+reporter 分档显示;flag 默认-off、agent 恒
unfold=true、unfold 分支完整仿 FUN(C1+C2);节点 SubgoalMaker【B4】;权限 planner+worker;qualifier `Proof_Data(Symtab.set)`
in-scope 唯一【B2】。

---

## 8. 实现状态

### ✅ 已完成并合入
- **P0 / P0.5**(§2):往返 + `unfold_locales` 拆叶子,真实 `OPEN_MODULE` 路径实测。
- **P1 内核**(`library/proof.ML`、`Agent/agent_server.ML`、`translator/library/translator.ML`):
  `{auto_unfold_locale}` record(默认 off,legacy 一字不改)、unfold 分支仿 FUN(thm 层施 `unfold_locales` →
  `init_goal` 包装 → 发一次 `Goals` 且**不** `report_goal`;N=0 发 `Goals []`)、**独立 CB 单 thm 去壳**
  (`conclude_goal |> finalize_goal`)、`Proof_Data(Symtab.set)` qualifier 唯一性(门控在 flag)、
  `INTERPRET_FACTS_COUNT`(pack tag 19 + **reporter 白名单**)。
  **§2 的盲区(内核内部 `init_goal` + MAGIC-CB 组合)已用 `ScratchP1Unfold.thy` 端到端验证**:
  `derived 1 2` 拆成 `0<1`/`0<2` → 逐叶证 → CB 去壳 → 注册 → `d.dfoo` 可用 → 闭合;qualifier 重用被拒。
- **P2 接线**(`Agent/agent.ML`、`agent_packer.ML`、`IsaMini/AoA/model.py`、`tools/cc_edit.jsonc`):
  `INTERPRET` xcmd(双向 pack)、`interpret_i`(拼 `where` + **cartouche 包裹** + `Token.explode` 配方)、
  `@proof_operation("Interpret_Locale")` 节点(**无条件开块 + 无条件 END**)、`edit` 工具的 operation 变体、
  `>16` facts 计数渲染。**355/355 既有测试通过,无 golden 变更。**

> 一个比设计更省的实现发现:`unfold_locales` 在 **thm 层**施加即可(不必 `Proof.refine` 动 `ps`)——
> 展开前后**结论相同**,解完的 thm 可直接喂 `refine_primitive ps`,所以**不需要 `ps'`**;且无进展时
> `init_goal` 对单子目标幂等,**兜底自动成立、无需特判分支**。

### ⚠️ 仍未做(真实缺口)
1. **没有正式回归测试** —— `test.py` / `Tests/*.yml` 里**没有 `Interpret_Locale` 用例**。现有验证全靠一次性探针
   (见文首)。补测要新建 `.thy` fixture + golden YAML,**建 golden 须用户批准**。
   完整 agent 路径(`root.fill` → RPC → ML)**从未跑过**这个 operation。
2. **N=0**(无假设 locale)与 **no-progress 回退** 未实测。
3. 两个交互(`instantiations` 缺参补全 / locale 表达式 parse 失败)——用户规划,尚未开始。
4. 限制:仅保证顶层 `lemma … by aoa`(嵌套 `context begin` 未验)。
5. P4 真实 benchmark 端到端未跑。

---

## 9. 评审留存 / 删除

**存活并已并入**:C1(报告仿 FUN,§4.1)、C2(CB 拆壳,§4.1)、C3(facts close-state harvest,§4.3)、C4(translator 签名,§5)、
C5(禁 parse_cmds,§5)、C6(reporter 四改点,§4.3)、C7(Proof_Data 唯一性,§6.4)、C9(删 cache-key 误述,§6.5)。

**判为低质量、已删除**:
- 首轮 C7(多实例 qualifier 只限首实例):按单实例处置,已注明。
- 首轮 C9 / 二轮 C8(ROI / 叶子爆炸无上限):非技术失败;叶子数=每条 assumes 一个非每层一个;上限与 always-unfold 冲突。

---

## 10. 风险 / 提醒

- 改 `.ML` → 必须重启 REPL server。
- 渲染/行为变化动 golden YAML → 跑 test、看 `.diff`、**改 golden 前须用户显式批准**。
- 共享工作树:禁 `git stash/checkout/reset --hard/clean`;`isabelle build` 禁擅自加 `-c`。
- 用户可见文案(prompt/error/失败消息)不得自拟,只出脚手架让用户选。
- unfold 对简单 locale 是"增强"(HAMMER 也能直接证谓词),对深/强假设 locale 可能成"必需"——恒 unfold=true 两种都覆盖。
