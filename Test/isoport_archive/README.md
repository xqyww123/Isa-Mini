# isoport 原型档案（P24 归档，2026-08-08）

iso-atomize/rulify 移植（`MY_OBJECT_LOGIC_PLAN.md` 第二部分）2026-08-06 那一轮原型实验的
存档。原件在易失的 scratchpad（`…/scratchpad/isoport/`）里放了两天，按 P24 决议
（用户 2026-08-08：归档到本目录）抢救于此。

## 内容

- **`patch_isamini_*.diff`** —— 各原型树相对 `isamini_base`（当时的干净 Isa-Mini 拷贝）的
  源码差分。六份 553 MB 的完整树没有进仓库，差分是它们的全部源码增量：
  - `patch_isamini_lab3.diff` —— **最后一版原型**（归档时用
    `diff -ru --exclude='*.proof-cache*' --exclude='__pycache__' --exclude='*~'` 现场生成，
    评审 A4 发现它此前从未存盘）；
  - `patch_isamini_lab.diff` / `patch_isamini_lab2.diff` / `patch_isamini_new.diff` /
    `patch_isamini_basefix.diff` —— 早期各版（lab / basefix 两份也是归档时补生成）。
- **`out_{BEFORE,AFTER,LAB2,LAB3}_Iso_*.txt`** —— §10 对拍矩阵各格的输出
  （Iso_A…E / Iso_Isar × 各引擎）。
- **`reg_REG{BASE,NEW,LAB2,LAB3}_RT_*.txt`** —— 回归 theory（RT_*）在各引擎下的输出。
- **`*.sh` / `*grid.log` / `reg*.log`** —— 当时的驱动脚本与运行记录。
- 其余 `*.txt`（`ctx_*` / `e2e*` / `leak*` / `ol*` / `objatom` / `goalside_*` 等）——
  探针输出。

## `out_LANDED_Iso_*.txt`（2026-08-08 落地验收列）

落地当日在**已切换的工作树**（提交 `51c0157`）上用 `corpus/Iso_*.thy` 重跑的
候选列（引擎 = `iNet_Thm_Collection` + `Merely_Rewrite` + `My_Object_Logic`,
即真正落地的形态）。十格全过：A/A2/B/C1/C2/E 六格由 BEFORE 列的 OBTAIN 崩溃
转为成功,`##RESULT` 与 LAB3 列逐字同；C0/D/E0/Isar 与 BEFORE 列逐字同。
上文对 LAB3 列「不是落地形态」的告诫不适用于本列。

## `corpus/`（2026-08-08 落地当日补档）

对拍矩阵与回归的 **theory 源码**（`Iso_*.thy` 32 件、`RT_*.thy` 12 件,取自
`isamini_base` 原型树顶层）。此前只归档了输出与差分,源码漏归;落地验收时
从尚存的原型树抢救于此。`RT_*` = 当时 `Test/` 对应 theory 改名 + import 去
session 限定(`Minilang.Minilang` → `Minilang`),供 `process_theories -D <树>` 跑。

## ⚠️ 使用告诫（评审 2026-08-08，A4）

1. **lab3 不是落地形态**：它用 `Named_Thms` + 手写 struct 遍历 + `Phi_Conv` 名 +
   `iso_engine` 四引擎开关；落地形态是 `iNet_Thm_Collection` + `Merely_Rewrite` +
   `My_Object_Logic`（第二部分 I9/I10/W8）。**对拍矩阵的"改前"列与语料可直接复用，
   "候选"列必须用新引擎重建。**
2. 本档案的全部证据采集于 2026-08-06 的树——**早于** FUN 延迟 pat-completeness 块
   （`530281e`）进树；对该路径（及 FUN 交互式终止、INTERPRET）覆盖为零，
   见第二部分评审补丁（C3/F4）。
