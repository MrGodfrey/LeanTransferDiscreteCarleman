# T218 / C234 独立本机验收

- checked_sha: `b41b6861b988e758d026fed32f5d5802e411b636`
- mathematical_base: `79151186853d57b5e937851b51ace47c05a4e7ff`
- reviewed_at: `2026-10-20T05:17:34+00:00`
- reviewer: 独立本机 Agent `accept_spatial_foundations`
- result: **PASS，17/17 显式声明（10 定理、5 定义、2 缩写），无阻断缺陷。**
- scope: **AUXILIARY；C234 可按此范围验收，原文 17/26 不变。**

直接读取固定 Git 对象中 `CoefficientJetForm`、`HigherCoefficientForm` 全部源码、17 项完整 raw 类型、公理、固定分析/MATH_SPEC/C234/T218 清单，并对照 `paper/main.tex:2615–2652` 的 `eq:coefficientform`、2635 行的上界步骤及 362–365 行 `eq:unshiftedformbound`。本批构造真实系数形式与统一加权上界；不把该上界或 OriginalForm 包装等同于完整 Proposition A.1。

## 数学审查

1. **全部指标和真实连续双线性形式。** `MultiDerivativeIndex d m = Σ k:Fin(m+1), Sym(Fin d) k.val`，包含所有阶数 0…m，每个无序多指标恰一次。`jetScalarComponent` 是既有真实弱字段与 Euclidean 分量投影的 CLM 复合。两层全有限和保留任意阶数间的交叉项，包括非对角、低阶、零阶系数；没有最高阶或对角筛选。`coefficientJetForm` 由原 `BoundedMultiplier.continuousLinearMap`、实际 `innerSL ℝ`、`bilinearComp` 及有限和构造，连续性来自这些实际 CLM，而非输入目标估计或有限维自动连续性。局部 `ContinuousAdd` 仅取现有 `IsTopologicalAddGroup` 的字段，没有更换 jet 拓扑/范数。
2. **真实积分及可积性。** `coefficientJetForm_apply` 明确是 `⟨aαβ Dβu,Dαv⟩`。原 `BoundedMultiplier` 只包含真实 a.e. 可测性、有限非负 bound 及 a.e. 绝对值界；其 `memLp_smul` 内部证明 aαβDβu∈L²。因此两因子的内积密度真正可积；结合实际 `map_ae`，原积分密度与它 a.e. 相等。积分定理逐项展开 `L2.inner_def` 并按该身份改写，不以未证可积的 Lean 积分零约定代替原积分。所有代表身份只在 a.e. 意义下使用，没有赋予 L² 等价类任意点值。
3. **真实系数对称。** `hsym` 为每对 α、β 的原系数 a.e. 相等，不要求其 bound 元数据相同。证明先交换双和指标，再用真实 L² 乘子相等、自伴配对 `inner_map_left` 和实内积交换。该步骤同时覆盖任意不同阶数、不同分量；未预先假设最终形式对称。
4. **原 N 范数及统一常数。** 已直接展开 `weightedNorm`：平方是 `Σk (q^(m−k) ‖w D^k u‖₂)²`，其中每阶为全部 Sym 分量的 Euclidean L² 场。真实投影分量范数≤全场范数，且 q≥1 给 q^(m−k)≥1，故任意单分量的加权 L² 范数≤Nq,w。对每对 α、β，`inner_inverse` 使用实际 wξ=1 将原配对精确写为 `⟨w(aαβDβu),ξDαv⟩`；标量乘子交换后仅应用系数 bound，再用 L² Cauchy–Schwarz。最终常数恰为 `C_a=Σαβ bound(aαβ)`，只依赖预先固定的有限系数族和 d/m，不含 q、w/ξ 的 sup 界、权导数、状态或时间长度。此显式 C_a 在任意权/符号/时间参数选择之前固定；正负指数和逆权均可代入同一结论，没有符号限制或缩小允许权族。q=1、零系数、m=0、d=0、空域也无除法或非法指标。这里只需非负 C_a；如后续接口要求严格正常数，可统一放大为 C_a+1，不影响本结论。
5. **同一原 H₀ᵐ。** 已重新读取 `HigherDirichletSpace`、`SobolevHilbert`、`ConformingHilbert` 及分量平方范数公式。`HigherDirichletEnergy` 是已验收原测试集合 Hᵐ 闭包的完整 Hilbert 实现；`higherDirichletToJet` 是同一状态的真实射流，不限制为光滑状态。`higherDirichletEnergy_norm_sq` 先展开所有阶 L² 场的平方和，再用 `Fintype.sum_sigma` 和 `derivativeField_norm_sq`，得到全部 Dαu 的 L² 范数平方之和，无排列重数或隐藏等价常数。限制形式精确继承同一系数、积分、对称性及相同 C_a 的上界；未把 jet 的积范数误认作这个平方和范数。
6. **原假设与剩余范围。** `higherCoefficientOriginalForm` 内部供应原 H₀ᵐ 的 Hᵐ 闭性、L² 稠密性和 Sobolev 包含；实际 form 就是上述有限积分和。输入 `hcoer : ∃ c>0, ∀u, c‖u‖²≤a(u,u)` 明确对应原文给定的 coercivity，未从有界或对称性错误推出正定。系数不要求经典/弱导数，更没有把原 W^{2m,∞} 系数擅自替换为 C∞。这部分结论只需要有界可测系数，因此是原系数假设所需的零阶形式步骤；本批没有构造一般系数的 W^{2m,∞} 高阶弱乘法接口。关联算子完整域等式、H^{2m} 图界、交换子、加权下界均未在此得到，也未作为本批上界的新前提。

## 17 项完整清单

源码定位相对于固定版本 `Carleman/Spatial/`；raw 行号指 `/tmp/carleman-t218-coefficient-form-local-axioms.txt`。均已核对完整类型和实现。

| 固定源码定位 | 完整声明 | raw 起始行 | 逐项结论 |
|---|---|---:|---|
| CoefficientJetForm:14 | `Carleman.MultiDerivativeIndex` | 40307 | PASS；Σ 阶数 0…m 与全部 Sym 无序多指标，含零阶及混合导数。 |
| CoefficientJetForm:23 | `Carleman.jetScalarComponent` | 40309 | PASS；真实 fieldCLM 与 scalar component CLM 复合，未另选导数。 |
| CoefficientJetForm:27 | `Carleman.coefficientJetForm` | 40315 | PASS；所有 α、β 的实际乘子 L² 配对组成连续双线性形式。 |
| CoefficientJetForm:32 | `Carleman.coefficientJetForm_apply` | 40322 | PASS；展开后系数作用在 Dβu，另一因子为 Dαv，顺序与原文相同。 |
| CoefficientJetForm:39 | `Carleman.coefficientJetForm_integral` | 40329 | PASS；真实 L² 内积及乘法的 a.e. 身份给原完整系数积分。 |
| CoefficientJetForm:56 | `Carleman.coefficientJetForm_symmetric` | 40339 | PASS；仅用原 a.e. 系数对称、真实乘子自伴及有限双和交换。 |
| CoefficientJetForm:73 | `Carleman.jetScalarComponent_weighted_le` | 40346 | PASS；任意分量由完整原 Nq,w 控制，所用 q≥1 明示。 |
| CoefficientJetForm:81 | `Carleman.coefficientJetForm_weighted_upper` | 40353 | PASS；互逆权配对精确消去，常数为固定全部系数 bound 之和。 |
| HigherCoefficientForm:18 | `Carleman.HigherDirichletEnergy` | 40365 | PASS；原 H₀ᵐ 在实际 Sobolev Hilbert 空间中的载体。 |
| HigherCoefficientForm:21 | `Carleman.higherDirichletToJet` | 40369 | PASS；同一状态的全部原弱字段，真实连续线性映射。 |
| HigherCoefficientForm:25 | `Carleman.higherDirichletEnergy_norm_sq` | 40374 | PASS；能量范数平方精确等于全部 Dαu 的 L² 范数平方和。 |
| HigherCoefficientForm:33 | `Carleman.higherCoefficientForm` | 40378 | PASS；同一系数形式限制到完整原 H₀ᵐ 能量空间。 |
| HigherCoefficientForm:38 | `Carleman.higherCoefficientForm_apply` | 40385 | PASS；限制形式与原射流形式精确相等。 |
| HigherCoefficientForm:43 | `Carleman.higherCoefficientForm_symmetric` | 40393 | PASS；全 H₀ᵐ 状态的原系数对称形式。 |
| HigherCoefficientForm:49 | `Carleman.higherCoefficientForm_integral` | 40401 | PASS；原受限 Lebesgue 测度上的完整系数积分身份。 |
| HigherCoefficientForm:57 | `Carleman.higherCoefficientForm_weighted_upper` | 40413 | PASS；同一常数给全 H₀ᵐ 状态及任意 q≥1 互逆权上界。 |
| HigherCoefficientForm:67 | `Carleman.higherCoefficientOriginalForm` | 40427 | PASS；内部供应真实闭/稠密 H₀ᵐ 与连续对称形式；仅保留原 coercivity 输入。 |

## 本地证据和依赖边界

- 独立枚举 `/tmp/carleman-t218-local-source-manifest.txt` 的 **1007** 项，集合完整且无重复，覆盖固定提交全部受检 Lean 源及三项工具链配置；逐项 SHA256 全部匹配实际 Git blob。清单 **109227 bytes**，SHA256 `75bb46a284321d0238e38ef792e6eefa8190af363caa256204741530f412b02c`。原稿 SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef` 未变。两新模块实际被固定 root 导入，17 项显式 `#check @` 和 `#print axioms` 齐全。
- 实际 import 递归闭包为 **99** 个 Carleman 模块；其中 **97** 个旧模块与 mathematical_base 的 Git blob 均不变，其余两项正是本批新模块。相关 T216 原空间已由冻结报告提交 `061e2229186295742d29c00397e0b7a1ed480e2e` 接受；本次直接读其被调用定义和证明，并全文读取固定 T217 报告（reviewed_at `2026-10-20T05:07:09+00:00`），未重复审计无关历史。用于本批的乘子、原 N 范数、分量界、内积消去、Hilbert 范数和 OriginalForm 实际字段均另行核对。
- `/tmp/carleman-t218-local-evidence.json` 的 checked/source SHA 均为本报告固定版本，source=local、status=PASS；完成时间 `2026-10-20T05:14:26.116750+00:00`。实际 `lake build Carleman`、`lake env lean tools/CheckAxioms.lean` 记录均 exit 0。已读取 `target-build.log` 的两个目标成功和 **3241 jobs**，`build.log` 的全库 **4243 jobs** 成功；`axioms.log` 为 **0 bytes**。本次复核现有真实执行证据及其源绑定，没有声称另行重建旧闭包或查询远端 CI。
- 固定 raw **3107089 bytes**，SHA256 `6cbdfd58a2ac8278bb9c49df088a5d60e4ba3b6fbdd09773eb04cefba6408914`，与 evidence/固定登记相同。17 项完整类型和递归公理输出逐项读取；独立扫描 raw 的 **3617** 条显式公理记录，全部仅含 `propext`、`Classical.choice`、`Quot.sound` 或无公理。另检查固定 `CheckAxioms.lean` 的 `privateToUserName` 全命名空间遍历及 `collectAxioms` 白名单机制，末行实际为 `Axiom audit passed for all 9241 Carleman declarations.`。**9241** 为完整递归审计数，区别于显式打印数；无 sorryAx 或新增数学公理。工具链固定 Lean **4.35.0**，mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`。

本报告仅接受本批原系数形式及统一加权上界。没有发现数学或证据缺陷；保持 AUXILIARY / 17 of 26，不提升完整 Proposition A.1。正文和 reviewed_at 签发后冻结；仅单文件提交本报告，不修改数学、台账、原稿或未来草稿，不 push。
