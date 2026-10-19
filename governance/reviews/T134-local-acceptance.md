# T134 / C150 独立本机验收

- checked_sha: `3d418d76a4959a094dcd26d2d157c213f297531d`
- base_commit: `c3ea3c03352de258d944bf495695b31bcef3f3b0`
- reviewed_at: `2026-10-19T07:39:28+00:00`
- reviewer: `/root/accept_spatial_foundations`，独立本机验收 Agent。
- result: **PASS**；axiom_check: **PASS**。
- scope: **AUXILIARY**。可将 C150 在本固定版本登记为 REVIEWED；P023 / `prop:analytic-realizations` 不提升，原文完成数保持 **14/26**。

本报告直接读取固定 Git 对象中的四模块、六项实际展开类型、关键证明依赖、原稿、MATH_SPEC、T134 分析和台账；独立查询同 SHA 正式 CI，独立下载并比较原始证据。执行者说明与 CI 不替代数学核查。仅写本报告，未修改实现、台账、原稿或根导入，未提交或推送。后续工作树和动态 `.ci/axioms.txt` 均不属于本批证据。

## 全部六项声明

下表行号均属于 checked_sha，文件均位于 `Carleman/Spatial/`。声明 JSON 与固定 C150 台账逐项相同；模块 JSON 对应四个实际模块。固定 `Carleman.lean` 导入全部四模块，`tools/CheckAxioms.lean` 对六项均有 `#check @...` 与 `#print axioms ...`，原始证据包含六项展开类型。

| # | 完整声明 | 固定源码位置 | 逐项结论 |
|---|---|---|---|
| 1 | `Carleman.exists_spatialTest_eq_one_on_compact` | `InteriorSmoothCutoff.lean:16` | PASS。开 S 与紧 K⊆S 内部供应真实 C∞ 紧支截断，拓扑支持包含于 S，K 上严格等于 1。 |
| 2 | `Carleman.cutoff_fderiv_eq` | `CutoffMollifierGradient.lean:16` | PASS。η 在开 T 上等于 1 时，任意实际 F 的 ηF 与 F 在每个 x∈T 的邻域相等，故实际 Fréchet 导数相等。 |
| 3 | `Carleman.cutoff_mollifier_gradient_tendsto` | `CutoffMollifierGradient.lean:24` | PASS。实际截断卷积的一阶 L² 分量限制到 T 后强收敛到原完整 H¹ jet 的对应分量；没有输入原状态 H² 或跨边界弱链。 |
| 4 | `Carleman.IsWeakNegativeLaplacian.restrictSubdomain` | `WeakPoissonRestriction.lean:13` | PASS。任意原 H¹ 弱 Poisson 解限制到开内域后满足同一载荷的限制；测试转移及 L² 内积均精确。 |
| 5 | `Carleman.exists_interior_H2_of_cutoff` | `InteriorPoissonRegularity.lean:18` | PASS。先固定截断并选 M，再量化全部原 H¹ 解与 L² 载荷；实际梯度极限、全部测试身份和最终 Hessian 分量界构造同一原一阶 jet 的 H² 扩充。 |
| 6 | `Carleman.exists_interior_H2_bound` | `InteriorPoissonRegularity.lean:59` | PASS。只保留开 S/T、closure T 紧且包含于 S，内部构造截断；输出完整一阶截断等式、实际负 Laplacian 等于 f|T，及保留 Sym 维数因子的 Hessian 界。 |

## 原文对应、对象及量词

固定 `paper/main.tex:2659`–2664 的 `prop:analytic-realizations` 要求实际 Dirichlet Laplacian 的 A1–A3；其证明通过 Grisvard Theorem 3.2.1.2 得到全域 D(A)=H²∩H¹₀ 及椭圆估计。T134 证明其中所需的内部正则性工具，尚不能替代这项全域结论。本验收线程此前直接查看的 Grisvard 印刷 147–149 页仍只作为该整体证明路线的参照；本批判断来自实际新证明与依赖，未把该书结论作为 Lean 新公理。

实际空间是 `SpatialCoordinates d = EuclideanSpace ℝ (Fin d)`，测度是 volume.restrict S/T。原 `WeakSobolevJet` 的每个字段为实际 L² 类，所有相邻阶字段由全部原 `SpatialTest` 的分布导数身份连接；二阶字段在 `EuclideanSpace ℝ (Sym (Fin d) 2)` 中。`IsWeakNegativeLaplacian u f` 明确要求每个原紧支 C∞ 测试 φ 满足 ⟨∇u,∇φ⟩=⟨f,φ⟩，不是待证结论的抽象替身。

第 6 项的完整前提为：任意 d，S、T 开，closure T 紧，closure T⊆S。随后存在 M≥0，再量化所有 u∈H¹(S)、f∈L²(S) 与原弱方程。结论 v∈H²(T) 满足
`truncate₁ v = restrictSubdomain u`、
`negativeLaplacian v = subdomainLp f`，以及

```text
‖field₂ v‖² ≤ card(Sym(Fin d), 2) ·
  [M (‖f‖ + 2 ∑ᵢ ‖Dᵢu‖ + ‖value u‖)]².
```

这里的一阶等式同时保留原 value 和全部梯度字段，而非仅选择另一个具有相同载荷的解。M 可依赖固定 d、S、T 及内部选定的截断，但先于 u/f；核序号、候选 Hessian、测试与收敛资格均不再是最终输入。未添加 S 有界、凸、连通、边界光滑、u∈H¹₀、u∈H²、载荷更高可积性或预设估计。

## 截断与新增 mathlib 依赖

第 1 项先由 `IsCompact.exists_cthickening_subset_open` 取得 δ>0 及 cthickening δ K⊆S，再对开 thickening δ K 与闭 K 调用实际 `exists_contDiff_support_eq_eq_one_iff`，取光滑阶 ∞。所得函数的普通支持精确等于该开增厚，K 上精确等于 1；其拓扑支持为该开增厚的闭包，包含于闭增厚。有限维 Euclidean 空间为 proper space，紧 K 的有限闭增厚紧；故真实拓扑支持紧且仍在 S 内。

已直接核对固定 mathlib `Geometry/Manifold/PartitionOfUnity.lean:753` 附近的光滑 Urysohn 构造及 790 行的 ContDiff 版本：通过两个非负光滑函数的 f/(f+g) 构造，分母在每一点严格为正。它给实际函数及光滑性、支持和 1 水平集身份，不是假定截断存在的自定义公理。其有限维条件由实际 EuclideanSpace 内部实例满足，无额外几何输入。另核对 `Topology/MetricSpace/Thickening.lean:283`、293、426 附近的紧闭增厚、闭包包含和正缓冲结论。

第 2 项没有无根据套用乘积求导：先由 T 开及 η=1 得 ηF=F 在 x 的邻域最终成立，再用 `EventuallyEq.fderiv_eq`。这对任意 F 合法；应用处 F 是实际光滑卷积。最终 K=closure T，故每个 x∈T 均具有需要的开邻域。

## 原梯度强极限与真实二阶字段

令 φₙ=η·(u⁰*κₙ)，其中 u⁰ 是原 value 的实际 L² 零延拓；κₙ 是现有实际非负、单位积分光滑核，外半径 2/(n+1) 趋于 0。`mulSmooth` 保持原 SpatialTest 的 C∞、紧支持及支持在 S 内；φₙ 的全部真实导数均先有 L² 资格。

第 3 项先令 g=Dᵢu，使用真正的全空间 L² 卷积强收敛
`spatialMollificationLp n (zeroExtendLp g) → zeroExtendLp g`，再通过实际有界线性限制映射传到 T。目标 L² 类与原 restrictSubdomain u 的第 i 梯度分量严格一致：证明逐步使用零延拓在 S 上的 a.e. 身份、限制的 a.e. 身份、T⊆S 的测度单调性，以及分量抽取与限制交换。

剩余识别不是把 u⁰ 当作全空间 H¹ 状态。固定 η 的紧支持与 S 开通过 `compact_mollifier_eventually_inside` 给某个最终阈值，此后所有 x∈tsupport η、y∈tsupport κₙ 均满足 x−y∈S。对 x∈T，η(x)=1 保证 x∈tsupport η；第 2 项去掉截断导数，再由原 u 的一阶弱链与合法反射核测试得到 Dᵢ(u⁰*κₙ)=(Dᵢu)⁰*κₙ。旧 `zeroExtend` 弱导数结论的测试域始终仍是 S，绝未改成 univ。最终的 L² 等式只需对充分大 n 成立，足以转移强极限。

第 5 项的 Gₙ 是 φₙ 的真实梯度限制，Aₙ(i,j) 是其真实二次方向导数限制。对任意 i、j 和任意原 T 测试 ψ，光滑测试的原弱导数身份经子域限制给
⟨Gₙ(i),Dⱼψ⟩=−⟨Aₙ(i,j),ψ⟩，对所有 n 成立，负号正确。没有缩小测试集合或要求 ψ 只在某个人工内部区域支持。

最终分量界逐层为：限制收缩；实际紧支测试的 Hessian–Laplacian 能量恒等式给每个二阶分量范数≤‖Δφₙ‖；T133 的实际截断 PDE 和非负单位核 L² 收缩给上述 M 界。已读取 T133 的乘积恒等式及估计：Δφₙ=−η(f⁰*κₙ)+2∑ᵢ(Dᵢη)((Dᵢu)⁰*κₙ)+(Δη)(u⁰*κₙ)，负号及系数 2 均保留；所有相加/相乘函数先证明 MemLp，未利用不可积积分的默认值。

T128 的 `exists_weakH2_of_gradient_test_limits` 仅从这些测试配对极限、分部积分及最终统一分量界构造二阶弱字段；其 Hahn–Banach/Riesz 步骤、真实混合弱导数交换和 Sym 字段组装已验收，本次再次核对调用与关键源码。构造保留原一阶 jet 的全部字段，不要求 Aₙ 收敛或对 u 作 H² 零延拓。Hessian 范数平方按无序 Sym 坐标精确求和，再以共同分量界估计；`card(Sym(Fin d),2)` 因子未被删除。

## 同一载荷、边界情形及范围

第 4 项把任意 T 测试 φ 视为 S 上同一全空间光滑函数。只有测试 φ.sobolevJet 使用 H¹₀ 零延拓；它确属原测试闭包，并由 `extendDirichlet_test` 精确恢复 monoDomain φ 的完整 jet。原 u 没有 H¹₀ 前提。实际梯度配对通过零延拓/限制内积等式转移，右端同样使用 `subdomainZeroExtend_inner` 得到 f|T；两次实内积交换只是对称性，不丢失边界项。

第 6 项对已构造 v 使用真实 `negativeLaplacian_isWeak`，以完整一阶截断等式重写成原 u|T 的弱方程；再与第 4 项给出的同一 f|T 方程比较，通过全部紧支测试的 `unique_rhs` 得实际 L² 等式。不是仅证明某个二阶字段存在后指定右端项。

空 K/T/S 的允许情形不要求非空或正体积；正缓冲/光滑 Urysohn 的陈述涵盖空集，零测度 L² 情形由原定义处理。d=0 也未偷加正维条件：Fin d 的一、二阶指标为空，所需分量证明为空族，Sym 二阶字段为零；同一载荷身份仍由真实弱方程及测试唯一性得到。全链没有除以体积、梯度范数、d 或 Hessian 常数。

本批无阻断缺陷。其内部常数没有声称对逼近边界的 T 一致；不能将本结论直接用于 T=S 的一般有界开域，也不能由此宣称光滑域边界正则性、凸域统一 Hessian 先验界、实际光滑凸穷竭或原 D(A)=H²∩H¹₀ 已完成。这些仍是 P023 的后续义务。

## 固定依赖版本核对

从四模块的 `public import` / `import` 递归取得 170 个 Carleman 源文件；其中 166 个在 base 中存在，逐字节与 checked_sha 完全相同，另四个即本批新模块。以下是再次与各已验收 declaration_version 比较的相关源依赖闭包，均为零改动：

| 依赖 | 已验收版本 | 本次比对入口及闭包数 |
|---|---|---|
| C149 | `c3ea3c03352de258d944bf495695b31bcef3f3b0` | CutoffPoissonEstimate，113 文件 |
| C148 | `a69b48ebeef0ea36e6f324c6bd2e1e7bf6659f52` | CompactTestHessianEnergy / WeakPoissonConvolution，87 文件 |
| C144 | `5f407936e769fa9742463e35a8d7d8e29970aa36` | WeakH2BoundedLimit，57 文件 |
| C147 | `94f7ddd96b42ac046a4dc2cb14fffb5cd97f1402` | DirichletExtensionPairing，95 文件 |
| C131 | `f134750df6b8ef03c639f50dd5084d4c42d49272` | StrongMollifierLimit，72 文件 |
| C089 | `c99262c4a0d65a4d23f2efb57748bda490e971d7` | InteriorWeakPoincare，67 文件 |
| C036 | `cfd7d038d322779b1e9bc1cdd076af65e0e829d1` | DomainConvolution，26 文件 |
| C145 | `bee8a93d0856f84c9280d10a19f50da7da2a362f` | WeakLaplacianLimit，58 文件 |

固定 toolchain 为 Lean 4.35.0；mathlib 锁定 `56a005855ea17e0b0958f73ec801ae140b0a1679`，实际本地 mathlib HEAD 相同且工作树干净，故新增 Urysohn/增厚源码读取对应这一版本。原稿未修改，SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

## 实际 CI、原始证据与公理

独立通过 GitHub API 读取 [main run 39216297404 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39216297404/attempts/1)：event=push，head_branch=main，head_sha 精确等于 checked_sha，整体 completed/success。三项实际 jobs 均 completed/success：lean `117940835167`、state-check `117940835367`、dashboard / snapshot `117941986517`。lean 的构建和两项证据上传步骤均为 success。

独立用 `gh run download` 下载同 run 的两份原始产物：

- `lean-ci-result`：artifact ID `12169807317`，本地 `/tmp/carleman-t134-interior-main-ci/result.json`。
- `lean-declaration-evidence`：artifact ID `12169877697`，本地 `/tmp/carleman-t134-interior-main-axioms/axioms.txt`。

实际 result.json 为 PASS，checked_sha/source_head_sha 均为本报告固定 SHA；finished_at=`2026-10-19T07:31:28.746663+00:00`，target=Carleman。CI Lean 为 4.35.0，commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib_commit 与上述固定值相同。

远端 axioms.txt 与固定 `/tmp/carleman-t134-interior-local-axioms.txt` 已作实际逐字节比较，完全相同：**2,140,355 bytes**，SHA256 **`90e74c2d73c431eb5cf9bace13b50934dcdbffa79fdb46a4a728842a0edf44bf`**。六项均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。独立解析全部 2,448 条显式公理记录：2,440 条仅含正常基础公理，8 条无公理依赖，没有其它公理；文件末尾为 **Axiom audit passed for all 6975 Carleman declarations.** 显式打印条数与递归审计声明总数是不同计数，未混用。

实际读取固定 `/tmp/carleman-t134-interior-target.log` 与 `-full.log`，分别记录定向 **3349 jobs**、全库 **3929 jobs** 构建成功；full.log 同时包含上述展开类型与递归审计。此处报告读取到的固定构建证据，不声称本验收另行重跑了这些构建。

**最终签发：C150 在 checked_sha 上 PASS / AUXILIARY；无阻断数学或证据缺陷。报告及 reviewed_at 在通知主 Agent 后冻结，不据后续工作树调整。**

