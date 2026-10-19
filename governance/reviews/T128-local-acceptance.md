# T128 / C144 独立本机验收

- checked_sha: `5f407936e769fa9742463e35a8d7d8e29970aa36`
- base_commit: `b7491fa1b22b01515e8d0c428f35a3dbe301c34f`
- reviewed_at: `2026-10-19T06:40:44+00:00`
- reviewer: `/root/accept_spatial_foundations`，独立本机验收 Agent。
- result: **PASS**；axiom_check: **PASS**。
- scope: **AUXILIARY**。C144 可在上述固定版本登记为 REVIEWED；P023 / `prop:analytic-realizations` 不提升，原文完成数保持 **14/26**。

本报告直接读取固定 Git 对象中的六模块、全部实际展开类型、关键依赖、原稿、MATH_SPEC、T128 分析和台账，并独立查询同 SHA 远端作业、下载原始产物。语义结论不以执行者说明或编译成功替代。仅编写本报告；未改实现、台账、原稿或根导入，未提交或推送。后续工作树与动态 `.ci/axioms.txt` 排除在本次证据之外。

## 全部 16 项声明

下表行号均为 checked_sha。声明 JSON 与 C144 台账精确一致；六模块均由固定 `Carleman.lean` 导入，16 项均在固定 `tools/CheckAxioms.lean` 中列有 `#check @...` 及 `#print axioms ...`。独立下载的原始证据实际包含全部 16 项的展开类型。

| # | 完整声明 | 固定源码位置（均在 `Carleman/Spatial/`） | 逐项结论 |
|---|---|---|---|
| 1 | `Carleman.SpatialTest.derivativeTest` | `SpatialTestDerivative.lean:15` | PASS。真实方向 Fréchet 导数仍为同域紧支 C∞ 测试，支持包含已证明。 |
| 2 | `Carleman.SpatialTest.derivativeTest_toLp` | `SpatialTestDerivative.lean:21` | PASS。导数测试的实际 L² 类等于原 `derivativeLp`，通过两者 a.e. 实现证明。 |
| 3 | `Carleman.SpatialTest.derivativeTest_derivativeLp_commute` | `SpatialTestDerivative.lean:27` | PASS。两次真实测试方向导数在 L² 中交换；使用测试自身的经典二阶对称性。 |
| 4 | `Carleman.IsWeakSpatialDerivative.mixed_commute` | `WeakMixedDerivative.lean:15` | PASS。原状态的两条完整弱导数链，经四个测试身份与测试唯一性推出混合 L² 导数相等。 |
| 5 | `Carleman.derivativeFiberInjection` | `DerivativeFieldAssembly.lean:13` | PASS。任意阶无序 Sym 指标的真实 Euclidean 坐标 CLM 注入。 |
| 6 | `Carleman.derivativeFiberInjection_component` | `DerivativeFieldAssembly.lean:17` | PASS。抽取同指标恢复原 L² 类，异指标为实际零类。 |
| 7 | `Carleman.derivativeFieldAssembly` | `DerivativeFieldAssembly.lean:32` | PASS。有限个真实坐标注入之和组成 L² 字段 CLM。 |
| 8 | `Carleman.derivativeFieldAssembly_component` | `DerivativeFieldAssembly.lean:36` | PASS。每个给定 L² 分量被精确恢复。 |
| 9 | `Carleman.derivativeFieldAssembly_norm_sq` | `DerivativeFieldAssembly.lean:44` | PASS。实际字段 L² 范数平方等于全部无序多指标分量范数平方之和。 |
| 10 | `Carleman.secondOrderFields` | `SecondOrderJetAssembly.lean:14` | PASS。保留原 0、1 阶字段并填入给定二阶字段；本定义自身不虚称弱身份已成立。 |
| 11 | `Carleman.secondOrderJet` | `SecondOrderJetAssembly.lean:21` | PASS。原 H¹ 弱链加上明确的全部二阶弱身份，构成真实 H² jet。 |
| 12 | `Carleman.secondOrderJet_truncate` | `SecondOrderJetAssembly.lean:35` | PASS。一阶截断严格等于原 H¹ jet，非仅 value 相等。 |
| 13 | `Carleman.secondOrderJet_hessian` | `SecondOrderJetAssembly.lean:44` | PASS。所得二阶字段严格等于输入 A。 |
| 14 | `Carleman.exists_weakH2_of_gradient_test_bounds` | `WeakH2BoundedTest.lean:17` | PASS。从全部原梯度测试泛函的 C 界内部构造二阶 L² 导数及对称性，输出原 H² jet 和明确维数因子。 |
| 15 | `Carleman.exists_weakH2_of_gradient_test_limits` | `WeakH2BoundedLimit.lean:14` | PASS。逐测试配对收敛、逐测试最终分部积分身份、候选分量最终界足够；不要求候选 Hessian 收敛或对称。 |
| 16 | `Carleman.exists_weakH2_of_strong_H1_limit_bounded` | `WeakH2BoundedLimit.lean:36` | PASS。真实 H² 序列的一阶截断强收敛及完整 Hessian 最终统一界，推出同一极限状态的 H² 身份。 |

## 原文对应和实际范围

原稿 2659–2664 行 `prop:analytic-realizations` 要求实际 Dirichlet Laplacian 满足 A1–A3，并用 Grisvard Theorem 3.2.1.2 得到 D(A)=H²∩H¹₀ 及椭圆正则估计。本次另直接查看所给 `/tmp/carleman-pdf-read/regularity-159.png` 至 `regularity-161.png`：印刷 147 页陈述凸域平滑逼近及该定理，148 页使用光滑内域解和统一二阶界，149 页通过最终包含测试支持后的积分身份识别极限二阶分布导数。

本批对应这一证明中“把有界分布导数组装为真实 H² 状态、把测试身份传到极限”的基础步骤。代码以有界测试泛函的 Hilbert 表示完成极限导数构造；该路线不必先抽取候选 Hessian 的弱收敛子列。它没有证明内域序列存在、内域解 H² 正则性、Dirichlet Hessian 先验界或原算子域等式。不可仅凭此工具验收整个 Grisvard 定理或原 `prop:analytic-realizations`。

第 1–3 项对一般实范数空间 E 的光滑测试成立；转 L² 时明确要求 Borel 结构和测度对紧集有限。第 4 项另要求 E 有限维、S 开、ν 几乎处处落在 S 及局部有限性，以便用真实测试唯一性。主 H² 构造和极限第 14–16 项实际取 ν=volume.restrict S，对任意 d 和任意开域 S 成立，未要求有界、凸、光滑边界或非空。候选场是全域真实 L² 类，不是形式分量符号。

## 数学核查

**1. 微分测试的资格、次序和负号。** `SpatialTest` 是全空间 C∞ 标量函数，真实拓扑支持紧且包含于 S。新 `derivativeTest e` 的值是 x↦Dφ(x)e；其光滑性、紧支性与 `tsupport_fderiv_apply_subset` 给同一支持条件。已核查 pinned mathlib 的支持包含及紧支方向导数定理，方向微分没有扩大到域外测试。

`derivativeTest_toLp` 通过原两个 a.e. 实现转为 L² 类等式。交换定理先以 CLM 应用的真实求导公式证明 D(Dφ·e)(x)f=D²φ(x)(f,e)，再用 C∞ 测试的 `ContDiffAt.isSymmSndFDerivAt`。它只对测试使用经典光滑性，未要求原状态 u 光滑。

第 4 项把 D_fφ 代入 u→u_e 的弱身份，把 D_eφ 代入 u→u_f 的弱身份；结合 u_e→u_ef 与 u_f→u_fe 在 φ 上的身份，得到

\[
\langle u_{ef},\varphi\rangle
=\langle u,D_eD_f\varphi\rangle
=\langle u,D_fD_e\varphi\rangle
=\langle u_{fe},\varphi\rangle.
\]

两次分部积分的两个负号正确抵消。`spatial_eq_zero_of_tests` 对差使用全部紧支光滑测试、原 L² 的局部可积性和 ν 支持条件，证明的是实际 L² 类相等。主实例的支持条件由 `ae_restrict_mem hS.measurableSet` 供应，没有额外分布唯一性假设。

**2. 真实无序多指标字段和平方范数。** `DerivativeFiber d k` 是 `EuclideanSpace ℝ (Sym (Fin d) k)`。注入由 PiLp 连续线性等价及 Kronecker 坐标 CLM 构造；以实际 operator multiplier 作用于 L² 类。第 6 项逐点 a.e. 核查注入、投影及零类，之后有限求和精确恢复每个给定分量。

第 9 项调用实际 `derivativeField_norm_sq`：该依赖证明每个 L² 分量平方可积，再将有限坐标和与真实积分交换。故得到等式而非某个未指定范数等价常数。所有无序多指标各出现一次；没有把有序 d² 坐标及其重复混合项冒充原 Sym 范数。声明适用于任意 k，包括空指标或零维情况。

**3. 二阶 jet 组装确实检查全部弱链。** `secondOrderFields` 的三个字段依次为原 u₀、u₁、A。`secondOrderJet` 展开原 `weakJetSubmodule` 的 k=0、1 两层：第 0 层直接复用 u 的全部弱身份；第 1 层将任意 Sym(_,1) 分解成唯一长度一指标，再使用 hA 对每个 i,j 的弱导数身份。没有遗漏混合方向。截断证明逐字段相等，Hessian 字段等式为定义性相等。

这里 hA 是低层组装定义的明确输入；第 14 项没有要求调用者供应 hA 或 Hessian。对每个 i,j，它用 T127 的 `exists_weakSpatialDerivative_of_test_bound` 从

\[
|\langle u_i,D_j\varphi\rangle|\le C\|\varphi\|_{L^2}
\]

内部构造 Dᵢⱼ∈L²、‖Dᵢⱼ‖≤C 及全部原测试上的弱身份。已复查该依赖：原测试 jet 的有限线性组合仍来自真实测试，value 单射将测试泛函视为 L² 子空间上的有界泛函，Hahn–Banach 同范数延拓及实际 Hilbert 对偶等距同构给 L² 表示。它没有预设二阶导数、测试空间完备或 H² 零延拓。

然后使用 u 的两个原一阶弱链和第 4 项证明 Dᵢⱼ=Dⱼᵢ。`Sym2.lift` 只在这条已证明的对称性下通过商下降，再经 pinned mathlib 的 `Sym2.equivSym` 转为原 `Sym (Fin d) 2`。源码 `hv` 显式处理 `cons j (cons i nil)` 的方向次序，不是直接假设交换。组装场 A 的每个分量满足 hA，故 U 的一阶截断严格等于原 u。

精确平方范数和及逐坐标界给

\[
\|\operatorname{field}_2U\|^2
=\sum_{\alpha\in\mathrm{Sym}(\mathrm{Fin}\ d,2)}\|D_\alpha\|^2
\le \#\mathrm{Sym}(\mathrm{Fin}\ d,2)\,C^2.
\]

维数因子明确保留；这不是声称最终完整 Hessian 范数仍≤C 的最优常数结论。C 仅需非负，C=0 无除法，零维的空二阶坐标求和正常成立。低阶字段完全保留，因此输出是同一个原 H¹ 状态的真实 H² 提升，而非只有某个 Hessian 范数数值。

**4. 逐测试最终身份与强 H¹ 极限。** 一般极限定理先固定 i,j,φ，合并该测试的最终身份与对应候选分量的最终范数界，用真实 Cauchy–Schwarz 得到配对绝对值最终≤C‖φ‖。配对收敛及绝对值连续性，再以闭序极限给同一界，最后调用第 14 项。最终身份起始指标可依赖 φ；无需某个统一 n 对所有测试同时有效。hbound 仅要求每对 i,j 最终成立，C 是同一个常数。

G 和 A 不要求在每个 n 上组成弱 jet，不要求 Aₙ 对称、弱收敛或强收敛。真正极限导数及其对称性由界和原极限 H¹ 状态内部构造。该工具因此适合后续内域问题的分量延拓，但没有断言这些分量是全域延拓函数的二阶弱导数，也没有供应后续所需的 eventual 测试身份。

强 H¹ 推论中，每个 Uₙ 本身是同域真实 H² jet。hlim 是原完整 H¹ 图拓扑中的截断收敛，包含 value 和全部一阶 L² 字段；`fieldCLM` 与 `derivativeComponentCLM` 连续性推出所需测试配对收敛。全部测试身份直接来自 Uₙ 的第 1 层弱链；`derivativeComponent_norm_le` 是实际 Euclidean 坐标投影范数≤1 的 L² 界，将完整 Hessian 最终界传给每个分量。没有把单独的 L² 值收敛误当 H¹ 收敛。

## 依赖版本、公理与原稿

递归比对六模块的 Carleman import 闭包，共 **57** 个模块；其中 **51** 个既有模块与 base 逐文件一致。另核查已接受 declaration_version：C143 `WeakDerivativeBoundedTest` 闭包 35 个模块与 `b7491fa1b22b01515e8d0c428f35a3dbe301c34f` 一致；C022 `WeakDerivativeUnique` 闭包 18 个与 `a6c199412758d406be8c3f8d1e76587b9f820bc1` 一致；C023 `SobolevTruncation` / `SobolevTopology` 联合闭包 30 个与 `e4b308fc21cd669906716aa9af53f1c2a263b1a7` 一致；C027 `ComponentNorms` 闭包 39 个与 `1445d536076eeb660a1abf9badef6231bd6d2872` 一致。没有使用旧验收掩盖已变化的依赖。

全部 16 项公理输出均仅为 `propext`、`Classical.choice`、`Quot.sound`。独立检查原始文件全部 **2386** 条显式公理记录：2378 条只使用此正常基础集合，8 条不依赖公理，无异常公理。末行是 **6880** 项 Carleman 声明的完整递归审计 PASS；两种条数未混同。无 `sorryAx` 或未证明的数学公理。

Lean 为固定 4.35.0，远端记录编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；manifest 及本机干净 mathlib checkout 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。原稿无修改，SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

## 实际构建与同 SHA 远端证据

实际读取 `/tmp/carleman-h2-bounded-target.log` 的 **3197 jobs** 成功及 `/tmp/carleman-h2-bounded-full.log` 的 **3900 jobs** 成功、6880 项审计末行。本验收核查这些固定日志，未声称重新运行全库构建。

独立通过 GitHub API 查询 [run 39210894315 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39210894315/attempts/1)：main head SHA 精确等于 checked_sha，最终 run 为 completed/success，三项实际作业全部 completed/success：state-check **117923789282**、lean **117923789680**、dashboard / snapshot **117924733184**。先前尚在运行的状态未被当作最终成功。

独立查询 artifact 元数据并自行用 `gh run download` 下载：`lean-ci-result`，artifact ID **12167214526**，至 `/tmp/carleman-h2-bounded-main-ci/result.json`；`lean-declaration-evidence`，artifact ID **12167498430**，至 `/tmp/carleman-h2-bounded-main-axioms/axioms.txt`。result 实际为 PASS，checked_sha 与 source_head_sha 均为本报告完整 SHA，finished_at 为 **2026-10-19T06:38:44.988534+00:00**，target 为 `Carleman`。

远端原始 axioms 与固定 `/tmp/carleman-h2-bounded-local-axioms.txt` 经独立逐字节比较完全一致：均 **2,096,243 bytes**，SHA256 均 **`0d2734ed7fd8407595f8b3b0bc43ba3a0b4d88ccbdad2d072d51a658fbd882ef`**。这是实际文本摘要，不是 artifact ZIP 摘要。

## 最终结论

固定版本全部 16 项通过独立数学、类型、依赖、公理和同 SHA 三项正式 CI 验收，无阻断发现。C144 可登记为 **REVIEWED / AUXILIARY**。

真实 Dirichlet 解的统一 Hessian 先验界、光滑内域正则性、凸域穷竭与相应测试身份仍须证明；本批不据此宣称 D(A)=H²∩H¹₀ 或原 A1–A3 全部完成。P023 及其他 PAPER 项不提升，原文保持 14/26。报告通知后冻结 reviewed_at 与全部内容。
