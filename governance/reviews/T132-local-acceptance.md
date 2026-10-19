# T132 / C148 独立本机验收

- `checked_sha`: `a69b48ebeef0ea36e6f324c6bd2e1e7bf6659f52`
- `base_commit`: `94f7ddd96b42ac046a4dc2cb14fffb5cd97f1402`
- `reviewed_at`: `2026-10-19T07:17:00+00:00`
- `reviewer`: `/root/accept_spatial_lemma`
- `result`: **PASS**；`axiom_check`: **PASS**。
- `scope`: **AUXILIARY**。C148 可登记为 REVIEWED；P023 / `prop:analytic-realizations` 不提升，原文保持 **14/26**。

本 Agent 从固定 Git 对象读取三模块全部证明、九项实际展开类型、T132 分析、MATH_SPEC、C148/T132 台账、原稿与关键依赖；另独立查询实际同 SHA 三项 CI，自行下载同 run 原始产物并逐字节比较。执行者说明及 CI 未替代语义审查。工作树后续 `CutoffPoissonConvolution`、`SmoothLaplacianProduct` 及动态 `.ci/axioms.txt` 均排除。

## 全部九项声明

名称省略公共前缀 `Carleman.`；固定位置以 `Carleman/Spatial/` 为根。顺序与 `/tmp/carleman-t132-interior-energy-declarations.json`、固定 C148 和 T132 的列表精确一致，包括一个实际定义。

| # | 声明 | 固定源码位置 | 独立结论 |
|---|---|---|---|
| 1 | `SpatialTest.mixed_derivative_norm_sq` | `CompactTestHessianEnergy.lean:15` | PASS；任意两方向的真实混合二阶 L² 范数平方等于两纯二阶导数的实际 L² 内积，由两次原弱分部积分及三阶测试导数交换证明。 |
| 2 | `SpatialTest.hessian_energy_eq_laplacian` | `CompactTestHessianEnergy.lean:26` | PASS；全部有序坐标对求和，精确等于实际纯二阶导数和的 L² 范数平方，系数1。 |
| 3 | `SpatialTest.hessian_component_norm_le_laplacian` | `CompactTestHessianEnergy.lean:35` | PASS；从非负平方和抽取任意分量，得到范数界，未删除混合项或改变计数。 |
| 4 | `SpatialTest.laplacianLp` | `CompactTestH2Jet.lean:16` | PASS；定义为真实测试二阶导数 L² 类的有限对角和。 |
| 5 | `SpatialTest.exists_H2_jet` | `CompactTestH2Jet.lean:20` | PASS；开域上构造真实 H² jet，其一阶截断严格等于原测试 jet，负 Laplacian 严格等于负的上述和；无序字段范数的维数因子明确保留。 |
| 6 | `IsWeakSpatialDerivative.mixed_convolution_first` | `WeakPoissonConvolution.lean:15` | PASS；只用一条原弱导数链，识别实际卷积函数的真实混合二阶导数；核支撑条件明示，两个方向顺序正确。 |
| 7 | `IsWeakNegativeLaplacian.integral_test` | `WeakPoissonConvolution.lean:30` | PASS；原完整弱方程准确展开为全部坐标的真实 Lebesgue 积分，无额外正规性前提。 |
| 8 | `IsWeakNegativeLaplacian.convolution_identity` | `WeakPoissonConvolution.lean:49` | PASS；合法反射测试、其负导数及实际 L² 零延拓积分身份给局部卷积散度方程。 |
| 9 | `IsWeakNegativeLaplacian.mollified_laplacian` | `WeakPoissonConvolution.lean:73` | PASS；内部组合原 H¹ 弱链和上项身份，得到同一卷积函数的真实 −ΔU=f*κ，未假设原解 H²。 |

## 原命题定位及范围

已核对固定 `paper/main.tex:2659–2664`。P023 对固定有界凸多面体（d=2,3）或任意固定维数盒子的实际 Dirichlet Laplacian，要求原 A1–A3，并通过 Grisvard Theorem 3.2.1.2 得到 D(A)=H²∩H¹₀ 和椭圆正则估计。T132 是其中内部正则性路线的前置分析工具，未证明这个域等式或整个推论。

本线程此前已查看 Grisvard 印刷147–149页，本次又实际查看 `/tmp/carleman-pdf-read/regularity-160.png`（印刷148页）：其证明使用光滑凸内域上的 H² 解及统一二阶界，随后取弱极限。该页面中的 H² 解存在性和统一估计是独立分析义务，不能由“紧支测试 Hessian 恒等式”直接替代。T132 当前只为局部截断和平滑化后的内部估计提供工具；未声称已经供应光滑内域边界正则性或一般 H²∩H¹₀ 的 Miranda–Talenti 不等式。

C147 / T131 已验收的穷竭接口仍输入实际 H² 内域解及统一 Hessian 界。本次读取其固定验收报告，确认这些输入并未被悄悄取消；C147 是后续使用场景，T132 的新证明没有把 C147 的条件性 H² 结论当作原解已有 H² 的事实。

## 真实测试及双重分部积分

`SpatialTest S` 是任意全空间真实 C∞ 函数，具有紧拓扑支持且整个支持包含于 S。其 `toLp`、`derivativeLp` 由真实 MemLp 证明构造，分别 a.e. 等于原函数与实际 Fréchet 方向导数。`derivativeTest e` 的值是 D_eφ，C∞ 与紧支性均被证明，且导数拓扑支持不扩大。因而本批反复使用的是同一原完整测试族。

第1项令 e、f 为任意真实方向，并分别使用 `(D_eφ)` 的 e 向弱链测试 `D_fD_fφ`、其 f 向弱链测试 `D_eD_fφ`。两条分部积分右侧分别为负的纯二阶配对与负的混合二阶自配对；三阶测试中的最后两次导数交换使左侧相同，二阶测试交换将右侧变为同一混合导数的自内积。由此得到

\[
\|D_fD_e\varphi\|_2^2
=\langle D_e^2\varphi,D_f^2\varphi\rangle_{L^2(S)}.
\]

这里没有边界项的原因是原测试及其导数的实际紧支持。底层 `SpatialTest.weakDerivative` 调用已证明的 Lipschitz 差商积分分部定理；C∞ 紧支函数的全局 Lipschitz 资格由源码内部供应，非调用者新增假设。实际混合导数交换由真实 fderiv 的对称二阶导数证明，不是公理或自定义替代导数。

第2项展开纯二阶和的内积，两次有限求和后逐项应用第1项，故左侧是 **全部有序** (i,j) 坐标对，每个出现一次。第3项两次使用非负平方和中的单项不超过总和，再由范数非负取平方根，系数严格为1。其类型不要求 S 开、凸或有界；紧支测试已经足够。d=0 时求和为空、两端为0；分量命题带 i,j:Fin d，未选择不存在的坐标。

所有内积均为 volume.restrict S 的真实 L² 内积。测试及任意阶测试导数平方可积由紧支光滑性内部证明，乘积可积由 L² 配对保证；这些恒等式不依赖不可积 Bochner 积分的默认值。

## 实际 H² jet 与负 Laplacian

`laplacianLp φ` 是 Σ_i D_i²φ 的真实 L² 类，符号为正 Laplacian。第5项明确要求 S 开：这是从全部测试唯一恢复弱导数所需的原条件，不是附加边界正规性。证明先用每个二阶分量的实际弱分部积分与 Cauchy–Schwarz，内部供应 C144 的全部梯度测试界，统一 C=‖laplacianLp φ‖≥0。

实际调用的 `exists_weakH2_of_gradient_test_bounds` 从这些界构造平方可积二阶弱导数，内部证明混合弱导数交换，按 Sym(Fin d,2) 组装原真实 H² jet，检查全部弱链，并保留原 H¹ jet。其输出不是预设的二阶正规性。`truncate¹ v=φ.sobolevJet` 是完整 jet 的严格等式，包含同一值及全部一阶字段。

随后逐个 i 比较 v 的原弱链和 `D_iφ` 的真实 i 向弱导数，以开放域上的弱导数唯一性证明对角二阶分量严格等于 D_i²φ。因此原 `negativeLaplacian v=-Σ_i field₂(v)_{ii}` 严格等于 `-φ.laplacianLp`，不是只在测试意义下成立的替代结论。

第5项估计是

\[
\|\operatorname{field}_2 v\|_2^2
\le \operatorname{card}(\operatorname{Sym}(\operatorname{Fin}d,2))\,
\|\Delta\varphi\|_2^2.
\]

这里原弱 jet 的二阶字段按无序多重指标存储；证明保留其维数因子，未将第2项有序 d² 个分量的等式错误当成无序字段的定义。该构造仅针对原紧支光滑测试，不是任意 H¹₀ 状态的 H² 提升。

## 一阶弱链足够的实际二次卷积微分

第6项的 u、v 只是全空间 L² 类，h 仅断言它们在 S 的全部原测试下满足 e₀ 向弱导数身份；无需全空间弱导数，也没有 v 的任何弱导数输入。核 κ 为任意真实紧支 C∞ 测试，不需非负、对称、积分1或预设半径。其显式几何条件为 `∀ y∈tsupport κ.value, x-y∈S`。

证明先使用全空间均有效的真实卷积微分公式

\[
D_{e_1}(u*\kappa)=u*(D_{e_1}\kappa),
\]

再对右侧真实光滑卷积取 e₀ 向导数。在这一步之后才于 x 使用 h 的局部弱交换，得到

\[
D_{e_0}\big(D_{e_1}(u*\kappa)\big)(x)
=(v*D_{e_1}\kappa)(x).
\]

因此没有对仅在单点成立的局部弱交换身份直接求导，也没有偷偷要求 x 邻域上统一支持缓冲。方向顺序严格是外层 e₀、内层 e₁；原已知弱导数正是 e₀。导数核的真实拓扑支持包含于 κ 的原支持，显式 hinside 由此合法传递。

底层全空间卷积公式使用 pinned mathlib 的 `HasCompactSupport.hasFDerivAt_convolution_right`，给出真实 HasFDerivAt；L² 蕴含局部可积，紧支光滑核及其导数保证卷积积分存在。向量值积分施加 CLM 时具有实际可积性证明。另有 `smooth_convolution` 证明同一实际卷积为 C∞，故此处 fderiv 并非对不可微函数使用默认零值。

## 原弱 Poisson 方程、反射负号和 a.e. 零延拓

第7项的 u 是任意原 H¹ jet，f 是原 L²(S) 类，h 是全部 `SpatialTest S` 上的原 `IsWeakNegativeLaplacian u f`。该定义为真实弱梯度配对等于 f 与测试的内积。`weakGradientPairing_coordinates` 将完整一阶字段精确拆成每个坐标一次；测试一阶字段和原真实导数 a.e. 身份进一步给出

\[
\sum_i\int_S D_i\varphi\,D_i u=\int_S\varphi f.
\]

没有额外光滑代表、边界迹条件、H² 输入或预设 PDE 点态身份。展开的两侧乘积都来自真实 L² 配对，符合原 Lebesgue 积分。

第8项明确输入 S 可测，以构造实际 `zeroExtendLp`。反射核测试 `φ(y)=κ(x-y)` 的紧支持通过反射同胚精确变换；hinside 保证整个拓扑支持包含在 S。真实链式法则给 `D_iφ(y)=-D_iκ(x-y)`，因此原弱方程确实变成

\[
-\sum_i\big((D_i u)^0*D_i\kappa\big)(x)
=(f^0*\kappa)(x).
\]

上标0表示实际 L² 零延拓。其定义由 indicator 的 MemLp 资格构造，a.e. 等于 S.indicator 原类；`integral_mul_zeroExtendLp` 准确恢复限制测度上的积分，证明没有把边界两侧的任意代表当成点态相等，也没有增加域外项。整个推导只需 S 可测和已给局部弱身份；无有限体积、凸性或 H¹₀ 前提。

第9项取同一实际函数 `U=(value u)^0*κ`。对每个坐标，u 的0阶原弱链零延拓后只在 **S 的测试族** 上成立，即 `IsWeakSpatialDerivative volume S ...`，并非 volume/univ 上的全空间弱导数。第6项于是于 x 识别 U 的真实纯二阶导数为梯度零延拓与核一阶导数的卷积。逐坐标替换第8项，得到严格点态等式 `-Σ_i D_iD_iU(x)=(f^0*κ)(x)`。

这既没有假设 u∈H²，也没有宣称 value u 的零延拓为全空间 H¹/H²，更未把单独延拓的梯度误认成跨越边界的全空间弱梯度。核支持条件不能删除；结论只覆盖它成立的 x。对 d=0、空域或零核等退化情况均未作除法或非法非空选择，原弱方程和 hinside 按实际类型保留。

## 依赖版本、量词及公理

三模块 Carleman 导入闭包共 **94** 模块，**91** 个旧模块与 base 逐字节不变。另对关键已验收版本递归比较：C144 `WeakH2BoundedTest` 的56模块闭包与 `5f407936e769fa9742463e35a8d7d8e29970aa36` 一致；C130 `LocalHessianConvolution` 的53模块闭包与 `a5c68e2aaa4da98efe42da31ed0c1da04ba99952` 一致；C057 `DirichletDistribution` 的57模块闭包与 `3d5aa9cec281974bef7da9d37ffa11a8f9f75670` 一致。实际读取相应证明及 `DomainConvolution`、`WeakConvolution`、`ZeroExtensionLp`、`SpatialTestDerivative`、`TestPoincare`、`SpatialTestSobolev`、`WeakProductComponents`、`WeakDerivative`、`LipschitzWeakDerivative`、`WeakLaplacian`，没有只靠旧 PASS 标签。

所有几何和正规性前提均在上文逐项列明。精确能量系数为1；第5项仅有明确维数因子，没有隐藏网格、域、核、半径或权参数常数。卷积结论为任意核/点的精确身份，不附带尚未证明的全局误差、统一内部 H² 估计或凸域先验界。

治理协议、原稿及工具链 pin 自此前验收不变；原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean 固定4.35.0；mathlib manifest pin 与实际本机干净 checkout 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。三个模块全部由固定 root 导入，九项在固定 `tools/CheckAxioms.lean` 均有实际类型及公理打印。

实际读取固定 target/full 日志：分别 **3252 jobs**、**3922 jobs** 构建成功；本验收核对既有固定构建证据，未声称重新运行全库。固定 raw 为 **2,126,767 bytes**，SHA256 **`c7719e6145e61f465ebcd7dd51a25c15bc41b6e3939df9733771f42dde4cf4b6`**。九项展开类型均与已读源码一致，全部只依赖 `propext`、`Classical.choice`、`Quot.sound`。全文件2422条非空公理记录及8条无公理记录均无异常；末行为 **6951项全声明递归审计 PASS**。显式打印条数与递归审计总数没有混同，新源码无 sorry/admit/新增 axiom。

## 独立同 SHA CI 和原始产物

本 Agent 经 GitHub connector 自行查询 [run 39214559347 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39214559347/attempts/1)：main/push，head 精确为 checked_sha，最终 completed/success，updated_at 为 `2026-10-19T07:16:14Z`。三项实际 job 全部 completed/success：state-check **117935290566**、lean **117935290995**、dashboard / snapshot **117936321406**；其完成时间分别为07:13:11Z、07:16:04Z、07:16:13Z。Lean pin、实际构建、结果记录、证据保存及 post 步骤均成功。

同 run 原始 artifact：`lean-ci-result` **12169166216**，ZIP492 bytes，digest `sha256:7e9d871e66cbd8071dba0ef905e331d611424394933178d8352cc08801d174ca`；`lean-declaration-evidence` **12168787607**，ZIP195871 bytes，digest `sha256:5188e01b2aa6be034f35360f7bcd8f0b84b7abbf72c031504a8cd81a66c2f3d1`。实际元数据均绑定本 run、main 和精确 SHA。

本 Agent 自行 `gh run download 39214559347`，分别保存到唯一前缀 `/tmp/carleman-t132-interior-energy-main-ci/result.json`、`/tmp/carleman-t132-interior-energy-main-axioms/axioms.txt`。实际 result 为 **PASS**，`checked_sha=source_head_sha=a69b48ebeef0ea36e6f324c6bd2e1e7bf6659f52`，target 为 Carleman，`finished_at=2026-10-19T07:15:03.586454+00:00`；编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib 与固定 pin 一致。解压 result 为537 bytes，SHA256 `9f7561d705efcccd7f25bdd97cc6b6194fc9644876d9a8811e1af3202fd1c41b`。

独立逐字节比较远端 `axioms.txt` 与 `/tmp/carleman-t132-interior-energy-local-axioms.txt`，完全一致：**2,126,767 bytes**，SHA256 **`c7719e6145e61f465ebcd7dd51a25c15bc41b6e3939df9733771f42dde4cf4b6`**，末行实际为6951项递归审计通过。上述原始文本摘要与 artifact ZIP 摘要分别记录，没有复用历史阶段或变化中的本机 `.ci` 证据。

## 验收决定

**C148：PASS，可登记为 REVIEWED / AUXILIARY。** 九项声明未发现需修复的数学、类型、量词、弱测试、方向次序、测度、支持边界或公理缺陷；同 SHA 三项正式 CI 及独立下载原始产物全部核验通过。

紧支测试的精确 Hessian 能量、实际 H² 测试 jet、原 H¹ 弱 Poisson 方程的局部实际卷积 PDE 已完成。一般 Dirichlet 状态的边界正则性、凸域统一二阶界、实际光滑凸穷竭及完整 P023 仍待，原文保持 **14/26**。本次仅新增本报告，未改实现、台账、原稿或 root，未 commit/push。最终一致性检查并通知主 Agent 后，冻结本报告及上述 reviewed_at，不再改动。
