# T129 / C145 独立本机验收

- `checked_sha`: `bee8a93d0856f84c9280d10a19f50da7da2a362f`
- `base_commit`: `5f407936e769fa9742463e35a8d7d8e29970aa36`
- `reviewed_at`: `2026-10-19T06:48:44+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：真实 H¹₀ 有界逼近族的共同弱子列、全部原测试的 Poisson 身份传递，以及由最终有界候选二阶分量构造同一右侧的真实 H²∩H¹₀ 状态。具体逼近族、内域 H² 正则性、统一先验界和凸域穷竭仍待，P023 不提升，原文保持 **14/26**。

本 Agent 从固定 Git 对象读取四模块全部证明、7项完整展开类型、T129 分析、MATH_SPEC、C145/T129 条目、原稿及关键依赖。另实际查看给定 Grisvard 页面图像，核对其证明路线。执行者说明、规格和 CI 未替代语义审查；后续子域零延拓文件及变化中的 `.ci/axioms.txt` 均排除。

## 全部七项声明

名称省略公共前缀 `Carleman.`，位置以 `Carleman/Spatial/` 为根；顺序与固定交付 JSON、C145/T129 精确一致。

| # | 声明 | 固定位置 | 独立结论 |
|---|---|---|---|
| 1 | `exists_hilbert_weak_subsequence` | `HilbertWeakSubsequence.lean:13` | PASS；真实弱对偶闭球序列紧性和 Riesz 等距同构内部给同一严格递增子列、全部 Hilbert 测试的弱收敛及原范数界。 |
| 2 | `exists_hilbert_weak_subsequence_in_subspace` | `HilbertWeakSubsequence.lean:34` | PASS；在原闭线性子空间中提取，再以真实正交投影将测试扩展至整个环境空间；极限成员和范数界均保留。 |
| 3 | `hilbert_weak_tendsto_map` | `HilbertWeakSubsequence.lean:47` | PASS；连续线性映射的真实 Hilbert 伴随传递弱配对极限，无强收敛前提。 |
| 4 | `exists_dirichlet_weak_subsequence` | `DirichletWeakSubsequence.lean:17` | PASS；原 Sobolev 平方和 Hilbert 范数及原 H¹₀ 测试图闭包中选同一子列，全部0、1阶字段对所有实际 L² 测试共同弱收敛。 |
| 5 | `IsWeakNegativeLaplacian.unique_rhs` | `WeakLaplacianLimit.lean:13` | PASS；全部原 SpatialTest 唯一确定固定弱 H¹ 状态的 L² 右侧，得到严格类等式。 |
| 6 | `IsWeakNegativeLaplacian.of_weak_gradient_limit` | `WeakLaplacianLimit.lean:22` | PASS；真实梯度弱收敛和逐测试最终 Poisson 身份给同一右侧的极限方程，无统一测试起始指标要求。 |
| 7 | `exists_dirichlet_H2_of_bounded_approximants` | `DirichletH2ApproximationLimit.lean:17` | PASS；内部选出原 H¹₀ 弱极限并构造真实 H² 提升，保留原低阶字段和能量界，证明 actual negativeLaplacian v=f。 |

## 原论文与 Grisvard 的对应范围

已对照原 `paper/main.tex:2659–2664` 的 P023 / `prop:analytic-realizations`：实际 Dirichlet Laplacian 在凸多面体/盒子上满足 A1–A3，证明引用 Grisvard Theorem 3.2.1.2 清偿 D(A)=H²∩H¹₀ 和椭圆正则估计。本批服务该结论的极限步骤，不是该完整定理。

实际查看 `/tmp/carleman-pdf-read/regularity-159.png`、`regularity-160.png`、`regularity-161.png`，分别为印刷147、148、149页。147页给凸域光滑内外逼近及定理陈述；148页从光滑内域解与统一界取弱极限，并在测试支持最终落入内域后传递方程；149页通过全部测试识别极限的平方可积二阶导数。

本代码处理其负 Laplacian 特例的分析极限部分。它直接在原 H¹₀ 图闭包中提取弱极限，并以有界测试泛函的 Hilbert 表示构造极限二阶导数，因而不必同时抽取候选 Hessian 的弱极限。该证明路线保留所需数学结论，但没有在本批构造书中光滑内域、解或先验界，也没有声明一般变系数算子正则性已完成。

## 从有界 Hilbert 序列内部选择共同子列

第1项的完整输入是任意可分、完备实 Hilbert 空间 H、序列 uₙ 和全部 n 的真实范数界 ‖uₙ‖≤C。将每项经 `InnerProductSpace.toDual` 送入强对偶，再视为 WeakDual；Riesz 是等距同构，因此这些元素确实位于同一个强对偶闭球在 WeakDual 中的原像。

已直接读取 pinned mathlib 的 `WeakDual.isSeqCompact_closedBall` 及其来源：可分性给弱对偶紧集可度量性，Banach–Alaoglu 闭球紧性进一步给序列紧性；ℝ 满足其标量适当性条件。不是将一般弱紧性未经说明当作序列紧性，也没有要求强对偶本身范数可分。

序列紧性一次给弱对偶极限 v′、闭球成员和一个严格递增 φ:ℕ→ℕ。Riesz 的逆映射将同一个 v′ 识别为实际 V∈H，等距性保留 ‖V‖≤C。对任意 z∈H，真实连续的弱对偶求值映射把该同一子列的收敛转为 `(u_{φ(n)},z)→(V,z)`。φ 在全部 z 之前选定；没有对每个测试独立选子列，再非法合并不可数多个选择。第1项无需单独给 C≥0，因为存在每个 uₙ 的界已蕴含它；C<0 的输入不可能成立。

第2项将序列作为原闭子空间 K 的元素提取。闭性给 K 的完备性，Hilbert 度量和环境可分性给其可分性；极限从构造起属于 K。对于任意环境测试 z，使用实际 K.orthogonalProjectionOnto z，因所有序列项与极限均在 K，配对与原 z 的配对精确相同。没有通过点态边界条件代替闭子空间，也没有损失范数常数。

第3项使用 `(Lu,z)=(u,L* z)` 的实际伴随恒等式。它只要求真正连续线性 L 和两端 Hilbert 完备性，对每个 z 传递同一序列的弱极限，不预设 Lu 的强极限或任何坐标代表逐点极限。

## 真正的 H¹ 平方和与原 H¹₀ 图闭包

第4项未直接把 WeakSobolevJet 的有限乘积范数当作能量范数。它采用 `SobolevHilbert d 1`，实际底层为 `PiLp 2` 的两个 L² 导数字段，且

\[
\|u\|_{H}^2=\|\operatorname{field}_0u\|_{L^2}^2+
\|\operatorname{field}_1u\|_{L^2}^2.
\]

零阶纤维是原标量值的等距实现，一阶纤维包含全部坐标。完整弱身份定义的子空间已证明闭，故该空间真正完备；`SobolevHilbert.toJet`、`ofJet` 是实际互逆连续线性映射，未改变任何弱字段。

原 `dirichletJetSpace S` 仍为全部 SpatialTest 的 jet 线性张成在完整弱 H¹ 图拓扑中的闭包。代码取其在 `toJet` 下的线性原像 K；`toJet` 连续和原图闭包闭性给 K 闭。这里不是 H¹₀ 的标量 L² 闭包，也不是假设全部闭包连续函数边界为零所得到的另一空间。

Lebesgue 受限测度的可分测度实例及有限维 DerivativeFiber 的可分性，内部供应两个 L² 字段的第二可数性，再传给有限 PiLp 和其子空间。已查看 mathlib 的 `Lp.SecondCountableTopology`，p=2≠∞ 的事实在代码中明确供应。最终定理不额外要求使用者提供可分性、有限体积或有界域；本实例可用于任意 S，最终 H² 构造另明确要求 S 开。

hC≥0 和原平方和界先准确给 Hilbert 范数≤C，闭子空间弱紧性保留该界，再用同一平方和等式返回原字段能量≤C²。每个字段是 `fieldCLM k ∘ toJet`，第3项使同一个 φ 对全部 k∈Fin 2 及全部真实 L² 测试 z 均弱收敛。没有只证明标量值弱收敛就声称梯度也收敛，也没有把弱收敛升级为强 H¹ 收敛。

## 全部测试的 Poisson 方程、唯一性和负号

已展开 `IsWeakNegativeLaplacian u f`：它是对所有原紧支光滑 SpatialTest φ 的真实身份

\[
\langle\operatorname{field}_1u,\operatorname{field}_1\varphi\rangle_{L^2}
=\langle f,\varphi\rangle_{L^2}.
\]

第5项对固定 u 的两个右侧相减，得到 f−g 与每个原测试正交；开域和受限 Lebesgue 测度的原测试唯一性给 f=g，结论是实际 L² 类相等。它证明的是同一 u 的右侧唯一性，不是未经能量论证便声称全部 Poisson 解唯一。

第6项对每个固定 φ，把其真实一阶 L² 字段作为 hlim 的测试，故左侧真实梯度配对收敛至 u 的配对。hpde 只需该 φ 的身份最终成立；最终常数序列的极限与上述极限的唯一性给同一 f 的身份。每个 φ 可以有不同的起始指标，不需要某个 n 同时容纳全部紧支测试。没有交换不可数个 a.e. 集或要求状态/候选导数具有点态收敛。

`negativeLaplacian` 已直接读取：它是真实 H² 字段的纯二阶坐标和之负，即 `−Σ_i D_ii`，每个坐标一次。`negativeLaplacian_test` 从 H² 的完整弱链得到上述正梯度配对，分部积分的负号与此定义相抵。最终不是把一个命名为 Laplacian 的自由场当作实际算子。

## 候选 Hessian 无额外收敛或全域弱身份

第7项的实际输入清楚分为：原 H¹₀ 序列 Uₙ、全部 n 的统一 H¹ 平方和界 C₁²；真实标量 L² 候选 Aₙᵢⱼ、对每对 i,j 最终成立的范数界 C₂；对每个 i,j,ψ 最终成立的单步分部积分身份；以及每个 ψ 的最终 Poisson 身份。C₁、C₂ 非负且不随 n 变化。这些是本辅助极限步骤的公开输入，未伪装成已从原域几何证明的结论。

首先由第4项内部取得同一个 u∈原 H¹₀、同一个严格递增 φ 及全部字段弱收敛。设 Gₙᵢ 为 U_{φ(n)} 的实际一阶分量。`derivativeComponentCLM` 是真实 L² 连续线性坐标映射，第3项把完整梯度弱收敛传为 C144 所需的每个 `(Gₙᵢ,D_jψ)` 配对极限。这个步骤没有从单独标量值弱收敛推导梯度信息。

φ 严格递增蕴含 φ(n)→∞，因此同一个 `hφ.tendsto_atTop.eventually` 将每个 hA、hid 和 hpde 沿同一子列拉回。候选 A 不要求强收敛、弱收敛、逐点收敛、对称或在每个 n 上是 Uₙ 的全域弱 Hessian；Uₙ 自身也不要求 H²。逐测试最终身份比“每个 n 对全部测试成立”弱，适合后续内域穷竭。

已直接复核 C144 `exists_weakH2_of_gradient_test_limits` 和其基础。固定 i,j,ψ 后，最终身份与 Cauchy–Schwarz 给配对绝对值最终≤C₂‖ψ‖；配对极限和闭序界给同一极限测试泛函界。C143 的真实有界测试泛函表示内部构造每个 L² 二阶弱导数；它使用同范数 Hahn–Banach 延拓和实际 Riesz 表示，不假设目标导数存在。

混合导数的对称性随后由原 u 的两个一阶弱链和全部光滑测试的真实二次方向导数交换证明。只有在得到 Dᵢⱼ=Dⱼᵢ 后才经 Sym2 商下降，组装原 `Sym (Fin d) 2` 字段，并逐项检查全部二阶弱身份。结果 v 满足严格的 `truncate¹ v=u`，不是只有 value 相等或只给一个候选二阶数组。

真实字段平方范数是全部无序 Sym 分量平方范数之和，所以

\[
\|\operatorname{field}_2v\|_{L^2}^2
\le \#\mathrm{Sym}(\mathrm{Fin}\ d,2)\,C_2^2.
\]

维数因子明确保留，没有将每分量≤C₂错误宣称为整个 Hessian≤C₂，也没有混同有序 d² 计数与原无序纤维范数。零常数和 d=0 的空坐标情形均不涉及除法或不存在的坐标选择。

## 同一极限、原 H¹₀ 成员和严格负 Laplacian 等式

对同一 φ、同一 u，第6项给 `IsWeakNegativeLaplacian u f`。真实 H² 的 `negativeLaplacian_isWeak v` 给截断 v 的方程；用 `truncate¹ v=u` 后，这两个身份针对完全相同的弱 H¹ 状态。第5项于是证明严格 L² 等式 `negativeLaplacian v=f`，没有假设 candidate A 的迹已经等于 f。

截断等式的 value 分量给 value v=value u，以 u∈dirichletJetSpace S 为见证得到 value v∈dirichletSubspace S。因此 v 是同一原 H¹₀ 弱极限的真实 H² 提升，边界条件未替换成新的点态或弱迹假设。截断等式的0、1阶分量还准确保留原 C₁² 能量界，不需要额外弱下半连续性猜测或更换极限状态。

该最终结论适用于任意维数、任意开域；没有外加凸性、有界性、光滑边界或非空性。它也不声称一般 H¹₀ 函数的二阶零延拓为全空间 H²。候选分量将来可以由内域二阶导数延拓而来，但其资格、统一界和逐测试最终身份仍须在后续阶段逐项供应。

特别地，本定理的 ∃v 位于 U、hU、hb、A、hA、hid、hpde 之后。它没有消除这些逼近输入而证明“对任意 f 无条件存在 H² 解”，也没有产生 C₁、C₂≤C‖f‖ 的先验估计。原 P023 的域等式、椭圆正则估计和其余原假设不可由本阶段提前记为完成。

## 固定依赖、原稿、构建与公理

依赖验收门槛已通过：[C144 / T128](T128-local-acceptance.md) 供应真实对称 H² 提升及测试极限；[C143 / T127](T127-local-acceptance.md) 供应实际有界测试泛函表示；[C057 / T041](T041-local-acceptance.md) 供应实际负 Laplacian 和完整分布身份。本次另直接读取关键源码和上述 mathlib 弱对偶序列紧性、L² 第二可数性依据，未仅引用 PASS 标签。

四模块 Carleman 导入闭包共 **80** 模块，其中 **76** 个旧模块与 base 逐字节不变。C144 `WeakH2BoundedLimit` 的57模块闭包相对 base 不变；C143 `WeakDerivativeBoundedTest` 的35模块闭包相对 `b7491fa1b22b01515e8d0c428f35a3dbe301c34f` 不变；C057 `DirichletDistribution` 的57模块闭包相对 `3d5aa9cec281974bef7da9d37ffa11a8f9f75670` 不变。没有借用改变后的旧依赖版本。

已读治理协议、原稿及工具链 pin 自 T126 不变。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean固定4.35.0，mathlib pin及本机实际干净HEAD为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。固定 root 显式导入四模块；CheckAxioms 对7项输出完整类型与公理，并递归审计全部 Carleman 公开/私有声明，仅允许正常基础公理。

实际读取 `/tmp/carleman-dirichlet-limit-target.log` 的 **3235 jobs** 成功记录和 `-full.log` 的 **3910 jobs** 成功及 **6887声明递归审计PASS**。本验收核对这些固定日志，未声称重新运行全库。固定 `-local-axioms.txt` 为 **2,102,943 bytes**，SHA256 **`d3b1972e9ec476855a15f14dc1c37859133470d2b1b002fea9757157cfdc1ec4`**。

7/7项实际展开类型和公理已核验，均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。全部2385条非空公理记录及8条无公理记录均无异常集合；显式打印条数与6887项递归审计为不同统计。四新模块无 sorry/admit/新增 axiom，没有未证明的数学公理。

## 同 SHA 正式 CI 与独立下载证据

本 Agent 自行经 GitHub connector 查询 [main CI 39211640653 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39211640653/attempts/1)。实际run为main/push，head SHA精确匹配，最终completed/success，updated_at为 `2026-10-19T06:48:25Z`。三job全部completed/success：state-check **117926143158**、lean **117926143325**、dashboard / snapshot **117927344558**。Lean的pin、构建、结果记录和证据保存步骤全部成功；产物提前可下载时的 in_progress 状态未被当成最终通过。

同run原始artifact：`lean-ci-result` **12167763588**，压缩产物492 bytes，digest `sha256:1d4aebd25cd675a7d7ecdc6b5573471a67765d326c1652a4ff74e9cd98ca57e0`；`lean-declaration-evidence` **12168415346**，压缩产物193583 bytes，digest `sha256:705d00c61f999955fed1def6b31940d680d33bf36718f523ef490d5d784a6edf`。两份workflow_run元数据均绑定该run、main和精确SHA。本 Agent 自行用 `gh run download 39211640653` 下载至 `/tmp/carleman-dirichlet-limit-main-ci` 和 `-main-axioms`。

实际 `-main-ci/result.json` 为 **PASS**，`checked_sha=source_head_sha=bee8a93d0856f84c9280d10a19f50da7da2a362f`，targets为Carleman，`finished_at=2026-10-19T06:47:13.593959+00:00`，ci_url为上述run/attempt。Lean提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib为上述pin。解压result为537 bytes，SHA256 `4bc84b4a9106edb81ba1cd05371e170d32a392468fe9de1046c1e087ec142e54`。

独立逐字节比较真实远端 `-main-axioms/axioms.txt` 与固定本机副本，完全一致：**2,102,943 bytes**，SHA256 **`d3b1972e9ec476855a15f14dc1c37859133470d2b1b002fea9757157cfdc1ec4`**，末行实际为 **6887项全声明递归审计PASS**。包含本批全部7项实际展开类型和基础公理；原始文本摘要与artifact ZIP摘要分别记录。

## 验收决定

**C145：PASS，可升级为REVIEWED，scope保持AUXILIARY。** 7项声明未发现需修复的数学、类型、测试族、边界闭包、子列量词、弱极限或公理缺陷。同一原 H¹₀ 弱子列、真实二阶导数的内部构造、同一 f 的严格负 Laplacian 等式和两类量化界均成立；同SHA三项正式CI与独立下载的原始产物一致。

光滑内域解的正则性、Miranda–Talenti 型统一界和实际凸域穷竭尚待清偿。P023不提升，原文保持 **14/26**。本次仅新增本报告，未修改实现、台账、原稿或root导入，未commit/push。签发UTC如上固定；最终核对并通知主Agent后冻结报告内容及时间戳。
