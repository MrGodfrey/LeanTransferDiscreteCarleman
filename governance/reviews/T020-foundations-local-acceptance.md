# T020 基础层本机独立验收：C038 / C039

- `checked_sha`: `a315bdc449c58a705a982f0d009f1dde24d6af66`
- `reviewed_at`: `2026-10-18T14:30:45+00:00`（UTC）
- 审核范围：该 SHA 的 `state/progress.json` 中 C038 的 35 项、C039 的 17 项显式声明，共 52 项；两者均保持 `AUXILIARY`。
- `result`: **PASS**（C038）；**PASS**（C039）。
- `axiom_check`: **PASS**（全部 52 项及本次 CI 的递归依赖审计）。

本报告由独立验收 agent 从固定提交的实际 Lean 陈述、证明和相关定义核对。源码使用 `git archive` 导出的固定树，原文使用该树中的 `paper/main.tex`；执行者的 analysis 文档只用于定位，未以其结论替代检查。没有审核或导入工作区内新写的未提交数学模块，也没有修改数学代码、台账、根导入或论文。

## 固定版本、构建与依赖

通过 GitHub connector 独立读取 [main CI 39135593975 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39135593975/attempts/1) 的 run 和 jobs：`event=push`、`head_branch=main`、`head_sha=a315bdc449c58a705a982f0d009f1dde24d6af66`、`status=completed`、`conclusion=success`。`lean`、`state-check`、`dashboard / snapshot` 三项及 Lean 构建步骤实际成功。

实际读取 `/tmp/carleman-spatial-main-ci/result.json`：`checked_sha`、`source_head_sha` 均为上述 SHA，`status=PASS`，目标 `Carleman`，完成时间 `2026-10-18T14:23:13.156876+00:00`。其 Lean 4.35.0 和 mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 与固定源码的 `lean-toolchain`、`lake-manifest.json` 相符。本次复用同 SHA 的真实完整构建，没有声称重新执行本机构建。

逐项检查 52 个声明均列入 `tools/CheckAxioms.lean` 的显式 `#check` 与 `#print axioms`，其定义模块均由 `Carleman.lean` 导入。实际公理产物 `/tmp/carleman-spatial-main-axioms/axioms.txt` 中全部 52 项都有类型及公理输出，仅含正常基础公理 `propext`、`Classical.choice`、`Quot.sound`。产物末尾为 `Axiom audit passed for all 3080 Carleman declarations.`；固定版审计程序用 `collectAxioms` 遍历所有公开及私有 Carleman 声明，任何不在此三项许可集合内的公理均报错。因此没有 `sorryAx` 或额外数学公理依赖。

产物 SHA256：

- `result.json`：`eb372dc6fe602b636bb3e82371d83cc73ffb6216b650e968a113f5358c08bd4a`。
- `axioms.txt`：`4cf5509f91b61e80901ab0f86484133c25cf95cd92f58849a473a01189a98278`。

旧声明版本没有被直接沿用为本次审核版本。比较每个 claim 的声明模块及递归本地 import 闭包：

| Claim | 旧 `declaration_version` | 直接模块 / 含自身的本地依赖模块 | 到本次 SHA 的相关变化 |
| --- | --- | --- | --- |
| C038 | `7f17beb74fbc260084d425126cc719187b0caaac` | 7 / 86 | 闭包内文件零变化 |
| C039 | `010b37869003458f0e1436e3804e11c807f550e9` | 6 / 146 | 闭包内文件零变化 |

两段版本差异的 Lean 源码变化均为下游新模块、根导入和显式审计清单扩充；工具链及 mathlib pin 不变。即便相关依赖未变，本次语义结论和构建证据仍统一绑定新 SHA，不混用旧 SHA 构建与新 SHA 审核。

## 数学审查分组

下列 G1–G10 对应后面的完整声明清单，每组均为 PASS。

### G1：可变测试算子的精确周期恒等式

`sum_variable_bilinear_increment` 以任意有限置换 τ 重编号，真实展开双线性形式，得到两倍时间增量配对等于增量能量加上 `B_i(u_i,u_i)-B_(τ⁻¹i)(u_i,u_i)`。对称性只在同一节点使用，没有要求相邻算子交换。

`pairing_variable_operator` 实际消去 `dt * dt⁻¹`。正方向邻点为 prev，所以变化项为 `T_i-T_next(i)`；反方向邻点为 next，所以变化项为 `T_i-T_prev(i)`。这与原文 `eq:weighted-time-summation` 及反射方向一致，D− 仍是 `(u_i-u_next)/dt`。`pairing_variable_operator_lower` 只用正半定性丢弃增量能量，并以实际节点算子差分界得到 `−(dt/2)∑b_i`。允许整个有限周期状态空间，包括更强的 N=1 情形；原文 N≥2 因而包含在内。

### G2：真实导数到节点增量、周期末格与 36 / 18 常数

`testOperator_cell_increment` 的 `hder` 是二次型 `⟨z,T(t)z⟩` 的真实 `HasDerivWithinAt`，不是任意命名导数字段。先把 `[0,T]` 的导数限制到未取模闭单元，再用导数界推出长度恰为 dt 的增量界。`CellAnchor.next_node_value` 通过 `T(0)=T(T)` 把最后一个右端点 T 转回周期零节点。

D+ 的下界使用本节点之后的单元；D− 使用 prev 节点之后的单元，以本节点为右锚点，利用负差的绝对值界。没有把跨周期的节点时刻差误认为 dt。

实际 q 比较常数 2 来自 `TimeWeightRegularity.comparable`，实际 L² 权乘法比较常数 3 来自 `SpatialProfile.seminorm_cell_le`。`test_mass_cell_le` 因而得到 `q(t)‖σ(t)Rz‖ ≤ 6 q(s)‖σ(s)Rz‖`；非负性允许平方，`test_derivative_cell_bound` 得到 `36 C`。精确恒等式中的 1/2 给出时间下界 `−18 C dt∑(q_i‖σ_iR u_i‖)²`。

D− 的零节点使用最后闭单元的右端点 T：q 由 `h.endpoint`、σ 由其实际乘子定义和同一 q 端点等式、测试算子由 `hend` 分别转回 0。小性条件仍明确为既有 cell comparison 所需的两条条件；36、18 不依赖 T、qmax 或节点数。

### G3：实际方程相减与非正交重构

`Reconstruction` 数据仅含时间无关的线性 R、J 及质量伴随。Q 定义为 RJ，G 定义为 JR（含 V→H 嵌入）；相关证明没有投影、正交性或 `G=Id` 假设。`difference_map/sub` 让真实周期差分与这些固定线性映射及相减交换。

`spatialForm` 是原 `a(v,w)+μ⟨v,w⟩_H`，两槽相减等式仅用双线性。`spatial_continuous_test` 从原 D(A) 上的算子 Euler 方程及算子—形式测试等式取内积。`spatial_discrete_test` 从 `Dεz+A_hz+μGz=Jf` 得到实际重构测试式，刚度缺陷保持原正号。

`spatial_error_equation` 将这两式相减，取 `e_h=z−Ju`、`η=u−Qu`，确实得到
`⟨Dεe_h,v⟩+a_μ(Re_h,Rv)+b_h(e_h,v)=a_μ(η,Rv)−b_h(Ju,v)`。
两处刚度缺陷没有遗漏或变号。这里输入的是原方程/其变分形式，没有输入目标误差估计；C038 同时提供从强方程到该变分输入的桥。

### G4：完整三项对偶恒等式

`spatial_consistency_identity` 用实际离散方程测试 JY，再用连续方程测试 QY，保留真实误差 `e_s=u−Rz`。逐节点结果含 `⟨Dεu,Y−QY⟩`、`a_μ(e_s,Y−QY)` 和 `+b_h(z,JY)`，对应原 `eq:completeidentity` 的最后一行。

`pairing_difference_opposite` 用已有周期求和分部给出 `Dε* = D(opposite ε)`，没有额外负号。`spatial_complete_identity` 用对称形式及真实反向变分 Euler 方程转移差分，得到完整求和式。`spatial_weighted_duality` 的真实载荷为 `W_i(W_i e_s,i)`，由 W 自伴性得到左端 `dt∑‖W_i e_s,i‖²`。它允许一般自伴线性权算子，不假定 W 正性；该平方等式本就不需要正性。

这组声明输入一个满足反向方程的 Y，证明的是恒等式；对偶解构造和各项率估计不在 C038 的声明中，也没有被其 scope 冒认完成。

### G5：真实有限维全状态离散适定性

`auxiliaryEuler` 是整个周期序列空间上的线性映射 `Dε+ A_h+μG`。`auxiliaryEuler_injective` 调用的两方向唯一性实际使用时间能量非负、A_h 非负，以及 R 单射推出 G 正定和 μ_i>0；没有频率限制、网格小性或假设最终唯一性。

`existsUnique_auxiliaryEuler` 使用有限维 X 以及有限节点集，应用有限维线性自映射“单射等价满射”，对任意 `f : Index→X` 得到存在唯一解。它涵盖原特殊载荷 Jg，并保留全部离散状态。这里有限维只加在论文原本有限维的 X，没有强加给连续 H。

### G6：真实弱 Sobolev 能量的半范数表示

`weightedFieldMap` 把实际弱 jet 的每阶 L² 导数字段映为 `q^(m−k) σ D^k u`，放入 Hilbert 乘积 `HilbertJetFields`。`weightedFieldMap_norm_sq` 用该乘积的平方范数等式识别为原 `weightedSq`，从非负性与平方相等识别 `weightedSeminorm=weightedNorm`。随后加法/减法三角不等式是这个真实半范数的性质。

`conformingWeightedSeminorm` 通过实际 `domainSobolevJet` 复合，`conformingWeightedSeminorm_apply` 识别为原 conformingWeightedNorm。底层 jet 的字段受真实分布弱导数关系约束，零阶是原 L² 值。没有把 V 的 H 诱导范数充当 H^m 能量范数，也没有引入未识别的替代误差标量。

### G7：dt 序列范数代数与无网格损失的提升

`TimeGrid.weightedNorm` 是 `sqrt(dt∑p_i(u_i)²)`。`weightedNorm_product_sum` 使用有限和 Cauchy–Schwarz 并精确合并两项 sqrt(dt)。加法三角式由平方展开及该交叉项界推出，减法利用半范数对负号不变；节点上界同常数提升为序列上界。`weighted_bilinear_sum_bound` 先三角再 Cauchy–Schwarz，把逐节点形式/缺陷上界以完全相同的常数提升。

`weightedNorm_sum_le` 迭代三角不等式，`weightedNorm_le_field_sum` 先将各字段范数视为非负实序列，再用有限 Minkowski。结论是 `C∑_k‖f_k‖_(ℓ²_dt)`，没有使用粗糙的节点计数界；不存在 N、sqrt(N)、T 或 sqrt(T) 因子。

### G8：σ² 测试的原权族范围

`squared_weight_test_uniform` 的常数在 w、τ、t、v 之前选取。证明调用内禀 `SmoothOnClosure` 与有界域上的正/逆权共轭比较，设正权乘法 W、原逆权乘法 I，以真实乘子消去证明 `I(W(Wv))=Wv`。两次已有比较给出 `N_(σ⁻¹)(σ²v)≤J²N_σ(v)`。

这里 σ² 是两次同一 σ 的乘法，V 保持性只调用原 σ 及原 σ⁻¹；没有把 `2τ` 或 `2ρ` 当作新的允许权要求 N1–N4 成立，也没有要求在域外存在光滑延拓。τ 可任意的空间代数比较不增加原数值假设的权族范围。

### G9：Céa 测试、缺陷吸收及真实空间实例

`spatial_test_stability` 从 `RTe−MRe` 的 superapproximation 和 M 乘法界得到 `Ct=ε+CM`。`spatial_test_node` 展开真实测试误差，逐项留下连续形式测试缺陷 `Cf ε`、刚度缺陷 `ηA Ct`、逼近项和 `Ju` 缺陷项，质量余量 `B mass²` 仍在左侧。

`spatial_test_energy_bound` 用 G7 求和，时间下界与质量余量相消；条件 `Cf ε+ηA Ct≤c/2` 恰留下 `c/2` 的能量。证明先处理误差半范数为零的分支，再在正分支消去该范数，没有非法除零。结果为 `(2/c) Ct [Cf N(η)+ηA N(RJu)]`，没有给定目标误差结论作为输入。

`OriginalForm.bilinearForm_apply` 是定义等式，保证线性映射形式仍为原 scalarForm。`Section4.energySeminorm` 用 G6 的实际弱 Sobolev N。`Section4.spatial_cea` 以此具体化：内部使用 G2 证明两方向 `18 Ctime` 时间下界，并使用 G3 从实际两方程导出测试误差方程。

本入口仍显式接收 `hform`、带 `18 Ctime` 余量的 `hcoer`、`hmul` 和 `hsmall`。它是正确的辅助 Céa 定理，不单独声称已在原参数族上选择统一空间阈值或已给出完整 Lemma 4.1。更高层如何供应这些输入需要其独立验收；本报告不据此扩大 C039 范围。

### G10：N3 节点 R 范数与低阶 N 比较

`nodal_approximation_bound` 展开真实空间 parameterNorm，把其第 k 项精确写为 `‖q_i^(n−k) σ_i D^k u_i‖`，由 G7 得到与 Section3 完全相同的 `nodeParameterNorm = ∑_k ‖q^(n−k)σD^k u‖_(ℓ²_dt)`。这从逐节点 N3 界推出序列界，没有把序列误差估计另设为假设。

`weightedNorm_truncate_le_parameterNorm` 在 m≤n、q≥1 时先用 N≤逐阶和，再比较幂次及取高阶 R 的单项界，所得固定常数 m+1 是有效而较宽松的阶数常数。`conforming_energy_le_parameterNorm` 先用弱 jet 值映射的单射性识别原域低阶 jet 与高阶 jet 的截断，随后应用该估计。没有假设不相干的两套导数字段相等，也没有产生 T 或节点数损失。

## 全部显式声明清单

以下每项均在上述固定 SHA 检查，分组列同时指向其数学审查；每项结果均为 PASS。

### C038（35 项，AUXILIARY）

| # | 声明 | 分组 |
| --- | --- | --- |
| 1 | `Carleman.sum_variable_bilinear_increment` | G1 |
| 2 | `Carleman.TimeGrid.pairing_variable_operator` | G1 |
| 3 | `Carleman.TimeGrid.pairing_variable_operator_lower` | G1 |
| 4 | `Carleman.Orientation.difference_map` | G3 |
| 5 | `Carleman.Orientation.difference_sub` | G3 |
| 6 | `Carleman.Reconstruction.spatialForm` | G3 |
| 7 | `Carleman.Reconstruction.spatialForm_sub_left` | G3 |
| 8 | `Carleman.Reconstruction.spatialForm_sub_right` | G3 |
| 9 | `Carleman.Reconstruction.spatial_continuous_test` | G3 |
| 10 | `Carleman.Reconstruction.spatial_discrete_test` | G3 |
| 11 | `Carleman.Reconstruction.spatial_error_equation` | G3 |
| 12 | `Carleman.Reconstruction.spatial_consistency_identity` | G4 |
| 13 | `Carleman.Orientation.pairing_difference_opposite` | G4 |
| 14 | `Carleman.Reconstruction.spatial_complete_identity` | G4 |
| 15 | `Carleman.Reconstruction.spatial_weighted_duality` | G4 |
| 16 | `Carleman.Reconstruction.auxiliaryEuler` | G5 |
| 17 | `Carleman.Reconstruction.auxiliaryEuler_injective` | G5 |
| 18 | `Carleman.Reconstruction.existsUnique_auxiliaryEuler` | G5 |
| 19 | `Carleman.TimeGrid.testOperator_cell_increment` | G2 |
| 20 | `Carleman.TimeGrid.pairing_testOperator_dPlus_lower` | G2 |
| 21 | `Carleman.TimeGrid.pairing_testOperator_dMinus_lower` | G2 |
| 22 | `Carleman.WeakSobolevJet.weightedFieldMap` | G6 |
| 23 | `Carleman.WeakSobolevJet.weightedFieldMap_norm_sq` | G6 |
| 24 | `Carleman.WeakSobolevJet.weightedSeminorm` | G6 |
| 25 | `Carleman.WeakSobolevJet.weightedSeminorm_apply` | G6 |
| 26 | `Carleman.WeakSobolevJet.weightedNorm_add_le` | G6 |
| 27 | `Carleman.WeakSobolevJet.weightedNorm_sub_le` | G6 |
| 28 | `Carleman.conformingWeightedSeminorm` | G6 |
| 29 | `Carleman.conformingWeightedSeminorm_apply` | G6 |
| 30 | `Carleman.TimeGrid.weightedNorm_nonneg` | G7 |
| 31 | `Carleman.TimeGrid.weightedNorm_product_sum` | G7 |
| 32 | `Carleman.TimeGrid.weightedNorm_add_le` | G7 |
| 33 | `Carleman.TimeGrid.weightedNorm_sub_le` | G7 |
| 34 | `Carleman.TimeGrid.weightedNorm_le_of_bound` | G7 |
| 35 | `Carleman.TimeGrid.weighted_bilinear_sum_bound` | G7 |

### C039（17 项，AUXILIARY）

| # | 声明 | 分组 |
| --- | --- | --- |
| 1 | `Carleman.SpatialProfile.test_mass_cell_le` | G2 |
| 2 | `Carleman.SpatialProfile.test_derivative_cell_bound` | G2 |
| 3 | `Carleman.SpatialProfile.pairing_test_dPlus_lower` | G2 |
| 4 | `Carleman.SpatialProfile.pairing_test_dMinus_lower` | G2 |
| 5 | `Carleman.Reconstruction.spatial_test_stability` | G9 |
| 6 | `Carleman.Reconstruction.spatial_test_node` | G9 |
| 7 | `Carleman.Reconstruction.spatial_test_energy_bound` | G9 |
| 8 | `Carleman.squared_weight_test_uniform` | G8 |
| 9 | `Carleman.OriginalForm.bilinearForm` | G9 |
| 10 | `Carleman.OriginalForm.bilinearForm_apply` | G9 |
| 11 | `Carleman.Section4.energySeminorm` | G9 |
| 12 | `Carleman.Section4.spatial_cea` | G9 |
| 13 | `Carleman.TimeGrid.weightedNorm_sum_le` | G7 |
| 14 | `Carleman.TimeGrid.weightedNorm_le_field_sum` | G7 |
| 15 | `Carleman.WeakSobolevJet.weightedNorm_truncate_le_parameterNorm` | G10 |
| 16 | `Carleman.WeakSobolevJet.nodal_approximation_bound` | G10 |
| 17 | `Carleman.Section4.conforming_energy_le_parameterNorm` | G10 |

## 验收结论与状态边界

C038 的 35 项和 C039 的 17 项均可在本报告 `checked_sha` 下升级为 `REVIEWED`，`scope` 继续为 `AUXILIARY`；台账应同步该 SHA 的构建证据与本报告的语义审核引用。没有发现阻断升级的陈述、证明、依赖或常数问题。

上述明确输入与较宽松的固定 m+1 常数属于正确的辅助接口边界，不是隐藏的证明缺口。C038/C039 的审核不自动验收下游完整空间率、统一阈值或任何论文级入口，也不据此增加原文完成计数；Lemma 4.1、Theorem 4.2 和 Theorem 2.1 均必须按各自完整声明另行验收。
