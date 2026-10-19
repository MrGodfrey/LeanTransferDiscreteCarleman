# T100 / C116 独立本机验收

- `checked_sha`: `d8a513e72a1c480b4ecab1e2dcf3fe583ffc5527`
- `base_commit`: `e6f194345f2f7b9822f8d8654a003aee071382a2`
- `semantic_checked_at`: `2026-10-19T02:48:23+00:00`
- `reviewed_at`: `2026-10-19T02:51:09+00:00`
- `result`: **PASS**；固定版本语义、同 SHA 三项 CI 及原始产物核验均通过。
- `axiom_check`: **PASS**；远端原始产物与固定本机副本逐字节一致，6230 项递归审计通过。
- `scope`: **AUXILIARY**；完整原精确刚度恒等式 `eq:fdstiffness`，尚不等于完整 FD/P012。原文保持 **14/26**。
- 原式入口：`Carleman.cartesianFiniteDifferenceLaplacian_stiffness`；另有实际弱梯度配对版本 `Carleman.cartesianFiniteDifferenceLaplacian_weak_stiffness`。

本报告直接读取固定三模块全部 14 项源码、证明及完整实际类型，并读取有限循环平移、实际格点零延拓、Kuhn 单元梯度、精确单元积分/边组装及 Dirichlet scalarForm 识别等关键依赖。对照原 `paper/main.tex:1634–1704` 的标准 FD 模板、物理内积、真实重构和 `eq:fdstiffness`，并核对 `governance/analysis/T100-fd-stiffness.md`。本报告不以执行者说明或 CI 替代数学验收，后续工作树增量不在范围内。

## 全部 14 项声明

名称均加前缀 `Carleman.`；固定位置相对于 `Carleman/`。

| # | 声明 | 固定位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `cartesianInteriorToBox` | `Geometry/FiniteCartesianInteriorSum.lean:12` | PASS；原内部索引 a 逐轴映到半开盒索引 a+1，有限索引上界由真实算术给出。 |
| 2 | `cartesianInteriorToBox_injective` | `Geometry/FiniteCartesianInteriorSum.lean:15` | PASS；逐坐标相等及自然数加一单射证明实际注入，不假设节点枚举。 |
| 3 | `cartesian_sum_zero_faces_to_interior` | `Geometry/FiniteCartesianInteriorSum.lean:24` | PASS；像外点必有零坐标，只删明确为零的项，内部求和无系数或基数损失。 |
| 4 | `cartesianLatticePredecessor` | `Spatial/CartesianSummationByParts.lean:11` | PASS；真实整数格轴向前驱 z−e_r。 |
| 5 | `cartesianLatticePredecessor_successor` | `Spatial/CartesianSummationByParts.lean:14` | PASS；同轴先后继再前驱严格返回 z，没有模周期定义。 |
| 6 | `cartesian_sum_axis_shift` | `Spatial/CartesianSummationByParts.lean:19` | PASS；实际有限轴向平移，两个端面均由显式零值条件处理。 |
| 7 | `cartesian_sum_axis_by_parts` | `Spatial/CartesianSummationByParts.lean:33` | PASS；任意独立 F/G，G 在两端为零给正号中心差分与前向差乘积的精确身份。 |
| 8 | `cartesianPhysicalInner` | `Spatial/CartesianFiniteDifference.lean:15` | PASS；直接为原物理质量 `(∏δ_j)Σ_af_ag_a`，未换系数范数或一致质量。 |
| 9 | `cartesianFiniteDifferenceLaplacian` | `Spatial/CartesianFiniteDifference.lean:18` | PASS；直接为原 2d+1 点模板 Σ_r(2f_a−f_{a+e_r}−f_{a−e_r})/δ_r²，邻居取原数据零延拓。 |
| 10 | `cartesianLatticeData_at_interior` | `Spatial/CartesianFiniteDifference.lean:24` | PASS；正步长的实际节点单射保证内部格点值恰为原 f_a。 |
| 11 | `cartesianAxisDifference_sum_by_parts` | `Spatial/CartesianFiniteDifference.lean:29` | PASS；对真实 f/g 零边界数据调用第 7 项，两个 δ_r 分母精确成为 δ_r²。 |
| 12 | `cartesianFiniteDifferenceLaplacian_pairing_edges` | `Spatial/CartesianFiniteDifference.lean:43` | PASS；全部轴有限求和、实际内部索引删除零项后，原物理配对等于实际坐标边交叉配对。 |
| 13 | `cartesianFiniteDifferenceLaplacian_weak_stiffness` | `Spatial/CartesianFiniteDifference.lean:74` | PASS；接入真实重构边组装，得到原算子物理配对等于完整真实 L² 弱梯度配对。 |
| 14 | `cartesianFiniteDifferenceLaplacian_stiffness` | `Spatial/CartesianFiniteDifference.lean:82` | PASS；同一实际 H¹₀ 重构进入原 Dirichlet scalarForm，完整实现原 `eq:fdstiffness`，f/g 独立。 |

## 原对象与实际模板

原文对正维数 d、矩形 Ω=∏(0,L_j)、N_j≥2，取 δ_j=L_j/N_j，内部整数索引 1,…,N_j−1，边界值零，物理节点质量 ω=∏δ_j。代码使用 `CartesianInteriorIndex N=∀j,Fin(N_j−1)`，物理整数坐标为索引值加一；取 o=0 即原节点，允许任意 o 只是增加平移自由度。

`cartesianInteriorData` 按真实物理节点注入将有限数据延拓到空间点；正 δ 使该注入单射。在内部节点处数据严格等于原 f_a，非节点或原域外为零。`cartesianLatticeData` 只是把同一数据在真实整数格点 `o+zδ` 上取值，未另造周期数据或任意扩展。原边界整数坐标 0 或 N_j 对应物理开域外的端面，因此其值为零；边界判定不要求其余坐标也在盒内。

新增算子在每个原内部 a 上直接定义

`A_hf(a)=Σ_r [2f(a)−F(a+e_r)−F(a−e_r)]/δ_r²`，

其中 F 是上述真实零延拓。逐轴后继/前驱用整数加减一；靠边界的邻居恰落到相应零边界节点，首末内部层均保留。没有将 A_h 定义为刚度矩阵从而循环证明目标，也没有缩放成 δ_r⁻¹ 或另加零阶项。

`cartesianPhysicalInner δ N f g=(∏δ_j)Σ_af_ag_a` 精确是原节点物理内积的显式求和式。原每点质量恒定，移出有限和不改变定义。它不是原重构的 L² 一致质量矩阵，更不是无质量的 Euclidean 点积。正步长供应真实物理正质量；原式无需额外网格可比性。

最终所有 f、g 独立且任意，既非只证 f=g 的平方能量，也非只针对基向量、特殊符号或低频子空间。结论是精确等式，不含估计常数或误差容差。

## 两端有限求和分部

辅助求和域为半开整数盒 Z=∏_j{0,…,N_j−1}，而实际函数 F、G 定义在全部整数格上。`cartesian_sum_axis_shift` 并没有将格函数视为周期函数：它调用真实有限索引置换来重排求和，但将循环环绕两侧的函数值分别用原端面零值处理。

直接读取 `FiniteCartesianShift`：逐坐标 `finRotate` 是有限集合上的真双射；未到上端的项对应通常加一。若某个平移坐标从 N_j−1 环绕，实际平移点该坐标是 N_j，置换点是 0，两项分别由 hF 在上端和下端为零而相等。若不环绕，则两份整数坐标逐项严格相同。由此成立的是有限零边界平移身份，不是忽略边界项的形式换元。

对一般独立 F/G，只需 G 在本轴 0、N_r 两端消失。代码分别把上述平移身份应用于 `F(z)G(z)` 和 `F(z−e_r)G(z)`。即使 F 不在两端为零，这两个乘积仍因 G 而为零。前驱/后继严格抵消，因此得到

`Σ_Z F(z+e_r)G(z+e_r)=Σ_Z F(z)G(z)`，

`Σ_Z F(z)G(z+e_r)=Σ_Z F(z−e_r)G(z)`。

展开前向差乘积四项，代入两式，精确得到

`Σ_Z [F(z+e_r)−F(z)][G(z+e_r)−G(z)]`

`=Σ_Z [2F(z)−F(z+e_r)−F(z−e_r)]G(z)`。

中心系数为正 2，两个相邻项为负，与原 A_h=−Δ_h 的符号一致。上端 z_r=N_r−1 对应的边和下端 z_r=0 对应的边都参与原前向差和，未删去与首末内部节点相接的边。代入实际零边界数据后，两个差商的分母乘积精确为 δ_r²，故物理差商层的等式也无额外因子。

## 从半开盒到完整内部节点

轴向分部求和后，有限轴和换序，得到半开盒上 `F_op(z)G(z)` 的和。若任意坐标 z_j=0，原测试数据 G(z) 确实为零，所以该项为零；这里只利用 G 的值，不需要 F_op 在该点为零，即使它访问了盒外前驱也无影响。

新 `cartesianInteriorToBox` 是实际逐轴 a↦a+1 的单射。对半开盒中不在其像内的 z，若所有坐标均非零，逐轴 `(z_j−1)` 就构造出 `Fin(N_j−1)` 内部索引且映回 z，矛盾。因此像外每项确有一个零坐标，前述零值条件全部清偿。`Fintype.sum_of_injective` 只删除这些零项，绝不删掉非零的边界邻近内部状态。

最后对每个真实内部 a，用 `cartesianLatticeData_at_interior` 将 F(a)、G(a) 分别还原为 f_a、g_a。原轴向邻居仍保留同一整数零延拓，正好得到新定义的标准 Laplacian。物理质量 ω 在全程同乘，得 `(A_hf,g)_X=ωΣ_ZΣ_r D_r^+F D_r^+G`。

## 真实梯度、单元组装与原形式

本次没有仅因 T099 已验收而跳过右端识别，已读取 `KuhnNodalGradient`、`CartesianKuhnCellStiffness`、`CartesianLatticeDifferences`、`CartesianKuhnEdgeAssembly` 和 `KuhnCellVolume`。

原真实 R_hf 是全部内部连续 Kuhn 帽的有限和，实际 L² 类已经证明属于原 H¹₀ 图闭包。`cartesianKuhnReconstructionJet` 是这份值的真实弱 H¹ jet，其每个闭单元弱梯度 a.e. 等于同一 P1 仿射函数的 Fréchet 导数。局部坐标公式从实际相邻顶点差 `v_{k+1}−v_k=δ_{π(k)}e_{π(k)}` 和仿射值差推出，故

`∂_{π(k)}R_hf=[f(v_{k+1})−f(v_k)]/δ_{π(k)}`。

这不是人为指定的离散梯度。对任意 f/g 的真实 Euclidean 梯度内积，该公式逐分量给差商乘积有限和。单元积分为真实 Lebesgue 体积乘该常数；全域积分使用实际分割和 L²×L² 内积可积性，闭单元公共边界零测不会重复贡献。

在 T099 的边组装中，每个 Kuhn 步长是一个实际坐标轴差，出发点相对盒原点仅增加此前排列方向的前缀指示。当前轴不在该前缀中；在任何平移的横向端面上，差商两端数据皆为零，所以对应差商乘积为零。真实有限零边界平移将此前缀去掉。然后对排列 k→π(k) 重排轴和，得到与 π 无关的完整坐标边配对。

真实单元体积的格点平移不变性由 Lebesgue 平移换元给出；固定盒全部排列单元的体积之和由实际 Kuhn 分割积分得到 ω=∏δ_j。证明据此将体积和严格合并为原物理质量，而非假设每条边恰有 d! 个单元或加入未证等体积条件。最终的坐标边和与本批分部求和所得完全一致，因此弱梯度版本精确成立。

`weakGradientPairing U V` 定义为原真实第一阶 L² 字段内积，分量各计一次。`boundedDirichletOriginalForm` 的 V 是原 `dirichletSubspace`，形式为同一全梯度 L² 内积，没有添加质量项。`dirichlet_scalarForm_eq` 使用值到原能量空间的等价及真实 H¹ jet 的唯一性，将标量 H¹₀ 值上的原 scalarForm 识别为相同弱梯度配对。

最终 scalarForm 接受的两份 subtype 值就是原 R_hf、R_hg 的实际 L² 类；其 H¹₀ 资格由既有真实闭包定理内部供应。于是第 14 项确实是原 `(A_hf,g)_{X_h}=a(R_hf,R_hg)`，而非另一个能量、任意 Hilbert 空间或附加假设下的身份。

## 量词、退化情形和覆盖边界

原所有 d≥1、N_j≥2 和 δ_j>0 均在最终定理中。允许任意平移以及任意正各向异性步长，省略原步长可比性只加强精确等式。没有 q、h 小条件、周期或时间方向参数，故刚度身份本身对这些参数没有隐含依赖。f/g 全独立，零向量和任意正负混合数据不需分情况。

弱梯度版本和求和代数还允许 d=0；此时没有坐标轴项，恒等式相应为零。原 scalarForm 版本明确要求 d>0，与原正维数一致。允许 N_j=0 或 1 等无内部节点情形时，相关有限类型为空或数据零延拓为零；并未用这些退化情况替代原 N_j≥2 的证明，也未对首末层增加支持限制。

结论完整清偿原标准 FD 模板的 `eq:fdstiffness`，为原刚度缺陷为零提供精确等式基础。不过完整 FD/P012 还包含真实测试、观察和数值接口组装等要求；本批没有完成这些整包义务。故 C116 保持 **AUXILIARY**，不得把精确刚度身份单独计为新的完整具名论文结果，原文保持 **14/26**。

## 固定版本、构建与递归公理

三个新模块的 Carleman 导入闭包共 228 个模块，其中 225 个既有模块相对 base 逐字节未改；root 显式导入三个新模块。已读 AGENTS、操作协议和 state 协议在本次固定版相对 base 未变；原稿、Lean/mathlib pin 及两个 CI workflows 也未改。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

实际固定 `/tmp/carleman-fd-stiffness-target.log` 显示定向 3406 jobs 成功；`/tmp/carleman-fd-stiffness-full.log` 显示全库 3804 jobs 成功并完成 6230 声明递归审计。固定 `/tmp/carleman-fd-stiffness-local-axioms.txt` 为 1,859,659 bytes，SHA256 `6b4f01d9f484418c733ff5a125e7d256e7b3e06bae77b293da5e691c155aef3d`。

全部 14 项完整实际类型与源码逐项对照，每项恰有一条类型和一条公理结果。`cartesianLatticePredecessor` 无公理；`cartesianInteriorToBox`、其单射定理及前驱后继定理仅用 propext/Quot.sound；其余本批声明只用正常三项基础公理。全产物 2077 条带公理打印（2073 个不同带公理声明）及 8 条无公理打印已扫描，无白名单外公理。末行实际为 `Axiom audit passed for all 6230 Carleman declarations.`。

递归审计程序相对 base 原样未改，仍使用 collectAxioms 检查整个 Carleman 声明环境及生成私有声明。本批没有 sorry、admit、native_decide 或新增数学公理。

## 远端证据与正式签发

已自行查询 [main CI run 39191534685 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39191534685/attempts/1)，确认事件 `push`、分支 `main`、head SHA 为本次固定 `d8a513e72a1c480b4ecab1e2dcf3fe583ffc5527`。run 最终 `completed/success`，最后更新时间 `2026-10-19T02:49:19Z`；三个实际 jobs 全部最终成功：

| Job | ID | 最终状态 |
|---|---|---|
| `lean` | `117865201099` | `completed/success` |
| `state-check` | `117865201304` | `completed/success` |
| `dashboard / snapshot` | `117865832666` | `completed/success` |

已独立查询 artifact 元数据，`lean-ci-result`（ID `12159498708`）及 `lean-declaration-evidence`（ID `12160111930`）均未过期，且各自绑定同 run、main 分支及上述固定 SHA。本 Agent 自行下载这两份原始产物，两个下载进程均 exit 0。

原始 `/tmp/carleman-fd-stiffness-main-ci/result.json` 实际为 `status=PASS`，`checked_sha=source_head_sha=d8a513e72a1c480b4ecab1e2dcf3fe583ffc5527`，`finished_at=2026-10-19T02:48:12.359054+00:00`，target 为 `Carleman`。Lean 4.35.0 Linux commit 为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib commit 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，与固定源码 pin 一致。

原始 `/tmp/carleman-fd-stiffness-main-axioms/axioms.txt` 与固定本机副本已独立逐字节比对，完全一致：1,859,659 bytes，SHA256 `6b4f01d9f484418c733ff5a125e7d256e7b3e06bae77b293da5e691c155aef3d`。14 项实际类型及公理结果再次逐项核对，每项各一条；全产物 2077 条带公理打印只含三项正常基础公理，另有 8 条无公理打印，末行确认全部 6230 声明递归审计通过。未采用后续工作树 `.ci/axioms.txt`。

正式签发 **AUXILIARY / PASS**，未发现本批原精确刚度身份范围内的数学缺陷。可将 **C116 按 AUXILIARY / REVIEWED** 记录；原文保持 **14/26**，完整 FD/P012 不提升。本 Agent 仅写本报告并下载临时验收证据，未修改实现、台账、root 或原稿，未 commit/push。
