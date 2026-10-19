# T089 / C105 独立本机验收

- `checked_sha`: `f2e5416279274e334edf8df2d2e43ce3a4d23c39`
- `base_commit`: `b54a0a22a2352ab389a1cb109f1d60386ca2261a`
- `reviewed_at`: `2026-10-19T01:15:09+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：实际有限网格内部节点帽函数的零阶质量，以及结合已验收真实向量一阶矩后的完整仿射矩再现。载荷右逆／稳定性、完整FD与B.2仍待；原文保持 **13/26**。

独立从固定提交导出源码，读取四模块全部证明、15项完整展开类型及关键依赖，对照固定 `paper/main.tex` Appendix B Step 1的 `eq:fdmoments` 和原 `(J_hp)_i=p(x_i)`（TeX 2741–2755），以及Section 6真实Cartesian/Kuhn网格、质量和J_h定义。执行者规格和CI没有代替数学核对；后续工作区增量不属于本报告。

## 全部15项声明

名称均省略公共前缀 `Carleman.`，位置以 `Carleman/` 为根；顺序与交付JSON一致。

| # | 声明 | 固定位置 | 独立数学核对 |
|---|---|---|---|
| 1 | `openCoordinateBox_volume_real` | `Geometry/KuhnCellVolume.lean:15` | PASS；真实欧氏体积经ofLp保测度与坐标乘积区间体积给∏(bⱼ−aⱼ)。 |
| 2 | `cartesianKuhnSimplex_translation_vertex` | `Geometry/KuhnCellVolume.lean:28` | PASS；实际平移zδ把原点单元每个顶点送到同排列格点单元对应顶点。 |
| 3 | `cartesianKuhnSimplex_volume_translation` | `Geometry/KuhnCellVolume.lean:42` | PASS；真实闭凸包平移身份与Lebesgue保测度给单元体积相等。 |
| 4 | `cartesianKuhnSimplex_sum_permutation_volume` | `Geometry/KuhnCellVolume.lean:62` | PASS；N=1的真实有限分割积分常函数1，得到全部排列单元总体积∏δⱼ。 |
| 5 | `cartesianKuhn_origin_eq_of_vertex_eq` | `Geometry/KuhnNodeIncidence.lean:13` | PASS；固定排列和顶点位置，真实顶点相等经正δ消去得到整数原点相等。 |
| 6 | `cartesianFiniteSimplex_fixed_vertex_injective` | `Geometry/KuhnNodeIncidence.lean:24` | PASS；真实有限格点坐标映到固定位置顶点的映射是注入。 |
| 7 | `cartesianKuhn_node_incidence_unique` | `Geometry/KuhnNodeIncidence.lean:35` | PASS；任意内部节点、排列及顶点位置恰有一个真实有限格点原点。 |
| 8 | `cartesianKuhn_node_incidence_sum` | `Geometry/KuhnNodeIncidence.lean:60` | PASS；真实有限二重求和按唯一关联精确给每排列d+1项，无遗漏或额外网格数。 |
| 9 | `integral_cartesianKuhnHat_cell` | `Spatial/CartesianKuhnMass.lean:16` | PASS；实际帽函数逐单元重心坐标公式和可积性给匹配顶点的|K|/(d+1)之和。 |
| 10 | `cartesianKuhnHat_mass_domain` | `Spatial/CartesianKuhnMass.lean:46` | PASS；原域实际积分分割、关联计数及平移体积给∫Ωφ_a=∏δⱼ。 |
| 11 | `cartesianKuhnHat_mass` | `Spatial/CartesianKuhnMass.lean:72` | PASS；真实域外逐点零把同一质量身份还原为全空间积分。 |
| 12 | `cartesianKuhnHat_affine_integrable` | `Spatial/CartesianKuhnAffineMoment.lean:14` | PASS；任意实际仿射p与真实连续紧支帽函数之积在全空间真正可积。 |
| 13 | `cartesianKuhnHat_affine_integral` | `Spatial/CartesianKuhnAffineMoment.lean:22` | PASS；真实线性部分与可积向量一阶矩给∫pφ_a=(∏δⱼ)p(x_a)。 |
| 14 | `cartesianKuhnHat_affine_integral_domain` | `Spatial/CartesianKuhnAffineMoment.lean:46` | PASS；原域补集上pφ_a逐点零，得到原物理域相同积分。 |
| 15 | `cartesianKuhnHat_affine_moment` | `Spatial/CartesianKuhnAffineMoment.lean:56` | PASS；正步长保证∏δⱼ>0，精确归一化得到原仿射矩再现。 |

## 实际帽函数、单元及积分分割

已直接读取原 `cartesianKuhnHat`：它是实际有限Kuhn分割上以格点x_a为唯一值1节点、其余节点值0的数据所构造的全局节点函数；实际共有面匹配保证该函数在每个闭单元等于相应重心坐标和。它不是由期望矩条件定义的替代函数。已验收的内部节点条件给全局连续、紧支以及原开矩形域补集上逐点为零，并有真实Lp及Dirichlet成员接口。

第9项实际对任意整数节点标签a成立，不额外要求它内部：在每个真实闭单元上，帽函数等于所有匹配顶点的重心坐标之和。每个重心坐标是实际仿射函数，在紧单元上连续可积；有限和的积分交换逐项给出可积证明。原重心坐标积分依赖已读取：真实超水平集由以顶点为中心的缩放给出，Lebesgue体积按(1−t)^d变化，layercake积分得|K|/(d+1)。这里没有假定局部帽质量或把单元体积定义为指定质量。

全域积分分割使用原实际 `SimplicialPartition`。其a.e.唯一归属来自真实覆盖、内部不交和有限零测边界；闭单元只包含于原域闭包的事实，由开凸域的单元内部包含及边界零测性转成限制测度身份。因此∫Ωf恰为全部真实闭单元上的积分之和，不遗漏边界单元，也不重复计算公共面。实际帽函数在全空间可积，故其原域可积性内部供应。

## 真实盒体积、平移与排列单元总体积

`openCoordinateBox_volume_real`先用实际Euclidean空间到坐标函数空间的ofLp保测度性质，再用真实有限乘积开区间测度，得到∏(bⱼ−aⱼ)。它保留任意平移，允许某边长为零；有限端点保证真实体积有限，toReal没有掩盖无限值。

对固定排列π，格点z单元与原点单元的顶点逐点相差向量(zⱼδⱼ)ⱼ，原始平移o仍保留。真实仿射凸包／顶点重标号身份得到整个单元的平移等式，再由加法平移保持实际Lebesgue测度推出体积相同。没有把不同排列的体积相等作为未证前提。

所有排列单元总体积单独由Nⱼ=1的实际Kuhn有限分割证明：积分常函数1，有限格点函数空间此时恰有一个元素，其整数原点严格为0；剩余有限和正是全部排列的单元体积。再用上述真实盒体积公式得到

\[
\sum_{\pi\in\operatorname{Perm}(d)}|K_{0,\pi}|=\prod_j\delta_j.
\]

证明不需要逐个断言|K_{0,π}|=(∏δⱼ)/d!，因此没有未经证明地用对称性除以排列数。体积积分在原有限测度盒上进行，常函数1实际可积。

## 真实节点关联、唯一计数与边界首末层

固定内部整数节点a、排列π及顶点位置k，显式取

\[
z_j=a_j-\mathbf1_{\{\pi^{-1}(j)<k\}}.
\]

原实际顶点坐标公式立即给该单元第k顶点等于x_a。内部条件oⱼ<x_{a,j}<oⱼ+Nⱼδⱼ结合δⱼ>0及整数性精确给1≤aⱼ≤Nⱼ−1。因此每个zⱼ为aⱼ或aⱼ−1，满足0≤zⱼ<Nⱼ；旧 `cartesianKuhn_incident_finite_index` 的完整证明已直接核对，确实据此构造合法Fin(Nⱼ)格点而不额外假设存在关联。

当aⱼ=1时允许zⱼ=0，当aⱼ=Nⱼ−1时允许zⱼ=Nⱼ−1。这正覆盖靠边界第一层和最后一层内部节点，无更强的远离边界条件、星补全条件或剩余几何假设。反向唯一性在固定π、k下直接消去实际顶点公式中的同一前缀指示及非零δⱼ，得到整数原点相等，再恢复各Fin坐标相等。

有限二重求和先按格点／排列重排，再对每个k使用这个∃!关联，将格点求和化为恰一项m(π)，最后在d+1个顶点位置上求和。m可为任意实函数，不依赖非负性或预设质量。实际 `Affine.Simplex` 的仿射独立性保证单元顶点互异；原局部公式同时保留顶点索引，所以没有将不同局部顶点或不同排列标签无依据合并。网格总单元数不进入最终计数因子。

由逐单元帽质量公式、原域真实积分分割及平移体积，得到

\[
\int_\Omega\phi_a
=\sum_\pi(d+1)\frac{|K_{0,\pi}|}{d+1}
=\sum_\pi|K_{0,\pi}|
=\prod_j\delta_j.
\]

d+1严格正，其消去合法。d=0时空格点函数、空排列、唯一顶点及空乘积1都被原类型保留，零维Lebesgue体积是单位点质量，恒等式一致。若某Nⱼ不足以容纳内部整数节点，则内部前提不可满足；原Nⱼ≥2的全部内部节点均包含在结论范围。

## 真正可积性与全部仿射再现

输入p是任意实际仿射映射 `SpatialCoordinates d →ᵃ[ℝ] ℝ`，没有零边界、特殊系数或已知再现假设。有限维性保证p连续；与实际连续紧支帽函数相乘后得到全空间真实可积性，即使p本身在全空间无界也无妨。

取原p的线性部分对应的真实连续线性映射L，并令v=x_a。实际仿射身份L(x−v)=p(x)−p(v)逐点给

\[
p(x)\phi_a(x)=\phi_a(x)p(v)+L\bigl(\phi_a(x)(x-v)\bigr).
\]

两项积分的合法性分别来自真实帽函数可积性和T088已经证明的完整向量一阶矩可积性。新证明显式将后者传给 `L.integrable_comp` 和连续线性映射穿过Bochner积分的定理；没有仅利用总化积分在不可积时取零。

已核对所复用的一阶矩对象和证明：原有限域内部帽函数在节点反射下真实不变，包括首末内部层；全空间向量字段φ_a(x)(x−x_a)连续紧支并在反射下变号，实际Lebesgue反射换元给积分为零。新证明用该实际零向量矩及刚证明的质量，得到∫pφ_a=(∏δⱼ)p(x_a)。L的有限维连续化只用于合法积分交换，其算子范数没有进入结果。

原域补集上帽函数逐点零，所以全空间积分等于原Ω积分。最后正步长逐项给∏δⱼ>0，乘其逆得到精确的原归一化公式

\[
\left(\prod_j\delta_j\right)^{-1}\int_\Omega p(x)\phi_a(x)\,dx=p(x_a).
\]

原文ω_a=∏hⱼ，J_h按该质量归一化，故这一实际公式对应原 `(J_hp)_a=p(x_a)`。任意位置o、逐轴正步长、有限网格大小、全部内部整数节点和全部仿射p均保留；不要求长宽比或时间参数，也不把真实矩再现扩大成尚未构造的载荷右逆或稳定性结论。结合T088完成原eq:fdmoments这组辅助身份，但完整FD/P012、B.2/P026仍不提升，原文13/26不变。

## 固定依赖、构建与公理

四模块Carleman导入闭包共159模块，155旧模块与base完全不变，新增恰为本批四模块。关键已验收版本亦已比较：C104 CartesianKuhnFirstMoment的144模块闭包相对base不变；C103 CartesianKuhnNodal的139模块闭包相对 `7b2627620e04ad9b44e6bee31fab8a241d4f4d1a` 不变；C065 SimplicialIntegrals的85模块闭包相对 `99694c20834ac8d3b712f5e2d071a4e4ccfc308b` 不变；C069 SimplexBarycentricDistribution的35模块闭包相对 `24509632c6ae2b1a3bb9e30eca790c82decec4e3` 不变。上述关键数学依赖也已直接读取。

原稿、已读治理协议、工具链pin及CI工作流未由本批改变。原稿SHA256为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean为4.35.0，本机mathlib实际HEAD为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且工作树干净。root显式导入四模块，CheckAxioms包含15项完整类型及公理输出。

15项完整展开类型已逐项核对，均只依赖 `propext`、`Classical.choice`、`Quot.sound`。固定本机1906条显式公理记录（1902非空、4无公理）未发现其他公理或sorryAx；检查器通过privateToUserName遍历所有Carleman声明并递归collectAxioms。实际定向日志为3336 jobs；`/tmp/carleman-kuhn-moments-full.log` 包含 `Build completed successfully (3758 jobs).` 和 `Axiom audit passed for all 5988 Carleman declarations.`。固定 `/tmp/carleman-kuhn-moments-local-axioms.txt` 为 **1,743,847 bytes**，SHA256 **`40c2b1ae4958b86eb9ff237963b8588cadd3f1c50a63d85bc1f2a0982de163b6`**。

已独立通过GitHub connector读取 [main CI 39184122639 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39184122639/attempts/1)：main/push、head SHA精确匹配固定版本，run为completed/success。lean（117842828012）、state-check（117842828122）、dashboard / snapshot（117843644161）三项jobs全部completed/success；工具链准备、完整构建、checked source记录、原始证据上传及同次快照步骤均success。同run的lean-ci-result（12157457284）和lean-declaration-evidence（12157367888）实际artifact元数据均绑定固定SHA。

已实际读取 `/tmp/carleman-kuhn-moments-main-ci/result.json`：status PASS，`checked_sha=source_head_sha=f2e5416279274e334edf8df2d2e43ce3a4d23c39`，targets为Carleman，`finished_at=2026-10-19T01:12:54.238937+00:00`，ci_url与上述run/attempt一致。实际Lean 4.35.0提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib为上述pin。

原始远端 `/tmp/carleman-kuhn-moments-main-axioms/axioms.txt` 与固定本机副本已独立逐字节比较，完全相同：**1,743,847 bytes**，SHA256 **`40c2b1ae4958b86eb9ff237963b8588cadd3f1c50a63d85bc1f2a0982de163b6`**。另逐名核对远端15/15完整展开类型及公理，1906条显式记录（1902非空、4无公理）均无非基础公理、无sorryAx；实际末行为 **`Axiom audit passed for all 5988 Carleman declarations.`**。未混用其他SHA或后续工作区产物。

## 验收决定

**C105：PASS，可升级为REVIEWED，scope保持AUXILIARY。** 固定15项未发现真实节点关联、首末内部层、单元／盒体积、积分重计、可积性、向量矩或归一化方面需要修复的缺陷；同SHA正式三项CI及原始远端公理证据已独立核实。载荷右逆／稳定性、完整FD/P012、B.2/P026等后续义务如上，本批不提升其他原文命题，原文仍 **13/26**。

本次仅写本报告，没有修改数学实现、台账、原稿或root导入，没有commit/push。
