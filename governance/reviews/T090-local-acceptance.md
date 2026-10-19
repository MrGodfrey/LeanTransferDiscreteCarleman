# T090 / C106 独立本机验收

- `checked_sha`: `340cab6232ac4c81515d19b523fec6e7a031df75`
- `base_commit`: `f2e5416279274e334edf8df2d2e43ce3a4d23c39`
- `reviewed_at`: `2026-10-19T01:23:48+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**（固定本机与同次远端原始产物逐字节一致）
- `scope`: **AUXILIARY**
- 范围：原完整内部节点向量的实际分片仿射载荷及真实 L² 类，全部原 L² 上的归一化帽函数矩，精确右逆 `J_h L_h=Id` 与满射。网格一致加权稳定性、刚度、完整 FD/B.2 仍待，原文保持 **13/26**。

直接以 `git show` 读取固定五模块全部证明、28项完整展开类型及关键依赖，对照原 `paper/main.tex` Section 6 的内部索引、质量和 J_h（TeX 1634–1658），以及 Appendix B Step 1 原载荷公式与右逆（TeX 2756–2774）。执行者规格及 CI 不替代数学核对；后续工作树增量不在范围内。

## 全部28项声明

名称省略共同前缀 `Carleman.`；固定位置以 `Carleman/` 为根，顺序与交付 JSON、固定 C106/T090 台账一致。

| # | 声明 | 固定位置 | 独立核对 |
|---|---|---|---|
| 1 | `simplexLoadPolynomial` | `Spatial/SimplexLoadPolynomial.lean:12` | PASS；真实局部多项式是 Σc_i((d+2)λ_i−1)，其中 λ_i 为实际 AffineBasis 重心坐标。 |
| 2 | `simplexLoadPolynomial_continuous` | `Spatial/SimplexLoadPolynomial.lean:15` | PASS；有限和中每一项为真实连续仿射函数的实数倍，局部多项式全空间连续。 |
| 3 | `integral_simplex_dual_barycentric` | `Spatial/SimplexLoadPolynomial.lean:22` | PASS；实际一、二阶重心积分与合法积分线性运算给 δ_ij|K|/(d+1)，全部维数分母正确。 |
| 4 | `integral_simplexLoadPolynomial_barycentric` | `Spatial/SimplexLoadPolynomial.lean:41` | PASS；逐项证明可积后交换真实有限求和与积分，得到 c_j|K|/(d+1)。 |
| 5 | `cartesianKuhnLoadCoefficients` | `Spatial/CartesianKuhnLoad.lean:14` | PASS；真实单元顶点仅在原开矩形内时读取数据，其余系数严格为零。 |
| 6 | `cartesianKuhnLoad` | `Spatial/CartesianKuhnLoad.lean:20` | PASS；原闭单元指示函数乘实际局部载荷多项式的有限和，未假装跨面连续。 |
| 7 | `cartesianKuhnLoad_on_cell` | `Spatial/CartesianKuhnLoad.lean:25` | PASS；真实单元限制测度下 a.e. 等于本单元原多项式；公共面重复贡献被零测分割合法消去。 |
| 8 | `cartesianKuhnLoad_memLp` | `Spatial/CartesianKuhnLoad.lean:43` | PASS；各紧闭单元上连续多项式有界且有限测度，真实全空间 L² 成员内部证明。 |
| 9 | `cartesianKuhnLoad_integrable` | `Spatial/CartesianKuhnLoad.lean:59` | PASS；每个连续多项式在紧单元可积，指示函数与有限求和给真实全空间 L¹ 可积性。 |
| 10 | `cartesianKuhnLoad_mul_hat_integrable` | `Spatial/CartesianKuhnLoad.lean:67` | PASS；内部帽函数连续，各局部乘积在紧单元可积，真实全空间载荷乘帽可积。 |
| 11 | `integral_cartesianKuhnLoad_mul_hat_cell` | `Spatial/CartesianKuhnLoadMoment.lean:13` | PASS；关联单元用 λ_j 与真实活动系数，非关联单元用帽函数恒零，得到精确局部矩身份。 |
| 12 | `cartesianKuhnLoad_hat_integral_domain` | `Spatial/CartesianKuhnLoadMoment.lean:49` | PASS；原域真实有限分割及实际帽质量给 ∫Ω Lf φ_a=f(x_a)∏δ_j。 |
| 13 | `cartesianKuhnLoad_moment_right_inverse` | `Spatial/CartesianKuhnLoadMoment.lean:67` | PASS；正步长给真实质量乘积非零，准确归一化为节点值 f(x_a)。 |
| 14 | `CartesianInteriorIndex` | `Geometry/CartesianInteriorNodes.lean:13` | PASS；原全部内部节点索引为 ∀j,Fin(N_j−1)，没有额外数据子空间。 |
| 15 | `cartesianInteriorLatticeIndex` | `Geometry/CartesianInteriorNodes.lean:15` | PASS；逐坐标 val+1 给原整数指标1,…,N_j−1。 |
| 16 | `cartesianInteriorPoint` | `Geometry/CartesianInteriorNodes.lean:18` | PASS；由该整数指标构造真实物理节点 o+(val+1)δ。 |
| 17 | `cartesianInteriorPoint_mem` | `Geometry/CartesianInteriorNodes.lean:21` | PASS；Fin 界与正步长内部给实际节点严格位于原开矩形。 |
| 18 | `cartesianInteriorPoint_injective` | `Geometry/CartesianInteriorNodes.lean:36` | PASS；真实物理点相等，约去正步长与共同平移后恢复全部 Fin 指标。 |
| 19 | `cartesianInteriorData` | `Geometry/CartesianInteriorNodes.lean:48` | PASS；任意有限向量通过物理节点 Kronecker 有限和作为点数据扩展，无连续或可测前提。 |
| 20 | `cartesianInteriorData_at_node` | `Geometry/CartesianInteriorNodes.lean:53` | PASS；真实节点映射单射，Kronecker 和在节点精确取回原任意向量值。 |
| 21 | `cartesianKuhnLoadLift` | `Spatial/CartesianKuhnLoadLift.lean:14` | PASS；将任意完整内部向量的数据扩展输入实际载荷构造。 |
| 22 | `cartesianKuhnLoadLift_memLp` | `Spatial/CartesianKuhnLoadLift.lean:18` | PASS；由真实全空间 L² 成员限制到原域，未预设载荷有界性。 |
| 23 | `cartesianKuhnLoadLiftLp` | `Spatial/CartesianKuhnLoadLift.lean:24` | PASS；由 MemLp.toLp 构造原域真实 L² 等价类。 |
| 24 | `cartesianKuhnLoadLiftLp_ae` | `Spatial/CartesianKuhnLoadLift.lean:29` | PASS；该 L² 类在原限制体积下几乎处处等于实际载荷函数。 |
| 25 | `cartesianKuhnMoment` | `Spatial/CartesianKuhnLoadLift.lean:35` | PASS；对任意原 L² 状态定义真实帽函数矩，以原质量 ∏δ_j 归一化。 |
| 26 | `cartesianKuhnMoment_integrable` | `Spatial/CartesianKuhnLoadLift.lean:42` | PASS；任意 L² 状态乘真实 L² 帽函数由 Hölder 可积，未依赖总化积分的不可积分支。 |
| 27 | `cartesianKuhnLoadLiftLp_right_inverse` | `Spatial/CartesianKuhnLoadLift.lean:51` | PASS；整个完整有限向量等式 J_h(L_h f)=f，使用实际 L² 代表和节点恢复。 |
| 28 | `cartesianKuhnMoment_surjective` | `Spatial/CartesianKuhnLoadLift.lean:66` | PASS；以同一实际载荷 L² 类为见证，真正矩映射在全部有限向量上满射。 |

## 原局部公式与真实双对偶积分

`simplexLoadPolynomial T c` 的实际值是 Σ_i c_i((d+2)λ_i(x)−1)，λ_i 来自真实非退化单纯形 T 的完整仿射基，不是只满足预设矩条件的替代函数。系数 c 为任意实向量。原积分依赖给出真实 Lebesgue 体积 V=volume.real K，以及 ∫K λ_j=V/(d+1)、∫K λ_iλ_j=(1+δ_ij)V/((d+1)(d+2))。

新证明先分别供应 λ_iλ_j、λ_j 在真实紧单元上的连续可积性，再展开 `(d+2)λ_iλ_j−λ_j`，合法交换乘常数与减法积分。结果是 `(d+2)(1+δ_ij)V/((d+1)(d+2))−V/(d+1)=δ_ij V/(d+1)`；d+1、d+2 均严格正，未遗漏因子、体积或对角系数2。随后对任意 c 逐项证明乘积可积，交换有限和与积分得到 c_j V/(d+1)。没有用不可积时总化积分为零来完成矩身份。

已读取所用 SimplexMassIntegral 的真实一、二阶矩组合、非对角置换与重心和恒等式调用；其导入闭包与已验收版本相同。d=0时唯一重心坐标为1，载荷局部因子2·1−1=1，零维真实体积为单位点质量，公式正常成立；无非对角项，未误用正维数端点零测。

## 只读取内部数据与共享面 a.e. 公式

`cartesianKuhnLoadCoefficients` 在每个真实有限单元顶点 v_k 上检查 `v_k∈Ω`，成立则读取 f(v_k)，否则取零。原实际分区保证顶点属于闭矩形，故这精确对应原求和范围 `x_i∈K∩Ω`，边界节点不会混入载荷。输入 f 在这一层可以是任意点函数；它只在有限个实际顶点被读取，完全不要求 f 连续、可测、属于 Sobolev 空间或具有光滑延拓。

全空间函数采用所有闭单元指示函数乘各自实际局部多项式的有限和。共享闭面上可能同时存在多个贡献，代码没有声称它处处等于任选单元的多项式，更没有声称载荷连续。`cartesianKuhnLoad_on_cell` 的结论精确为每个真实单元限制体积下的 a.e. 身份。

该身份使用真实 a.e. 唯一分割，并以 `cell_measure_le_domain` 将原域上的 a.e. 结论合法限制到整个闭单元。此次直接读取该依赖：非退化单纯形的边界为实际零测集；其内部由 `inside` 及开凸域的 `interior(closure Ω)=Ω` 包含于 Ω，故闭单元限制测度不超过域限制测度。原空域分支亦单独处理。在这个共同满测集上，单元 i 包含 x 时其他全部单元均不含 x，指示有限和恰只余第 i 项。物理边界与共享面没有被错误地逐点删去，使用的是合法的测度零处理。

每个局部多项式在全空间连续，在真实紧单元上有有限界且限制体积有限，因此其指示函数属于真实全空间 L²；有限求和保持 MemLp。L¹ 可积性另由连续函数在紧单元可积及指示函数定理逐项供应，没有把全空间 L² 直接当作 L¹。实际载荷乘内部帽函数的 L¹ 资格也独立证明：帽函数全空间连续，每个局部乘积在紧单元连续可积，有限指示和保持可积。

这些有限界可依赖具体网格与数据，只用于实际函数空间成员资格；本批未据此宣布网格一致或带权稳定常数。

## 局部矩到全域矩及首末内部层

对任意实际内部整数节点 a，若单元含该节点，真实帽函数在该整个单元上就是其局部 λ_k；活动条件由 a∈Ω 内部供应，因此相应载荷系数严格等于 f(x_a)。通过载荷的单元 a.e. 身份和真实双对偶积分，得到 `∫K Lf φ_a=f(x_a)V_K/(d+1)=f(x_a)∫Kφ_a`。若单元不含节点，帽函数在整个闭单元恒零，两边都为零。两分支没有假设载荷自身的跨面连续性。

全域求和调用 `integral_eq_sum_cells`，且显式传入刚证明的载荷乘帽真实可积性。此次读取该接口的实际证明：有限指示和在真实 a.e. 唯一分割上等于原函数；每个指示项由原可积性供应可积；原域与闭单元的限制测度身份使积分之和既不遗漏外边界单元，也不重复计算共享面。再对真实帽函数作同一积分分割，使用已验收的 ∫Ωφ_a=∏δ_j，得到 `∫Ω Lf φ_a=f(x_a)∏δ_j`。

所用质量定理并未额外要求节点远离边界。此次读取实际节点关联证明：对每个排列 π 和顶点位置 k，显式取格点原点 `z_j=a_j−1_(π⁻¹j<k)`；真实内部整数条件给1≤a_j≤N_j−1，因此0≤z_j<N_j，并构造合法 Fin(N_j) 指标。固定 π、k 的真实顶点映射单射给唯一性。第一层 a_j=1 允许 z_j=0，最后层 a_j=N_j−1 允许 z_j=N_j−1，均无缺失。真实有限关联和、单元平移体积与全部排列总体积最终给原质量，未预设所需质量恒等式。

每项 δ_j>0 保证 ω=∏δ_j>0；以 ω⁻¹ 归一化后精确还原 f(x_a)。右逆证明实际只使用零阶帽质量，虽导入包含一阶仿射矩的模块，但没有暗中要求 f 仿射或依赖仿射再现来推广任意数据。

## 全部原有限向量与任意 L² 状态

`CartesianInteriorIndex N` 明确是 `∀j, Fin(N_j−1)`，经逐坐标 val+1 恰表示原全部内部整数指标1,…,N_j−1。没有选取较小数据空间。每个指标的物理点是 o+(val+1)δ，Fin 上界内部推出严格位于原开矩形；正步长使节点映射单射。

对任意 `f : CartesianInteriorIndex N → ℝ`，`cartesianInteriorData` 是有限物理节点 Kronecker 和，节点单射性保证每个节点精确取回 f(a)。这一点函数只是向实际单元顶点传递有限数据的工具，可能在非节点处为零；它不是先被转成 L² 类后再取点值。因此不能因为它在正维空间 a.e. 为零而把载荷误认为零，也没有非法对任意 L² 类作节点求值。实际载荷先通过这些节点数据形成单元多项式，再由真正 MemLp.toLp 构造原域 L² 类。

`cartesianKuhnMoment` 的输入是全部 `Lp ℝ 2 (volume.restrict Ω)`，其第 a 坐标为 `ω⁻¹∫Ω u(x)φ_a(x)dx`，与原 `(J_hu)_a=ω_a⁻¹(u,φ_a)_H` 的实 L² 内积一致。`cartesianKuhnMoment_integrable` 对每个任意 u 使用 u 的真实 L² 资格和帽函数 L² 类的 a.e. 代表身份，由 L²×L² 的 Hölder 可积性证明实际乘积可积。该定义的积分不依赖代表选择，a.e. 更换 u 可由实际积分同余处理；不要求 u 连续、H¹、光滑或具有点值。

最终 `cartesianKuhnLoadLiftLp_right_inverse` 的完整类型对全部 f 给整个有限向量函数等式。证明逐坐标先把真实载荷 L² 代表按 a.e. 身份替换为实际载荷函数，应用任意点数据的已证矩右逆，再用 Kronecker 节点恢复得到 f(a)。满射性以同一实际 L² 载荷为见证。这里没有把“每个光滑数据的矩一致”当成完整向量右逆，也没有假设存在某个光滑函数取样为 f。

全部 N_j∈ℕ 允许。若 d>0 且某 N_j≤1，则完整内部指标类型为空，函数空间只有空函数，向量等式与满射性正确退化；N_j=0 时物理开域也为空，N_j=1 时可以非空但无内部节点。原 N_j≥2 的全部数据均保留。d=0时空坐标乘积的内部指标类型有唯一元素、质量空积为1、物理空间为唯一点，结果也一致，不能把它误当成空节点集。

## 量词、原文范围与依赖

所有新精确身份对任意维数、平移 o、逐轴正步长 δ、有限 N、全部内部节点及全部数据成立。无需各步长可比性，因为本批没有给统一稳定性不等式；原文可比网格是其特例。没有时间、空间正则代表、额外节点零条件或新的图范数前提。边界系数零由原载荷定义内部处理，原载荷本身不被要求属于 H¹₀。

本批完成原 Appendix B TeX2759–2771 的实际载荷公式和 `J_h L_h=Id`，并构造全部原有限向量到真实 L² 的右逆函数及真正矩映射的满射性。这里尚未把这些函数封装成带原加权物理内积的全部算子接口，亦未证明网格一致加权载荷稳定性、R_h 稳定性、刚度身份、Q_h 误差或完整数值假设。故 C106 保持 AUXILIARY，不提升 FD/P012、B.2/P026，原文保持13/26。

五新模块 Carleman 导入闭包共177模块，其中172旧模块与基线逐字不变。关键版本另行递归比对：CartesianKuhnAffineMoment 的159模块闭包与 [T089](T089-local-acceptance.md) 固定基线完全一致；CartesianKuhnHatSupport 的140模块闭包与 [T087](T087-local-acceptance.md) 固定 `7b2627620e04ad9b44e6bee31fab8a241d4f4d1a` 一致；SimplexMassIntegral 的100模块闭包与已核对其真实质量积分的 [T055](T055-local-acceptance.md) 固定 `7815f431a2674c214a51368d1383b7deeb9eed40` 一致。本次也直接读取上述实际局部质量积分、帽函数矩、节点唯一关联、有限域关联、单元限制测度与全域积分分割证明，核实其调用条件。

## 构建、公理和远端证据

固定 `/tmp/carleman-kuhn-loadlift-target.log` 为3354 jobs成功；`/tmp/carleman-kuhn-loadlift-full.log` 为3763 jobs成功，并实际包含 `Axiom audit passed for all 6026 Carleman declarations.`。固定 `/tmp/carleman-kuhn-loadlift-local-axioms.txt` 为 **1,755,952 bytes**，SHA256 **`83c26d3148b3dfde9c17fdfdfa1357c2ecb28936dfbfbb7a9a6294f982754675`**。

28/28项完整展开类型与源码相符且每项各有一条公理记录；CartesianInteriorIndex、cartesianInteriorLatticeIndex 无公理，其余只依赖 `propext`、`Classical.choice`、`Quot.sound`。全部1934条显式记录（1928条基础公理、6条无公理；1930个不同声明）无白名单外依赖；递归审计涵盖辅助生成声明，无 sorryAx。五新模块无 sorry/admit/axiom/unsafe；root 明确导入全部五模块，CheckAxioms 仅新增28项完整类型和公理输出，原递归审计不变。交付 JSON 与固定 C106/T090 台账28项名单精确一致。

原稿、已读 AGENTS／治理协议、工具链 pin 和 CI 工作流相对基线未变。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`；Lean 4.35.0，mathlib 实际 HEAD 为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且本机工作树干净。

已独立通过 GitHub API 读取 [main CI 39184701139 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39184701139/attempts/1)：main/push，head SHA 精确为本报告固定版本，run completed/success。三项 job 全部绑定同 SHA 且 completed/success：state-check `117844548821`（01:17:56Z）、lean `117844549095`（01:21:15Z）、dashboard / snapshot `117845329837`（01:21:28Z）。

实际 artifact 元数据确认 `lean-ci-result`（`12156669625`）及 `lean-declaration-evidence`（`12157143051`）均属于该 run、main 分支及同一 head SHA，未过期。独立读取 `/tmp/carleman-kuhn-loadlift-main-ci/result.json`：status=PASS，checked_sha=source_head_sha=`340cab6232ac4c81515d19b523fec6e7a031df75`，targets 为 Carleman，finished_at=`2026-10-19T01:20:18.286043+00:00`，ci_url 对应上述 run/attempt；实际 Lean 与 mathlib pin 一致。

远端原始 `/tmp/carleman-kuhn-loadlift-main-axioms/axioms.txt` 已与固定本机副本逐字节比较，完全相同：**1,755,952 bytes**，SHA256 **`83c26d3148b3dfde9c17fdfdfa1357c2ecb28936dfbfbb7a9a6294f982754675`**。远端28/28项完整类型及公理记录逐名复核通过，全部1934条显式记录重新扫描无非基础公理；末行确认全部 **6026** 声明递归审计通过。未混用后续工作树或其他 SHA 的构建证据。

## 验收决定

**C106：PASS，可按 AUXILIARY 升为 REVIEWED。** 28项语义核对未发现原载荷多项式、体积因子、真实可积性、共享面 a.e. 处理、首末内部层、完整有限向量、全部 L² 输入、归一化或右逆方面的缺陷。同 SHA 三项最终 CI 和原始产物均已独立核实；本批不提升 P012/P026 或其他原文命题，原文仍为 **13/26**。

本次仅写本报告，未改实现、台账、root 或原稿，未 commit/push。范围保持 AUXILIARY，原文保持13/26。
