# T054 / C070 独立本机验收

- `checked_sha`: `cbea02af04b947ec6f1b1c6e3cfb0da5bd65e5a7`
- `base_commit`: `24509632c6ae2b1a3bb9e30eca790c82decec4e3`
- `reviewed_at`: `2026-10-18T20:30:24+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：真实单纯形重心坐标二阶矩、真实顶点置换的积分不变性、完整一致P1质量积分公式及节点系数加权的真实局部积分强制性。**不包含节点权与实际四类权的对应、完整V_h的节点表示／测试或全域加权投影稳定性，原文完成仍为12/26。**

本次独立读取固定提交四个新模块的全部证明、19项完整展开类型、实际依赖及T054规格，对照原 `paper/main.tex` Section 6 Proposition 6.1 Step 1 的一致质量L²投影及Γ_d阈值。原文该处引用DST；本批建立所需局部积分基础，不把这些辅助声明视作原引用定理或完整P1命题的证明。未评后续工作区增量，执行者说明与CI未代替数学审查。

## 全部19项声明

完整名称均以前缀 `Carleman.` 开始；位置属于固定版本的 `Carleman/Spatial/`。顺序与固定C070、T054及交付JSON完全一致。

| # | 声明（省略 Carleman.） | 固定位置 | 独立数学核对 |
|---|---|---|---|
| 1 | `integral_sq_eq_tail` | `BoundedSecondMoment.lean:10` | PASS；有限测度上a.e.可测且0≤f≤1，以真实layer-cake给∫f²=2∫_(0,1]t μ{f≥t}dt，实值／扩展非负积分转换合法。 |
| 2 | `integral_unit_tail_power` | `SimplexSecondMoments.lean:10` | PASS；实际区间积分给∫₀¹t(1−t)^d=1/((d+1)(d+2))，含d=0。 |
| 3 | `integral_simplexBarycentric_sq` | `SimplexSecondMoments.lean:30` | PASS；代入真实重心坐标分布，得到2vol(K)/((d+1)(d+2))；仅在实参数轴排除t=1。 |
| 4 | `simplexPermutationLinear` | `SimplexPermutationIntegral.lean:13` | PASS；真实单纯形坐标基之间的连续线性同构，目标为T.reindex e.symm。 |
| 5 | `simplexPermutationShift` | `SimplexPermutationIntegral.lean:16` | PASS；实际平移项把源基点送到重索引目标基点。 |
| 6 | `simplexPermutation_vertex` | `SimplexPermutationIntegral.lean:19` | PASS；实际仿射映射准确将顶点i送到顶点e(i)，重索引方向正确。 |
| 7 | `simplexPermutation_cell` | `SimplexPermutationIntegral.lean:28` | PASS；仿射像与实际顶点范围／凸包一致，闭单元像恰为自身。 |
| 8 | `simplexPermutation_barycentric` | `SimplexPermutationIntegral.lean:37` | PASS；实际仿射多项式的节点再现给全空间身份λ_(e i)(F x)=λ_i(x)。 |
| 9 | `simplexPermutation_jacobian` | `SimplexPermutationIntegral.lean:53` | PASS；对常数1作真实换元，利用正有限单元体积消去体积因子，推出绝对Jacobian为1。 |
| 10 | `integral_comp_simplexPermutation` | `SimplexPermutationIntegral.lean:65` | PASS；真实换元及J=1给同一闭单元上的积分不变性，无任意保体积假设。 |
| 11 | `integral_simplexBarycentric_mul_permutation` | `SimplexPermutationIntegral.lean:71` | PASS；积分换元与两重心坐标变换身份给二阶矩的真实置换不变性。 |
| 12 | `integral_simplexBarycentric_mul_offdiag` | `SimplexMassIntegral.lean:12` | PASS；固定i后交换其余顶点，结合一阶矩／对角二阶矩求得非对角矩；i≠j合法排除d=0。 |
| 13 | `integral_simplexBarycentric_mul` | `SimplexMassIntegral.lean:54` | PASS；对角／非对角统一为(1+δᵢⱼ)vol(K)/((d+1)(d+2))。 |
| 14 | `p1CoefficientForm_sum` | `SimplexMassIntegral.lean:64` | PASS；双和中的对角项与全系数和乘积准确合并为原p1CoefficientForm。 |
| 15 | `integral_simplexNodalInterpolant_mul` | `SimplexMassIntegral.lean:71` | PASS；实际可积多项式双和与积分交换，得到vol(K)/((d+1)(d+2))乘完整双线性系数型。 |
| 16 | `simplex_mass_factor_pos` | `SimplexMassIntegral.lean:103` | PASS；真实非空内部／紧性给体积严格正且有限，分母严格正。 |
| 17 | `integral_simplexNodalInterpolant_sq_bounds` | `SimplexMassIntegral.lean:110` | PASS；精确平方公式与有限Cauchy–Schwarz给上下界之比d+2，局部体积因子未丢失。 |
| 18 | `weighted_simplex_mass_coercive` | `SimplexMassIntegral.lean:130` | PASS；已有真实系数强制性乘正体积因子，结论为∫K p_c p_(ω²c)的下界，保留任意正尺度a和任意有符号c。 |
| 19 | `weighted_simplex_mass_pos` | `SimplexMassIntegral.lean:141` | PASS；γ<Γ_d、a>0、a≤ωᵢ≤γa及c≠0给上述实际积分严格正，没有假设目标积分正。 |

## 真实layer-cake、二阶矩与零维端点

integral_sq_eq_tail 的输入是一般有限测度μ、真实实值函数f的AEMeasurable及0≤f≤1 a.e.，不是已知二阶矩。固定mathlib的 `lintegral_comp_eq_lintegral_meas_le_mul` 对g(t)=t给∫⁻ofReal(∫₀^f t dt)=∫⁻_(0,∞)μ{f≥t}ofReal(t)。g在有限区间可积并在正轴非负，∫₀^f t dt=f²/2，因子2正确。

尾集测度随t反单调，故其ENNReal值可测，转实值后与t乘积可测。IsFiniteMeasure保证每个尾集测度不为∞，所以ofReal(toReal μ{f≥t})准确还原，而非将∞错误变为0。左侧f²/2为非负a.e.强可测函数，右侧在正轴非负，分别合法用积分与lintegral的toReal身份。这里的有限测度及a.e.界也直接保证f²可积；右侧在t≤1时受t·μ(univ)控制、t>1时为零。因此这些等式确为有限的实际积分身份，没有依赖不可积Bochner积分默认值使结论空洞化。

f≤1 a.e.使{f>1}零测；t>1时{f≥t}包含于该零测集，尾项恰为零。由此把正半轴积分限制到(0,1]，没有丢失可能有原空间正测度的水平集。应用于真实λ_i时，连续性给可测，单元内非负与总和1给0≤λ_i≤1，实际紧单元保证有限测度。

已直接核对T053分布依赖：顶点i为中心、比例1−t的真实仿射同位变换，将K准确映为K∩{λ_i≥t}；t<1保证反变换存在。真实Haar体积变换给尾体积(1−t)^d vol(K)。新证明只在Lebesgue实参数轴上排除单点t=1，然后代入分布。d=0时该尾幂为1，积分∫₀¹t=1/2，最终二阶矩公式为vol(K)，与零维唯一重心坐标λ₀=1一致；没有误称零维单元自身零测，也不需要全局d>0条件。

数值积分由t(1−t)^d=(1−t)^d−(1−t)^(d+1)、两个连续函数的区间可积性及真实幂积分算得。分母d+1、d+2均严格正，未遗漏端点或使用所求积分作为前提。

## 实际置换、Jacobian与交叉矩

simplexPermutationLinear使用实际全维单纯形的仿射坐标基，将T对应到T.reindex e.symm；平移修正基点。已有affineSimplex_coordinate_eq给顶点i实际映到e(i)，不存在将e与e⁻¹混用的问题。单元像由真实仿射凸包像及顶点范围重排推出。对任意x的重心坐标变换，则把λ_(e i)与真实仿射变换复合，在全部原顶点上验证其值，再用完整仿射节点再现得到全空间相等；不是只在顶点或a.e.声称该身份。

affineJacobian的实际定义为abs(det A)，已有真实Lebesgue测度推前及积分公式含J⁻¹。对常数1，因F(K)=K而得到vol(K)=J⁻¹vol(K)。T是Euclidean d空间中的真实非退化d单纯形，其仿射包为全空间；实际凸集内部定理给非空内部，体积在非空开集上正，紧性给有限。ENNReal.toReal_pos因而合法提供vol(K)>0，消去后得到J⁻¹=1、J=1。这里证明的是绝对Jacobian，未假设所有置换保持定向，也未假设一般仿射映射保体积。上述论证同样包含d=0。

integral_comp_simplexPermutation继承真实可测同构的积分换元，对任意实函数成立；实际用于连续重心坐标乘积时，其在紧单元上的可积性另有明确证明。λ_(e i)(F x)=λ_i(x)给二阶积分置换不变。固定i及j≠i后，对任何k≠i交换j、k，该置换固定i，因此所有非对角I_k=∫λ_iλ_k相同。积分真实恒等式Σ_kλ_iλ_k=λ_i得到ΣI_k=vol(K)/(d+1)。共有d个非对角项，与已证I_i=2vol(K)/((d+1)(d+2))合并，准确解得每个非对角项vol(K)/((d+1)(d+2))。i≠j本身蕴含d>0，代码对d=0显式矛盾消去后才除去该因子；没有新增维数限制。

## 一致质量积分和加权局部强制性

simplexNodalInterpolant是真实仿射多项式p_c=Σc_iλ_i，具有原节点值且再现全部仿射函数。本批实际展开p_c p_e的双和；各项为紧单元上的连续函数，故逐项可积并可与有限求和交换。完整公式为

\[
\int_K p_c p_e=\frac{|K|}{(d+1)(d+2)}\left(\sum_i c_i e_i+\left(\sum_i c_i\right)\left(\sum_i e_i\right)\right).
\]

这是实际一致质量积分的恒等式，体积和维数归一化均未吸收到任意常数。对c=e，右侧为体积因子乘[Σc_i²+(Σc_i)²]。平方非负给下界，有限Cauchy–Schwarz给(Σc_i)²≤(d+1)Σc_i²，故上界系数为d+2；不把d+1或网格单元数误写成这一比值。所有c、e均任意有符号实系数。

已直接阅读T052的p1CoefficientForm和强制性证明：μ(d,γ)=1−(d+1)(γ−1)²/(4γ)，在1≤γ<Γ_d下为正；通过有限Cauchy–Schwarz、权偏差界及平方非负估计控制有符号交叉项。一般a>0的归一化ω/a在还原时同时产生a²，两侧准确抵消，结论保留Σ(ω_i c_i)²。新weighted_simplex_mass_coercive仅把该已证系数不等式乘以严格正的真实体积因子，并用上述实际积分身份改写；其一般γ≥1版本不声称μ必正。weighted_simplex_mass_pos另要求γ<Γ_d及c≠0，正ω使加权平方和严格正，最终实际积分严格正。

这里第二个多项式是节点值为ω_i²c_i的p_(ω²c)，并非一般空间函数ω(x)²p_c(x)。代码没有这样的错误点态改写，也没有在Lp等价类上擅取节点值。局部ω仍是公开给定的节点权数组；a≤ω_i≤γa是实际前提。参数γ是该数组的有效相对变化界，不能直接取原网格尺度分级γ而忽略四类实际权的指数变化。T051得到的有效分级(γ_mesh+Γ_d)/2与实际节点权的构造／对应，完整V_h的全局节点表示、合法测试以及全域投影估计，均未在本批中冒充已完成。

本批积分身份对任意真实非退化单纯形和全部系数成立，不施加额外形状／尺度限制。所给几何依赖只有显式体积因子，代数系数依赖d及有效γ；没有时间参数T、网格单元数或最小单元尺度混入统一常数。但这并不等于已取得原全网格L²加权投影稳定性或完整P1实现。

## 固定依赖、构建与公理

本批导入闭包含100个Carleman模块，96个旧模块与base逐字节一致，新增恰为本次四模块；Carleman.lean显式导入全部四模块。另对实际使用的C063 SimplexReferenceMap闭包45模块、C068 P1CoefficientCoercivity闭包95模块、C069 SimplexBarycentricDistribution闭包35模块，分别与各自已验收版本 `ce719d2683c7509827e457ea2e15e0ce5451b487`、`df8b853f9203194295be90f39ef5f797af31b9b3`、`24509632c6ae2b1a3bb9e30eca790c82decec4e3` 比较，全部逐字节不变。相关实际定义及证明已直接复核。

原稿、治理协议、工具链pin和CI工作流与base一致。原稿SHA256为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean pin为4.35.0；本机实际mathlib HEAD为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且其工作树干净。所查layer-cake及非负Bochner／lintegral转换实际源码来自该pin。

19项完整类型已逐一核对，无隐藏额外积分身份或目标误差前提。固定CheckAxioms逐项执行 `#check @...` 与 `#print axioms ...`，再以privateToUserName识别全部Carleman声明并递归collectAxioms，仅许可 `propext`、`Classical.choice`、`Quot.sound`。19项公理集合均恰为这三项正常基础公理；本地全部1294条显式公理输出也未发现其他公理，无sorryAx。交付JSON与固定C070/T054的19项顺序完全相同。

`/tmp/carleman-second-moments-full.log` 实际包含 `Build completed successfully (3613 jobs).` 和 `Axiom audit passed for all 4814 Carleman declarations.`。固定 `/tmp/carleman-second-moments-local-axioms.txt` 为 **1,350,771 bytes**，SHA256 **`2c8d7f5dd7d538af1908c57add7187a4ae51e0ad14ceca1144deee99b944c3c2`**。

已独立通过GitHub connector核实 [main CI 39163247482 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39163247482/attempts/1)：main/push、head SHA为固定 `cbea02af04b947ec6f1b1c6e3cfb0da5bd65e5a7`，completed/success。lean（117780796494）、state-check（117780796660）、dashboard / snapshot（117781523537）三项jobs均completed/success；工具链准备、root构建、checked source记录、两份证据上传及同次快照生成均success。同run的lean-ci-result artifact（12149243131）及lean-declaration-evidence artifact（12149885948）均绑定该固定SHA。

已实际读取 `/tmp/carleman-second-moments-main-ci/result.json`：status PASS，`checked_sha=source_head_sha=cbea02af04b947ec6f1b1c6e3cfb0da5bd65e5a7`，targets为Carleman，`finished_at=2026-10-18T20:27:57.688660+00:00`，ci_url与上述run/attempt完全一致。实际Lean 4.35.0提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib为上述pin。

原始远端 `/tmp/carleman-second-moments-main-axioms/axioms.txt` 与固定本机副本已独立逐字节比较，完全相同：**1,350,771 bytes**，SHA256 **`2c8d7f5dd7d538af1908c57add7187a4ae51e0ad14ceca1144deee99b944c3c2`**。另逐名复核远端19/19完整展开类型及每项正常基础公理集合，末行实际为 **`Axiom audit passed for all 4814 Carleman declarations.`**，无sorryAx或未批准数学公理。没有混用其他提交、运行或后续工作区产物。

## 验收决定

**C070：PASS，可升级为REVIEWED，scope保持AUXILIARY。** 固定版本19项未发现需要修复的积分、端点、维数、Jacobian、系数型身份、权参数或量词缺陷；完整类型、递归公理和同SHA正式main CI均已独立核实。

本批补齐真实局部质量积分及其节点系数加权强制性；节点权与原四类权对应、完整V_h节点表示／测试、全域投影稳定性以及原P1实现的其他义务仍待，不提升P011/P014/P015或其他完整原文结果，原文仍12/26。

本次仅写本报告，没有修改证明、台账、覆盖表、原稿或root导入，没有commit/push。
