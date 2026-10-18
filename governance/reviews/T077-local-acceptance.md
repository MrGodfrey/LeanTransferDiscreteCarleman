# T077 / C093 独立本机验收

- `checked_sha`: `8c4571e511be4cb48a8fd9b76c11ddba9a16e975`
- `base_commit`: `101b95e1b988d17332c7106c2be2aa945b213b3a`
- `reviewed_at`: `2026-10-18T23:28:48+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：原欧氏坐标长方体的真实坐标／测度桥接、全部弱坐标导数的双面迹、全部H¹ jet的全梯度迹界及与全局连续代表实际面值的一致性。完整B.1的多面仿射核校正与物理零迹仍待；原文保持 **12/26**。

独立从固定提交导出源码，读取五模块全部证明、42项完整展开类型及关键依赖，对照固定 `paper/main.tex` Appendix B的Lemma B.1（`lem:fd-boundary-affine`，TeX 2796–2836）。执行者规格和CI未代替数学核对；后续工作区增量不属本报告。

## 全部42项声明

名称均省略公共前缀 `Carleman.`，位置以 `Carleman/` 为根；顺序与交付JSON一致。

| # | 声明 | 固定位置 | 独立数学核对 |
|---|---|---|---|
| 1 | `coordinateSplitMeasurable` | `Geometry/EuclideanCoordinateSplit.lean:16` | PASS；真实欧氏坐标到其余坐标×所选轴的可测等价。 |
| 2 | `coordinateSplitMeasurable_apply` | `Geometry/EuclideanCoordinateSplit.lean:23` | PASS；其余坐标按succAbove排列，最后分量恰为xᵢ。 |
| 3 | `coordinateSplitMeasurable_symm_apply` | `Geometry/EuclideanCoordinateSplit.lean:26` | PASS；逆映射为真实insertNth，无坐标遗漏。 |
| 4 | `coordinateSplit` | `Geometry/EuclideanCoordinateSplit.lean:29` | PASS；同一可测等价逐点证明线性，再由有限维性取得连续线性等价。 |
| 5 | `coordinateSplit_apply` | `Geometry/EuclideanCoordinateSplit.lean:45` | PASS；连续线性版本仍为相同坐标拆分。 |
| 6 | `coordinateSplit_measurePreserving` | `Geometry/EuclideanCoordinateSplit.lean:48` | PASS；真实欧氏体积、坐标乘积拆分和交换逐步保持体积。 |
| 7 | `coordinateSplit_basis` | `Geometry/EuclideanCoordinateSplit.lean:57` | PASS；所选真实标准基严格映到(0,1)。 |
| 8 | `affineSpatialChart` | `Spatial/AffineWeakTransport.lean:18` | PASS；真实连续线性等价接平移的同胚。 |
| 9 | `affineSpatialChart_apply` | `Spatial/AffineWeakTransport.lean:21` | PASS；实际值为Ax+b。 |
| 10 | `affineSpatialChart_hasFDerivAt` | `Spatial/AffineWeakTransport.lean:24` | PASS；全点实际Fréchet导数为A，平移导数消失。 |
| 11 | `SpatialTest.pullbackAffine` | `Spatial/AffineWeakTransport.lean:31` | PASS；目标测试拉回为原域紧支C∞测试，原像支撑方向正确。 |
| 12 | `SpatialTest.pullbackAffine_derivative` | `Spatial/AffineWeakTransport.lean:40` | PASS；链式法则将方向e严格传为Ae。 |
| 13 | `affineTransportLp` | `Spatial/AffineWeakTransport.lean:53` | PASS；显式保测度图的逆图拉回给真正L²类的加法映射。 |
| 14 | `affineTransportLp_ae` | `Spatial/AffineWeakTransport.lean:58` | PASS；传输类a.e.等于原代表复合逆图。 |
| 15 | `affineTransportLp_norm` | `Spatial/AffineWeakTransport.lean:63` | PASS；保测度资格给精确L²等距，无附加常数。 |
| 16 | `integral_mul_affineTransportLp` | `Spatial/AffineWeakTransport.lean:67` | PASS；真实积分换元及a.e.代表身份准确。 |
| 17 | `IsWeakSpatialDerivative.affine_transport` | `Spatial/AffineWeakTransport.lean:82` | PASS；逐个目标SpatialTest拉回，完整原弱身份传成方向Ae的弱身份。 |
| 18 | `openCoordinateBox` | `Geometry/CoordinateBoxChart.lean:15` | PASS；原欧氏域由所有严格坐标不等式定义。 |
| 19 | `openCoordinateBox_isOpen` | `Geometry/CoordinateBoxChart.lean:18` | PASS；有限个实际坐标投影的开逆像相交。 |
| 20 | `openCoordinateBox_isBounded` | `Geometry/CoordinateBoxChart.lean:26` | PASS；包含于闭坐标盒的真实连续像，含空域及零维情况。 |
| 21 | `openCoordinateBox_finite` | `Geometry/CoordinateBoxChart.lean:33` | PASS；原限制Lebesgue测度由有界性取得有限总量。 |
| 22 | `coordinateBoxChart` | `Geometry/CoordinateBoxChart.lean:37` | PASS；拆分后只把轴向平移−a，未按长度归一化。 |
| 23 | `coordinateBoxChart_apply` | `Geometry/CoordinateBoxChart.lean:41` | PASS；轴向坐标为xᵢ−a，横向原坐标不变。 |
| 24 | `coordinateBoxChart_symm_apply` | `Geometry/CoordinateBoxChart.lean:45` | PASS；逆图插入t+a。 |
| 25 | `coordinateBoxChart_preimage` | `Geometry/CoordinateBoxChart.lean:52` | PASS；目标横向盒×(0,bᵢ−aᵢ)的原像精确等于原盒。 |
| 26 | `coordinateBoxChart_image` | `Geometry/CoordinateBoxChart.lean:66` | PASS；同胚满射把原像身份转成精确像身份。 |
| 27 | `coordinateBoxChart_measurePreserving` | `Geometry/CoordinateBoxChart.lean:72` | PASS；坐标拆分和平移组合保持原体积。 |
| 28 | `coordinateBoxChart_restrict` | `Geometry/CoordinateBoxChart.lean:80` | PASS；原盒限制体积精确传到横向限制体积与轴向限制Lebesgue的乘积。 |
| 29 | `coordinateBoxAxisGrid` | `Spatial/CoordinateBoxTrace.lean:14` | PASS；一步网格只编码正轴长L=bᵢ−aᵢ。 |
| 30 | `coordinateBoxAxisGrid_period` | `Spatial/CoordinateBoxTrace.lean:17` | PASS；period精确为原物理轴长。 |
| 31 | `coordinateBoxChart_timeMeasure` | `Spatial/CoordinateBoxTrace.lean:21` | PASS；用真实timeMeasure定义改写第28项，无额外测度因子。 |
| 32 | `coordinateBoxLp` | `Spatial/CoordinateBoxTrace.lean:27` | PASS；实际原盒L²类传输到上述乘积L²类。 |
| 33 | `coordinateBoxLp_norm` | `Spatial/CoordinateBoxTrace.lean:33` | PASS；原L²范数精确保留。 |
| 34 | `coordinateBoxLp_ae` | `Spatial/CoordinateBoxTrace.lean:37` | PASS；传输代表a.e.等于u(insertNth(t+aᵢ,x))。 |
| 35 | `coordinateBox_weak_transport` | `Spatial/CoordinateBoxTrace.lean:48` | PASS；原第i坐标完整弱导数传到真实乘积域(0,1)方向，支撑与保测度内部供应。 |
| 36 | `coordinateBoxFaceTrace` | `Spatial/CoordinateBoxTrace.lean:66` | PASS；定义实际面L²类，false取左端积分E_L、true取右端积分E_0。 |
| 37 | `coordinateBoxFaceTrace_norm_sq` | `Spatial/CoordinateBoxTrace.lean:73` | PASS；任意数据对有2/L、2L的真实L²平方界。 |
| 38 | `coordinateBoxFaceTrace_representatives` | `Spatial/CoordinateBoxTrace.lean:84` | PASS；原完整弱身份内部推出a.e.连续切片及双端点，并还原原u、v的坐标线代表。 |
| 39 | `coordinateBoxFaceTrace_eq_continuous` | `Spatial/CoordinateBoxSobolevTrace.lean:13` | PASS；若原类有全局连续代表F，两面迹a.e.等于F在实际aᵢ／bᵢ面上的值。 |
| 40 | `weakJetBoxFaceTrace` | `Spatial/CoordinateBoxSobolevTrace.lean:48` | PASS；输入完整真实H¹ jet，采用其真实第i坐标弱导数。 |
| 41 | `weakJetBoxFaceTrace_norm_sq` | `Spatial/CoordinateBoxSobolevTrace.lean:54` | PASS；真实坐标分量收缩把同尺度界提升为原全梯度范数界。 |
| 42 | `weakJetBoxFaceTrace_eq_continuous` | `Spatial/CoordinateBoxSobolevTrace.lean:72` | PASS；jet内部供应完整弱导数身份，连续代表面值结论无需额外切片假设。 |

## 任意轴拆分、平移及零维横向

原空间是实际EuclideanSpace，所选i可为Fin(d+1)的任意元素。坐标拆分先用真实ofLp把欧氏向量看作坐标函数，按piFinSuccAbove提取xᵢ及其余succAbove坐标，再交换两个因子，并把横向函数空间转回欧氏空间。逆映射的insertNth与这些操作精确互逆。线性由每个真实坐标的加法、数乘验证；有限维性只用于取得连续线性等价。

目标是普通产品赋范空间，其范数为max范数。代码没有宣称该连续线性等价为欧氏等距，也未把它的算子范数放进迹常数。测度保持另由 `PiLp.volume_preserving_ofLp`、`volume_preserving_piFinSuccAbove`、乘积交换和 `PiLp.volume_preserving_toLp` 的真实体积身份组合证明。已读所用mathlib证明：欧氏与坐标乘积体积通过真实Haar归一化一致，坐标提取通过乘积矩形测度等式证明；这精确处理了坐标置换绝对Jacobian为1，而非把所有线性等价都当作保体积。

d允许为0，即原空间一维、横向为空指标空间。相关体积定理只要求Fintype而不要求非空；mathlib明确给零维欧氏体积为dirac 0。因此横向面测度在该情形为单位质量点测度，未退化成零测度或调用不存在的横向坐标。盒的开性、有界性和有限体积证明也没有选横向点。若非所选轴上某侧长不正，则横向盒可为空，结论在相应零限制测度上合法；非退化原盒当然包含在量词范围内。

盒图把轴向改为t=xᵢ−aᵢ，逆图插入t+aᵢ，横向保留原上下界a∘succAbove、b∘succAbove。forall_iff_succAbove把原全部坐标条件精确分成轴向与横向条件，得到原像和像等式。平移是实际Lebesgue保测度映射，结合图像限制及prod_restrict得到

\[
\mathrm{volume}|_{B}\longmapsto
(\mathrm{volume}|_{B_{\perp i}})\times(\mathrm{Lebesgue}|_{(0,L_i)}),
\qquad L_i=b_i-a_i.
\]

这里没有单位区间缩放、横截面平均或隐藏Jacobian，任意位置与任意正轴长均保留。

## 全弱测试、支撑方向与实际L²传输

通用仿射模块的A是任意真实连续线性等价，h(x)=Ax+b；显式MeasurePreserving h ν μ是该通用定理的前提。具体盒应用内部证明该前提，未把真实几何义务留给调用者。

对每个目标测试φ∈SpatialTest(T)，原测试取φ∘h。全空间C∞由链式法则给出，紧支由同胚拉回紧集得到，且tsupport(φ∘h)=h⁻¹(tsupport φ)⊆h⁻¹(T)⊆S。实际条件正是h⁻¹(T)⊆S；若反向包含则不足以保证测试合法，代码没有此错误。导数是D(φ∘h)(x)e=Dφ(hx)(Ae)，平移不贡献导数，方向并未误用A⁻¹e。

affineTransportLp实际以逆图复合原L²类，并使用逆图保测度资格形成新的L²类；其a.e.代表、范数等式和测试积分换元都由该实际构造证明。弱导数传输逐个目标测试使用上述原测试及原积分身份，故保留全部弱测试和原负号，没有要求原状态逐点可微。测试本身及真实导数在紧集有限测度下属于L²，与状态的乘积确实可积；一般换元引理虽对任意系数写出身份，应用到弱测试时不依赖不可积积分的默认值。

在盒上，原所选标准基由真实坐标计算严格映成(0,1)，其余坐标为零；所选轴长L_i>0通过一步TimeGrid表示，timeMeasure就是Lebesgue|(0,L_i)，没有周期端点条件、方向限制或节点数因子。传输后的u、v的a.e.代表分别精确为原u、v在insertNth(t+aᵢ,x)上的限制。

## 从原全部弱数据到真实双面迹

第36项先对任意原L²数据对(u,v)定义端点积分的面L²类，第37项的范数界也对任意数据对成立；把它解释为u的实际迹时，第38项明确要求v是原第i坐标完整弱导数。它不把任意v的端点积分误称为原u的迹。

已直接复核所调用T076的完整切片桥：张量测试Φ(x)ψ(t)是实际紧支C∞测试，(0,1)方向导数恰为Φψ′；真实L²乘积可积性允许Fubini，原弱身份经横向分布唯一性给每个ψ的a.e.切片恒等式。随后对实际(ψ′,ψ)的L²测试对集合使用可分性、可数稠密集和每条切片配对的连续性，获得一个共同零测集外的全部测试身份，没有对不可数测试集直接取a.e.交集。

横向原盒内部已证明开且限制测度有限，因此这一依赖的全部前提得到实际满足。T075再从真实弱切片构造唯一闭区间连续代表。新证明同时利用u、v的传输a.e.身份，分别还原原坐标线值类及原坐标线导数，得到同一个U满足完整弱身份和双端点等式。

端点积分约定是E_c=L_i⁻¹∫[u+(t−c)v]：E_{L_i}为左端、E_0为右端。因此定义中的false使用c=L_i，true使用c=0，分别给U(0)、U(L_i)；再代回原坐标就是aᵢ、bᵢ。这里不存在把c=0误认成左端或遗漏轴向平移。

真实乘积平方界经两项精确L²等距直接给出

\[
\|\operatorname{Tr}_{i,\pm}(u,v)\|_{L^2(B_{\perp i})}^2
\le \frac{2}{L_i}\|u\|_{L^2(B)}^2+2L_i\|v\|_{L^2(B)}^2.
\]

2/L_i与2L_i来自已验证的真实端点积分估计，未多乘或少乘面体积。常数不依赖位置、轴i、横向边长、网格或数据；轴长依赖显式保留，未宣称无尺度的统一迹常数。所有除法都由L_i>0保障。

## 全部H¹ jet与真实连续面值

weakJetBoxFaceTrace输入原盒上任意真实WeakSobolevJet(d+1,1)。其value为真实零阶L²值，第i导数由field 1的Sym.cons i Sym.nil分量取得；field_weak_derivative内部给出原全部测试身份，不增加光滑性或切片条件。

该分量在每点的绝对值不超过实际一阶Euclidean字段范数，使用derivativeComponent_ae及PiLp.norm_apply_le，再用L²支配得到‖∂ᵢu‖≤‖field₁u‖。平方单调和正系数2L_i于是给同一尺度的全梯度界，没有加入d、d+1或坐标CLM范数常数。未将一个任意指定字段充当梯度。

连续面值一致定理的实际额外条件是存在全局连续F且F与原值类在原盒内a.e.相同。证明通过逆盒图保测度把该a.e.身份拉回，再取a.e.横向切片；F复合真实连续坐标线在[0,L_i]连续。由一维闭区间连续代表唯一性，它和前述U在两个端点都相等。代入0得到F(insertNth(aᵢ,x))，代入L_i得到F(insertNth(bᵢ,x))。该过程没有访问原L²代表在零测边界上的任意点值。

所有H¹ jet的面L²类、界及弱切片端点构造不需要这一连续F前提；第39、42项只是进一步识别在该明确前提下的实际面值。它们没有声称对仅在开盒连续、无法延至边界的函数有任意面点值，也未证明所有H¹状态全局连续。仿射多项式具备这一识别所需的连续性，但多面迹核及校正还未在本批构造。

## 固定依赖、构建与公理

五模块Carleman导入闭包共72模块，其中67旧模块与base完全不变，新增恰为本批五模块。另检查关键旧验收版本：C022 SobolevRealization的25模块对 `a6c199412758d406be8c3f8d1e76587b9f820bc1`，C091 WeakIntervalTrace/WeakSliceEndpointTrace的62模块对 `a4d0f062b3a3d32e166af481ed93e38096a992c2`，C092 ProductFaceTrace的67模块对base，均无变化。关键原弱测试、真实jet、共同零测集切片证明、乘积端点L²类和数学库体积归一化也已直接读取。

原稿、已读治理协议、工具链pin及CI工作流未由本批改变。原稿SHA256为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean为4.35.0，本机mathlib实际HEAD为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且工作树干净。root显式导入五模块，CheckAxioms包含42项完整类型和公理输出。

42项完整展开类型逐项核对，均只依赖 `propext`、`Classical.choice`、`Quot.sound`。固定本机1626条显式公理记录无其他公理，无sorryAx；检查器通过privateToUserName遍历所有Carleman声明并递归collectAxioms。完整日志 `/tmp/carleman-box-face-full.log` 实际包含 `Build completed successfully (3705 jobs).` 和 `Axiom audit passed for all 5471 Carleman declarations.`。固定 `/tmp/carleman-box-face-local-axioms.txt` 为 **1,598,872 bytes**，SHA256 **`c01fc4eb2d2c0bb41165bd81cabf1a112b5939e6643d83b127f29bdbaacb1102`**。

已独立通过GitHub connector读取 [main CI 39176339765 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39176339765/attempts/1)：main/push，head SHA精确匹配固定版本，run为completed/success。lean（117819684260）、state-check（117819684440）、dashboard / snapshot（117820404681）三项jobs全部completed/success；实际工具链准备、构建、checked source记录、两份证据上传及同次快照步骤均success。同run的lean-ci-result artifact（12154039547）和lean-declaration-evidence artifact（12153984659）均绑定固定SHA。

已实际读取 `/tmp/carleman-box-face-main-ci/result.json`：status PASS，`checked_sha=source_head_sha=8c4571e511be4cb48a8fd9b76c11ddba9a16e975`，targets为Carleman，`finished_at=2026-10-18T23:26:22.716650+00:00`，ci_url与上述run/attempt一致。实际Lean 4.35.0提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib为上述pin。

原始远端 `/tmp/carleman-box-face-main-axioms/axioms.txt` 与固定本机副本已独立逐字节比较，完全相同：**1,598,872 bytes**，SHA256 **`c01fc4eb2d2c0bb41165bd81cabf1a112b5939e6643d83b127f29bdbaacb1102`**。另逐名核对远端42/42完整展开类型及基础公理，1626条显式记录无其他公理、无sorryAx；实际末行为 **`Axiom audit passed for all 5471 Carleman declarations.`**。未混用其他SHA或后续工作区产物。

## 验收决定

**C093：PASS，可升级为REVIEWED，scope保持AUXILIARY。** 固定42项未发现坐标方向、支撑原像、体积因子、原代表恢复、弱测试范围、双端点次序或尺度方面需要修复的缺陷；同SHA正式CI及原始远端公理证据已独立核实。

原Lemma B.1还需物理零迹识别、多面迹映射的仿射核校正及回缩后的统一逼近；本批不提升B.1/B.2/P1或其他原文命题，scope保持AUXILIARY，原文仍12/26。本次仅写本报告，没有修改数学实现、台账、原稿或root导入，没有commit/push。
