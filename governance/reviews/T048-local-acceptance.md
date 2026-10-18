# T048 / C064 独立本机验收

- `checked_sha`: `2ccd0e5f1ae783f69c70d18593e09c79dfe7d7bd`
- `base_commit`: `ce719d2683c7509827e457ea2e15e0ce5451b487`
- `reviewed_at`: `2026-10-18T19:46:02+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：任意阶完整弱 Sobolev jet 的真实子域限制；任意实际 H¹ 状态的局部仿射代表与其全部弱梯度的识别；完整 conformingSpace 的逐单元多项式／梯度身份。**不包含全网格加权求和和原 allowed 权比较，原文完成仍为 12/26。**

本次独立读取固定提交的四个新模块全部证明、20 项实际展开类型和相关依赖，对照原 `paper/main.tex` Section 6 的完整 P1 状态空间及逆估计。执行者说明和 CI 是待核实材料，没有代替数学验收；后续未提交模块不属于本报告。

## 全部 20 项声明

完整名称均以前缀 `Carleman.` 开始。位置属于固定版本的 `Carleman/Spatial/`，顺序与 C064、T048 和交付 JSON 一致。

| # | 声明（省略 Carleman.） | 位置 | 独立数学核对 |
|---|---|---|---|
| 1 | `subdomainLp` | `SubdomainRestriction.lean:13` | PASS；T⊆S 给真实受限测度单调性，以同一代表的 MemLp.toLp 构造实际 L² 限制。 |
| 2 | `subdomainLp_ae` | `SubdomainRestriction.lean:17` | PASS；限制后的代表与原代表在 volume.restrict T 下 a.e. 一致。 |
| 3 | `SpatialTest.monoDomain` | `SubdomainRestriction.lean:20` | PASS；保留同一个测试函数、光滑性和紧支，只将 tsupport 包含传递到 S。 |
| 4 | `IsWeakSpatialDerivative.restrictSubdomain` | `SubdomainRestriction.lean:26` | PASS；对子域全部原测试，测试及真实导数在 T 外为零使两项积分准确限制，弱身份及负号不变。 |
| 5 | `derivativeComponent_subdomain` | `SubdomainRestriction.lean:57` | PASS；任意阶、任意 Sym 分量与实际限制交换，a.e. 转移方向使用正确测度单调性。 |
| 6 | `WeakSobolevJet.restrictSubdomain` | `SubdomainRestriction.lean:67` | PASS；逐阶限制全部字段，并逐个清偿所有相邻阶／坐标弱导数约束。 |
| 7 | `WeakSobolevJet.restrictSubdomain_value` | `SubdomainRestriction.lean:77` | PASS；零阶标量值精确等于原 value 的真实限制。 |
| 8 | `affineScalarDerivative` | `AffineWeakGradient.lean:16` | PASS；实际连续 AffineMap 的 contLinear，无任意导数候选。 |
| 9 | `affineScalar_hasFDerivAt` | `AffineWeakGradient.lean:19` | PASS；该实际 CLM 是每一点的真实 Fréchet 导数。 |
| 10 | `affineScalar_lipschitz` | `AffineWeakGradient.lean:23` | PASS；仿射两点差等于真实线性部分作用，算子范数给全局 Lipschitz。 |
| 11 | `weakDerivative_eq_affine` | `AffineWeakGradient.lean:31` | PASS；有限测度开域上构造真实常方向导数 L² 类，积分分部与完整弱唯一性识别任意已有 v。 |
| 12 | `WeakSobolevJet.gradient_eq_affine` | `AffineWeakGradient.lean:49` | PASS；遍历全部正交坐标并经 Sym.oneEquiv 恢复完整一阶 Euclidean fiber 的 a.e. 身份。 |
| 13 | `simplexCell_ae_interior` | `SimplicialLocalGradient.lean:14` | PASS；真实 frontier 零测给闭单元与其内部在 ambient volume 下 a.e. 相等。 |
| 14 | `simplexInterior_finiteMeasure` | `SimplicialLocalGradient.lean:22` | PASS；准确受限测度等式把真实紧单元的有限测度传给内部。 |
| 15 | `SimplicialPartition.cell_interior_subset` | `SimplicialLocalGradient.lean:30` | PASS；开凸 S 的 interior(closure S)=S 给单元内部包含；空 S 分支单独处理。 |
| 16 | `SimplicialPartition.cell_measure_le_domain` | `SimplicialLocalGradient.lean:40` | PASS；先以零测边界替换成内部，再用真实集合包含得到限制测度≤域测度。 |
| 17 | `SimplicialPartition.gradient_on_cell` | `SimplicialLocalGradient.lean:45` | PASS；任意原 H¹ jet 限制到单元内部，由局部标量身份和弱唯一性识别梯度，再按测度等式扩回闭单元。 |
| 18 | `affinePolynomialOfCoefficients` | `ConformingLocalPolynomial.lean:13` | PASS；实际坐标系数 c₀+Σcⱼxⱼ 构成真正 AffineMap。 |
| 19 | `affinePolynomialOfCoefficients_apply` | `ConformingLocalPolynomial.lean:17` | PASS；常数项与全部线性坐标的精确作用公式，索引无错位。 |
| 20 | `SimplicialPartition.conforming_local_polynomial` | `ConformingLocalPolynomial.lean:25` | PASS；完整 conformingSpace 成员刻画给每个单元的真实 p，同一 p 同时给 value 和全部弱梯度的 a.e. 身份。 |

## 子域限制保留完整测试与任意阶字段

subdomainLp 对任意 NormedAddCommGroup 值的真实 L² 类工作；T⊆S 使 `volume.restrict T≤volume.restrict S`，因此原代表在小测度下仍 MemLp。输出由同一个代表的 toLp 构造，并有在小测度下的 a.e. 身份。此处不要求原状态光滑、全空间延拓、有限测度或先验点态代表。

SpatialTest 仍是全部真实 C∞、紧支且 tsupport 包含于给定域的测试函数。每个 SpatialTest T 使用相同函数成为 SpatialTest S，未缩减测试族，也未用“子域测试由大域测试限制而来”这种不充分方向。对这一测试，T 外因不在 tsupport，其函数值和实际 Fréchet 导数均为零；两种积分的 integrand 因而在 T 外为零。已核对固定 mathlib 的 setIntegral_eq_integral_of_forall_compl_eq_zero 及 fderiv_of_notMem_tsupport，故积分从 T 到 S 的等式合法。再用实际 subdomainLp 的 a.e. 身份转换代表，得到完整 `∫D_eφ·u=−∫φ·v`，没有边界项或符号遗漏。

任意阶 derivativeComponent 的限制交换通过实际字段分量 a.e. 公式和 Lp.ext 证明。原域上的 a.e. 公式向子域转移时用的是上述小测度≤大测度，方向正确。restrictSubdomain 对任意 m 限制全部 `Fin(m+1)` 字段，并逐个保留 k、Sym α、坐标 i 的相邻阶完整弱条件；不是只限制零阶／梯度而漏掉高阶约束。零阶 value 身份作为空多重指标的交换式精确成立。m=0 时无相邻阶条件，定义仍正常。

## 实际仿射导数与完整弱唯一性

affineScalarDerivative 是实际 AffineMap 经有限维连续性形成 ContinuousAffineMap 后的 contLinear。其每点 HasFDerivAt 与两点差公式分别给真实经典导数和全局 Lipschitz，常数是该实际 CLM 的 NNReal 算子范数。

weakDerivative_eq_affine 没有仅凭 u 与 p a.e. 相等就直接微分所选代表。它对任意方向 e 构造常函数 `c=Dp(e)` 的真实 L² 类 w；有限域测度是公开前提并实际用于 MemLp_const。由 p 的真实 Lipschitz 和每点 HasFDerivAt 得真实 lineDeriv 等于 c，再调用已有差商积分分部桥，为同一 u 和 w 证明完整 IsWeakSpatialDerivative。与输入 hw 所描述的任意已有弱导数 v 比较，原全部 SpatialTest 的弱导数唯一性在开 S 上推出 v=w，继而得到 v a.e. 等于真实 fderiv p 的方向值。

已直接复核该唯一性依赖：两个弱身份相减后与全部紧支光滑测试正交；实际 L² 的局部可积性、开域光滑测试分离定理以及限制测度 a.e. 位于 S 给零类。该路线没有假设目标导数相等，也没有只对有限元测试使用有限维非退化性。

gradient_eq_affine 对每个正交基方向使用原 jet 的相邻层弱条件。有限坐标的 a.e. 结论合并后，经 Sym.oneEquiv 的双向身份逐分量恢复全部一阶 fiber。derivativeOneFiber 的实际定义是把 CLM 在全部正交坐标方向的值放入 EuclideanSpace，每个方向出现一次。因此结论是全梯度字段的 a.e. 等式，不是单一方向、算子范数或任意命名能量。d=0 时一阶 fiber 的分量集合为空，ext 给唯一零向量的正确身份。

## 单元内部、零测边界和测度转换

SimplicialPartition 的 inside 字段只给 `cell i⊆closure S`，代码没有把它当成 `cell i⊆S`。S 非空且开凸时，interior S=S 非空；固定 mathlib 的凸集内部闭包定理给 interior(closure S)=interior S=S。interior_mono 将 inside 合法提升为 `interior(cell i)⊆S`。S 为空的分支直接使用 closure ∅=∅ 与 inside 排除内部点，没有从空域选择一点，也不需要隐含非空假设。

实际单纯形 frontier 已证明在 ambient volume 下零测。排除 frontier 后，“属于 cell”与“属于 interior cell”等价，故两集合 a.e. 相等；Measure.restrict_congr_set 给其**受限测度精确相等**。由紧单元有限体积得到内部有限测度；由内部真实包含于 S 得闭单元受限测度≤S 受限测度。没有依赖 S 的边界零测去替代单元边界事实，也没有把环境 a.e. 与单元 a.e. 无条件互换。

gradient_on_cell 对任意真实 H¹ jet u，先以实际子域包含限制到开单元内部。其 value 的局部仿射身份来自原域 a.e. 的“若在 cell 则等于 p”，通过测度单调性及内部点属于 cell 得到；不是额外假设局部梯度。内部是有限测度开集，正好满足前述仿射弱唯一性条件。得到受限 jet 梯度身份后，再以实际字段限制的 a.e. 公式恢复原梯度代表，最后用内部／闭单元受限测度相等扩回整个 cell。结论始终是 a.e.，不声称在面、顶点逐点可微或代表逐点一致。

## 完整 conformingSpace 的状态范围

既有 conformingSpace 是实际分片仿射 L² 空间与任意 V 的交；前者是有限 indicator／坐标函数生成映射的 range，并已双向刻画为每个单元上的实际坐标仿射多项式。已直接复核该完整成员刻画及其 a.e. 分区前提：它没有把空间定义为某个节点插值映射的像，也没有预设全局梯度身份。

新 affinePolynomialOfCoefficients 用常 AffineMap 加实际坐标投影的线性组合，作用恰为 `c 0+Σj c j.succ*x j`。conforming_local_polynomial 直接从任意原 value 的空间成员取出这组系数，形成真正 p，并供给 gradient_on_cell。标量身份到闭单元的转换另外使用已经证明的 cell_measure_le_domain 及该闭单元的 a.e. 成员身份。最终同一个 p 同时表示原 value 与原全部一阶字段。

最终量词为任意有限真实单纯形分区、公开的域有限测度、开凸 S、任意 L² 子空间 V、任意真实 H¹ jet u，只要求 value u 属于完整 M.conformingSpace V。没有节点表示、节点边界值、FaceMatching、额外光滑性、H² 或谱限制。V 任意时 H¹ 是显式状态条件；在原 V=dirichletSubspace 情形，既有 dirichletSubspace_sobolev 已保证每个 V 成员具有真实 jet 见证，所以这一表达覆盖原完整 V_h，不缩小原状态范围。原有界凸多面体满足这里的开凸／有限测度条件。

本阶段只有真实局部身份，没有把全空间弱梯度定义为分片经典导数来回避证明，也没有承诺额外 T、节点数或维数统一的估计常数。原 Section 6 的全网格加权逆界仍需对这些实际字段做单元积分求和、原 allowed 权的统一比较以及尺度识别；其余 H² 插值、加权投影、椭圆正则性、连续热 CE 等义务也未因此完成。C064 保持 AUXILIARY，不提升 P011 或任何完整原文结果，原文仍 12/26。

## 固定依赖、构建与公理

本批导入闭包包含 84 个 Carleman 模块，80 个旧模块与基线逐字节一致，新增恰为本次四模块；固定 Carleman.lean 显式导入全部四模块。已直接检查本批真正调用的弱导数测试、Lipschitz 积分分部、弱唯一性、完整 jet、分片仿射空间与分区成员刻画。原稿、治理协议、工具链及 CI 工作流与基线一致；MATH_SPEC 增加本阶段说明。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

本机 mathlib HEAD 已核实为固定 `56a005855ea17e0b0958f73ec801ae140b0a1679`，工作树干净；读取的积分限制、支撑外导数为零、凸域 interior/closure 和相关依赖均属这一 pin。Lean pin 为 4.35.0。

固定 CheckAxioms 对本次 20 项逐一执行 `#check @...` 和 `#print axioms ...`，再遍历以 privateToUserName 识别的全部 Carleman 声明，递归 collectAxioms，仅许可 `propext`、`Classical.choice`、`Quot.sound`。固定本地 20/20 实际展开类型已逐名核对，每项公理集合恰为上述三项正常基础公理；交付 JSON 与固定 C064/T048 的声明顺序一致。

`/tmp/carleman-local-gradient-full.log` 实际包含 `Build completed successfully (3589 jobs).` 和 `Axiom audit passed for all 4715 Carleman declarations.`。固定本地 `/tmp/carleman-local-gradient-local-axioms.txt` 为 **1,311,538 bytes**，SHA256 **`0e619a89152b8167d3e1e10ef2c97f8606660e52fa2614d6ca85bb6012a054e2`**。

已独立通过 GitHub connector 核实 [main CI 39159881586 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39159881586/attempts/1)：main/push、head SHA 为固定 `2ccd0e5f1ae783f69c70d18593e09c79dfe7d7bd`，completed/success。state-check（117770755380）、lean（117770755613）、dashboard / snapshot（117771331125）三项 jobs 均 success；Lean pin、root 构建、checked source 记录和两份证据上传步骤均成功。同 run 的 lean-ci-result artifact（12148561707）和 lean-declaration-evidence artifact（12148531916）均绑定固定 SHA。

已实际读取 `/tmp/carleman-local-gradient-main-ci/result.json`：status PASS，`checked_sha=source_head_sha=2ccd0e5f1ae783f69c70d18593e09c79dfe7d7bd`，targets 为 Carleman，`finished_at=2026-10-18T19:42:41.915169+00:00`，ci_url 与上述 run/attempt 完全一致。Lean 4.35.0 提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` 和 mathlib pin 均正确。

原始远端 `/tmp/carleman-local-gradient-main-axioms/axioms.txt` 与固定本机副本已逐字节比较，完全相同：**1,311,538 bytes**，SHA256 **`0e619a89152b8167d3e1e10ef2c97f8606660e52fa2614d6ca85bb6012a054e2`**。另逐名复核远端 20/20 完整展开类型及正常基础公理集合，末行实际为 **`Axiom audit passed for all 4715 Carleman declarations.`**，无 sorryAx 或未批准数学公理；未混用后续源码或产物。

## 验收决定

**C064：PASS，可升级为 REVIEWED，scope 保持 AUXILIARY。** 固定版本 20 项未发现需要修复的测试范围、字段、导数唯一性、集合／测度转换或完整状态量词缺陷；完整类型、递归公理和同 SHA 正式 main CI 均已独立核实。全网格加权求和、原 allowed 权比较及其余 P1 义务仍待，原文 12/26 不变。

本次仅写本报告，没有修改数学源码、台账、覆盖表、原稿或 root 导入，没有 commit/push。
