# T042 / C058 独立本机验收

- `checked_sha`: `0df65a77f4a13fdab4641c30a3843f02bd8b1af8`
- `base_commit`: `3d5aa9cec281974bef7da9d37ffa11a8f9f75670`
- `reviewed_at`: `2026-10-18T18:55:27+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：实际中心内缩、凸域内正支撑缓冲、真实紧支 Lipschitz 函数的全空间弱 H¹、实际节点函数的内缩 H¹ jet。**不计 H¹ 逼近收敛、节点 H¹₀ 成员或 H² 正则性；原文完成仍为 12/26。**

本次从固定提交导出全部源码，独立读取三个新模块的所有证明、24 项实际展开类型及相关依赖，对照原 `paper/main.tex` Section 6 的 conforming P1 空间和节点插值。执行者规格及 CI 是核实对象，没有代替数学判断。后续未提交草稿不在本报告范围。

## 全部 24 项声明

完整名称均以前缀 `Carleman.` 开始。位置属于固定提交的 `Carleman/Spatial/`，顺序与 C058、T042 和交付声明清单一致。

| # | 声明（省略 Carleman.） | 位置 | 独立数学核对 |
|---|---|---|---|
| 1 | `centeredDilation` | `ConvexSupportContraction.lean:14` | PASS；实际映射 a+r(x−a) 和逆映射 a+r⁻¹(x−a)，两向互逆及连续性均证明。 |
| 2 | `centeredDilation_mem` | `ConvexSupportContraction.lean:23` | PASS；开凸 S、a∈S、0<r<1 下，closure S 的像由严格凸组合落在 S 内。 |
| 3 | `contractedFunction` | `ConvexSupportContraction.lean:33` | PASS；f 与逆同胚的实际复合，收缩支撑的方向正确。 |
| 4 | `contractedFunction_tsupport` | `ConvexSupportContraction.lean:37` | PASS；同胚的闭包原像公式给精确 tsupport 正向像，而非仅点态 support 包含。 |
| 5 | `contractedFunction_compact` | `ConvexSupportContraction.lean:48` | PASS；与同胚复合保持真实紧支。 |
| 6 | `contractedFunction_support_inside` | `ConvexSupportContraction.lean:53` | PASS；支撑公式与凸域内缩给整个闭支撑包含于 S。 |
| 7 | `contractedFunction_buffer` | `ConvexSupportContraction.lean:61` | PASS；紧支集包含于开 S，推出某正 δ 的整个闭 δ 邻域仍包含于 S。 |
| 8 | `contractedFunction_continuous` | `ConvexSupportContraction.lean:69` | PASS；原连续 f 与真实连续逆映射复合。 |
| 9 | `contractedFunction_hasFDerivAt` | `ConvexSupportContraction.lean:74` | PASS；在正确逆像点的实际导数 A，经链式法则成为 A∘(r⁻¹ Id)。 |
| 10 | `compactLipschitz_fderiv_memLp` | `CompactLipschitzSobolev.lean:14` | PASS；实际可测 fderiv 在紧支外为零、内部范数≤C，以有限体积 indicator 控制证明全空间 L²。 |
| 11 | `compactLipschitzDerivativeLp` | `CompactLipschitzSobolev.lean:28` | PASS；已证明可积的实际 fderiv 所生成的 CLM 值 L² 类。 |
| 12 | `compactLipschitzDerivativeLp_ae` | `CompactLipschitzSobolev.lean:32` | PASS；实际 L² 代表与 fderiv 的 volume-a.e. 身份。 |
| 13 | `compactLipschitzLp` | `CompactLipschitzSobolev.lean:35` | PASS；Lipschitz 给连续，真实紧支给 MemLp，构造原 f 的全空间 L² 类。 |
| 14 | `compactLipschitzLp_ae` | `CompactLipschitzSobolev.lean:39` | PASS；该标量 L² 类确实 a.e. 表示 f。 |
| 15 | `compactLipschitzSobolevJet` | `CompactLipschitzSobolev.lean:42` | PASS；Rademacher 给真实 a.e. HasFDerivAt，再由已证完整积分分部构造原弱 H¹ jet。 |
| 16 | `compactLipschitzSobolevJet_value` | `CompactLipschitzSobolev.lean:50` | PASS；value 精确等于原 f 的实际 compactLipschitzLp。 |
| 17 | `centeredDilation_lipschitz` | `ContractedNodalSobolev.lean:14` | PASS；两点差精确为 r(x−y)，Lipschitz 上界为 |r|，无额外维数因子。 |
| 18 | `contractedFunction_lipschitz` | `ContractedNodalSobolev.lean:25` | PASS；逆映射常数 |r⁻¹|，复合的真实 Lipschitz 常数为 C|r⁻¹|。 |
| 19 | `contractedSobolevJet` | `ContractedNodalSobolev.lean:30` | PASS；上述实际内缩函数的紧支与 Lipschitz 性供应真实全空间 H¹ 构造。 |
| 20 | `contractedSobolevJet_value_ae` | `ContractedNodalSobolev.lean:36` | PASS；jet 的 value a.e. 等于同一个 contractedFunction。 |
| 21 | `SimplicialPartition.nodalFunction_tsupport_subset` | `ContractedNodalSobolev.lean:46` | PASS；原节点函数在 closure S 外为零，闭包最小性给闭支撑包含；此项不需要有限索引。 |
| 22 | `SimplicialPartition.nodal_contraction_buffer` | `ContractedNodalSobolev.lean:53` | PASS；有限真实单元提供紧支，实际节点函数直接代入内缩缓冲定理。 |
| 23 | `SimplicialPartition.nodalContractedSobolevJet` | `ContractedNodalSobolev.lean:61` | PASS；边界节点零与真实几何条件供应既有全局 Lipschitz，得到同一节点函数内缩的全空间 H¹ jet。 |
| 24 | `SimplicialPartition.nodalContractedSobolevJet_value_ae` | `ContractedNodalSobolev.lean:68` | PASS；该实例的 value a.e. 精确等于原 nodalFunction 的真实内缩。 |

## 实际内缩、支撑和正缓冲

centeredDilation 直接构造 `D(x)=a+r(x−a)` 的 Homeomorph，逆函数明确为 `a+r⁻¹(x−a)`，r≠0 是互逆所需的公开条件。contractedFunction 定义为 `f∘D⁻¹`，故其非零点及闭支撑沿 D 的正向像移动；0<r<1 时的方向确为内缩。支撑恒等式使用真正同胚对闭包原像的精确保持，随后把 D⁻¹ 的原像转换成 D 的像；不要求 f 连续，也未混用 support 与 tsupport。

若 S 开且凸、a∈S、x∈closure S，D(x) 等于 `(1−r)a+rx`。固定 mathlib 的凸集内部／闭包组合定理要求内部点的系数严格为正、另一个系数非负且和为 1；这里分别由 r<1、r>0 和实数恒等式供应。S 开使 interior S=S，因而所得点在 S 内。该论证对闭支撑全部点成立，包含可能位于原边界上的点。

缓冲不是从“支撑点各自在 S 内”直接推出统一距离：首先由原 HasCompactSupport 经真实同胚复合得到紧闭支撑，再调用实际紧集与闭补集的分离性质，得到某 δ>0，使 Metric.cthickening δ 的整个集合包含于 S。已直接核对该 mathlib 定理及其闭厚化定义用途。δ 在量词上位于 S、a、r、f 之后，可依赖这些数据，没有宣称 r→1 时保持正下界或对网格／节点值统一。一般几何定理允许 S 无界，但 f 的紧支是明确输入。

连续性由复合证明。导数定理的输入是在 D⁻¹(x) 处的实际 HasFDerivAt f A；内层仿射映射的导数确实为 r⁻¹ Id，链式法则得到 A.comp(r⁻¹ Id)。没有把任意候选 CLM 重新命名为导数，也没有把 x 处的导数错误用于逆像点。这里尚未证明关于一族 r 的 a.e. 导数变换或积分换元／范数缩放；当前定理只是正确的逐点链式身份。

## 紧支 Lipschitz 的实际全空间弱 H¹

`compactLipschitz_fderiv_memLp` 对实际 fderiv 证明全空间 L²，而不要求调用者提供一个可积导数替身。固定 mathlib 的 measurable_fderiv 在此有限维 Euclidean 域、实值完备目标及相应 Borel 结构下可用；可测性供应强可测性。norm_fderiv_le_of_lipschitz 给每点导数算子范数≤C，包含非可微点处 fderiv 按定义取零的情况。tsupport f 外存在恒零邻域，真实 fderiv 为零。于是其范数由 `(tsupport f).indicator (fun _ => C)` 控制；该紧集可测且体积有限，证明 indicator 的 L² 后用真实支配定理得到 CLM 字段的 L²。没有假设整个 Euclidean 空间体积有限，也没有遗漏支撑外的导数。

标量类由 Lipschitz 连续性和紧支直接构造；导数类由刚证明的 fderiv MemLp 构造，两者都有完整 volume-a.e. 身份。Rademacher 在实际有限维 Euclidean 空间与 Lebesgue 加性 Haar 测度上给 f a.e. DifferentiableAt，继而给 HasFDerivAt f (fderiv f x) x。与导数类的 a.e. 身份合并后，准确满足 lipschitzGlobalJet 的实际导数前提。

已再次直接核对该依赖的完整弱身份：对每个原 SpatialTest univ，真实 Lipschitz 差商积分分部给 `∫ D_e f·φ=∫ D_{−e}φ·f`；测试函数光滑使右侧等于 `−∫ D_e φ·f`。全部坐标方向经实际 L² 连续线性求值进入 firstOrderJet 的全部 weakJetSubmodule 约束。SpatialTest 未缩减，仍为所有全空间 C∞ 紧支实值测试。故 Rademacher 只供应经典 a.e. 导数，真正分布导数仍由积分分部证明；结论不是把二者直接等同。结果为 `WeakSobolevJet d 1 volume univ`，value 精确等于实际标量 L² 类。

上述全空间成员结论只需真实 Lipschitz 和紧支，不需要 f 光滑、已有弱导数、既有 Sobolev 成员或额外可积性假设。C=0、零函数、d=0 等情况没有除以 C 或隐藏非空／正维前提。范数界在这里用于证明成员，未承诺原数值估计中的统一常数。

## 实际节点实例及量词边界

dilation 的两点差精确为 r(x−y)，因此其 Lipschitz 上界为 |r|；逆映射取 r⁻¹，复合常数为 C|r⁻¹|，并非 Cr。一般 contractedSobolevJet 对任意 r≠0 均有效，包括负 r 和 r=1；这些情形只声称全空间 H¹，不声称支撑内缩。正缓冲定理独立要求 0<r<1，二者的条件没有混淆，r=0 没有借实数零除法混入构造。

nodalFunction_tsupport_subset 从实际定义在 closure S 外取零及闭包最小性证明。它不需要 FaceMatching、BoundaryFitted 或有限索引；有限性只在后续使用有限紧单元覆盖以给 HasCompactSupport 时需要。因此 nodal_contraction_buffer 的纯支撑结论对任意点态节点输入 f 成立，不要求零边界或连续性，这是合法的几何陈述。

真实 nodal H¹ 实例则公开要求 S 开、FaceMatching、BoundaryFitted 和所有实际边界顶点值为零。已直接复核这些条件如何使原 nodalFunction 成为全空间连续零延拓，并通过有限个局部仿射函数与零函数的连续选择给真正全局 Lipschitz。以同一函数的紧支和 Lipschitz 代入 contractedSobolevJet 后，value a.e. 等于 `f_nodal∘D⁻¹`；没有换成任意重构、未知逼近序列或公理化候选。

nodalContractedSobolevJet 本身不要求凸性或 a∈S，因为这些条件与全空间 H¹ 保持无关；需要内支撑与 H¹ 同时成立时，须把它与明确要求开凸 S、a∈S、0<r<1 的缓冲定理合用。a∈S 明确排除空域中心选择，没有从空域擅自选中心。空网格的覆盖使 S 为空，此时几何缓冲的带中心前提不能实例化，最终 H¹₀ 证明仍应单独处理零函数情况。

## 原文对应与未完成义务

原 Section 6 在固定有界凸多面体、d=2 或 3 上定义 `V_h={v∈H₀¹(Ω):v|K∈P1}`，随后使用节点插值及其误差。当前更一般维数的实际内缩与弱 H¹ 成员构造，为把边界零的连续分片仿射节点函数放入此前真实 Dirichlet 光滑闭包提供准备。开凸域正中心和内缩是该证明路线中的明确几何条件，并未额外限制原凸多面体目标。

本批没有证明 r→1 时内缩在 H¹ 图范数中趋于原函数，也没有构造在正缓冲内光滑化的 H¹ 收敛。因此内缩函数的紧支和 H¹ 成员不能在本报告中直接升级成原节点函数属于 dirichletSubspace 的证明。节点 H¹₀ 成员、H² 椭圆正则性／完整域等式、H² 连续点值代表、具体网格与原统一数值误差以及连续热 CE 均未在本批完成。既有 T040/T041 的形式或分布图成果不因此扩大为这些后续结论。

C058 必须保持 AUXILIARY；原文 12/26 不变。台账 `extra_hypotheses=[]` 仅针对上述公开参数下的辅助目标，不表示完整 Proposition 6.1 已无未清偿条件。

## 固定依赖、构建和公理

导入闭包为 47 个 Carleman 模块，其中 44 个旧模块与基线逐字节一致，新增恰为本次三模块；固定 root 显式导入全部三个新模块。已经直接复核本批调用的真实节点支撑／紧支／Lipschitz、全空间弱积分分部及一阶 jet 构造；不是仅沿用旧报告标签。治理协议、原稿、工具链与 CI 工作流均与基线一致，MATH_SPEC 增加本阶段说明。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

本机 mathlib HEAD 已核实为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，工作树干净。已读取其实际凸组合内部定理、同胚支撑公式、紧集正闭厚化、fderiv 可测性／范数界、Rademacher 及积分分部相关证明和条件，调用处均满足要求。Lean pin 为 4.35.0。

固定 CheckAxioms 对 24 项逐名输出完整 `#check @...` 与 `#print axioms ...`，最后遍历经 privateToUserName 识别的所有 Carleman 声明递归 collectAxioms，只允许 `propext`、`Classical.choice`、`Quot.sound`。已核对固定本地 24/24 展开类型及每项公理集合，均为上述三项正常基础公理。C058、T042 和交付 JSON 的声明列表及顺序完全一致。

`/tmp/carleman-contraction-full.log` 实际包含 `Build completed successfully (3565 jobs).` 和 `Axiom audit passed for all 4504 Carleman declarations.`。固定本地 `/tmp/carleman-contraction-local-axioms.txt` 为 1,254,839 bytes，SHA256 `053315b3d2302f9ccb899ab8f55df65048b98fdafddff1e57e417c488e120839`。

已独立通过 GitHub connector 读取 [main CI 39155983776 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39155983776/attempts/1)：main/push，head SHA 为固定 `0df65a77f4a13fdab4641c30a3843f02bd8b1af8`，completed/success。lean（117759188880）、state-check（117759189168）、dashboard / snapshot（117759728443）三项 jobs 均 success；Lean pin、root 构建、checked source 记录及两份证据上传步骤均成功。同 run 的 lean-ci-result artifact（12147211682）和 lean-declaration-evidence artifact（12146838709）均绑定该 head SHA。

已实际读取 `/tmp/carleman-contraction-main-ci/result.json`：status PASS，`checked_sha=source_head_sha=0df65a77f4a13fdab4641c30a3843f02bd8b1af8`，targets 为 Carleman，`finished_at=2026-10-18T18:51:44.317671+00:00`；ci_url 与上述 run/attempt 完全一致，Lean 4.35.0 提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` 和 mathlib pin 均正确。

原始远端 `/tmp/carleman-contraction-main-axioms/axioms.txt` 与固定本机副本已逐字节比较，完全相同：**1,254,839 bytes**，SHA256 **`053315b3d2302f9ccb899ab8f55df65048b98fdafddff1e57e417c488e120839`**。另逐名复核远端 24/24 实际展开类型和公理集合，均恰为上述三项正常基础公理；远端末行实际为 **`Axiom audit passed for all 4504 Carleman declarations.`**。未发现 sorryAx 或未批准数学公理，未混用后续源码或产物。

## 验收决定

**C058：PASS，可升级为 REVIEWED，scope 保持 AUXILIARY。** 固定版本的 24 项未发现需要修复的陈述、量词、支撑、导数、可积性或实际节点实例缺陷；完整类型、递归公理及同 SHA 正式 main CI 证据均已独立核实。H¹ 逼近收敛、节点 H¹₀ 成员和 H² 正则性仍不属于本批已完成结果，原文 12/26 不变。

本次仅写本报告，没有修改数学源码、台账、覆盖表、原稿或 root 导入，没有 commit/push。
