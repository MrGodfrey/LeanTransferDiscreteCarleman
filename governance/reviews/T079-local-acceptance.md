# T079 / C095 独立本机验收

- `checked_sha`: `9e23cd8be8716b986762484e947b242ba8465323`
- `base_commit`: `d0fb274fb6f24830fd03428cddb86bbf9f034474`
- `reviewed_at`: `2026-10-18T23:46:40+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：单位参考立方体上全部原弱 H² 状态、任意所选面集合的边界仿射逼近；原真实面迹零条件推出所选整个闭面上消失的实际仿射多项式及真实 H¹ 残差，维数常数先于面集合与状态。原物理盒子的统一 h² 缩放仍待，原文完整结果保持 **12/26**。

直接以 `git show` 读取固定四模块的全部证明、15项实际展开类型、关键依赖与原 `paper/main.tex` Appendix B 的 Lemma B.1（`lem:fd-boundary-affine`，TeX 2796–2836）。执行者规格、既有验收和 CI 均未代替本次数学核对；后续工作树增量不属范围。治理协议沿用已读版本，并核对本批未改变。

## 全部15项声明

名称省略共同前缀 `Carleman.`；固定位置以 `Carleman/` 为根，顺序与交付 JSON、C095 和 T079 的名单一致。

| # | 声明 | 固定位置 | 独立数学核对 |
|---|---|---|---|
| 1 | `openCoordinateBox_convex` | `Geometry/CoordinateBoxConvexity.lean:14` | PASS；开盒是所有真实坐标线性投影的开区间原像之交，凸性内部证明。 |
| 2 | `openCoordinateBox_nonempty` | `Geometry/CoordinateBoxConvexity.lean:22` | PASS；每条边严格正时，真实坐标中点向量属于开盒，包含零维情形。 |
| 3 | `openCoordinateBox_volume_pos` | `Geometry/CoordinateBoxConvexity.lean:29` | PASS；开且非空给 Lebesgue 正测度，有界性给有限测度后才转 real 体积严格正。 |
| 4 | `unitCube_diameter_bound` | `Geometry/CoordinateBoxConvexity.lean:35` | PASS；实际欧氏平方范数按坐标求和得 dist²≤d，再用 d≤d² 得 dist≤d；d=0 合法。 |
| 5 | `affineBoxJetLinearMap` | `Spatial/AffineJetTraceIdentities.lean:12` | PASS；原真实仿射 H¹ jet 的加法及数乘由实际值类线性和完整弱 jet 值注入性证明。 |
| 6 | `affineBoxJetLinearMap_apply` | `Spatial/AffineJetTraceIdentities.lean:26` | PASS；打包后精确等于原实际仿射 jet，不替换导数字段。 |
| 7 | `weakJetBoxFaceLinearMap_affine` | `Spatial/AffineJetTraceIdentities.lean:29` | PASS；真实值及第 i 个真实弱梯度分量分别与仿射值／导数映射相同，故真正弱面迹精确识别为仿射面迹。 |
| 8 | `unitCubeFace_norm_le` | `Spatial/AffineJetTraceIdentities.lean:40` | PASS；长度1的实际平方迹界给 `‖Tr_F u‖≤2(‖u‖+‖∇u‖)`，对任意面与全部 H¹ jet 成立。 |
| 9 | `h1_value_gradient_add_bound` | `Spatial/AffineJetTraceIdentities.lean:52` | PASS；分别对真实 L² 值和完整一阶 L² 字段应用三角不等式后相加。 |
| 10 | `h2AffineResidual_eq_jet_sub` | `Spatial/UnitCubeH2Affine.lean:15` | PASS；在完整原开盒上以值注入性识别 T074 残差为原 H² 一阶截断减实际仿射 jet，所有弱字段同时相等。 |
| 11 | `unitCube_h2_affine_approximation` | `Spatial/UnitCubeH2Affine.lean:27` | PASS；单位域几何前提全部内部供应；维数常数先于任意原 H² jet，输出无约束仿射逼近且右端只有原 Hessian 半范数。 |
| 12 | `unitCube_selected_affine_trace_bound` | `Spatial/UnitCubeBoundaryAffine.lean:14` | PASS；所选面上真实零迹、迹线性和第7项给仿射迹=残差迹的负值；有限乘积 max 范数统一控制全部所选面。 |
| 13 | `unitCube_h1_boundary_correction` | `Spatial/UnitCubeBoundaryAffine.lean:35` | PASS；T078 核校正和真实 jet 加法恒等式组合，常数 `1+2K` 在 J、w、p 之前，q 在所选闭面处处零。 |
| 14 | `unitCube_h2_boundary_affine` | `Spatial/UnitCubeBoundaryAffine.lean:67` | PASS；先取 H¹ 校正与 H² 逼近常数后量化 J、u；实际零迹下输出边界仿射 q，误差界右端为 `C‖field₂u‖`。 |
| 15 | `unitCube_h2_boundary_affine_actual` | `Spatial/UnitCubeBoundaryAffine.lean:92` | PASS；返回实际仿射映射 p 与真实完整 H¹ 残差 r，值类 a.e. 等于原 u−p，保留闭面逐点零条件和实际范数界。 |

## 原全弱状态、范数与单位域几何

固定结论使用 `WeakSobolevJet (d+1) 2 (volume.restrict Q) Q`，Q 为真实开单位立方体。已直接复核 `weakJetSubmodule`：全部0、1、2阶实际 L² 字段，由每个多指标、每个坐标和每个完整 SpatialTest 的分布恒等式连接；没有选定光滑代表、有限元状态、预设逼近、单独切片或边界点值条件。`truncate 1≤2` 直接保留原0、1阶字段及其全部弱身份。输入覆盖该原弱 H² 空间全部状态。

值是原标量 L² 类。一阶 `DerivativeFiber n 1` 的 Euclidean 范数恰为所有 n 个坐标弱导数平方和；二阶字段以 `Sym (Fin n) 2` 为多指标，每个混合多指标计一次，符合本项目原稿的 D² 约定。结果中的 `‖value r‖+‖field 1 r‖` 是真实 L² 值范数加完整梯度 L² 范数，未混用 jet 产品的 max 图范数，也未将某一个坐标导数代替梯度。T074 用 n² 上界控制双坐标 Hessian 分量总和，保守放大维数常数，没有少算混合导数而获得虚假小常数。

开盒的定义是所有坐标满足 a_j<x_j<b_j。凸性证明真正使用 EuclideanSpace.proj 的线性原像；非空性取实际中点。体积正性调用非空开集的 Lebesgue 正测度，并由已证盒子有界保证 measure≠∞，所以 ENNReal.toReal 不会因无穷变零。最终单位立方体的有限测度、开放、凸、正体积及直径界均由具体数据供应，不是外留假设。

单位域内各坐标差的平方≤1，求和得 ‖x−y‖²≤n；n 为自然数又满足 n≤n²，非负开平方得 dist≤n。这是合法但非最优的维数直径上界。基础几何声明包含 n=0；最终面结果使用 n=d+1≥1，因而 n≥1 可用于从 `‖r‖+n‖∇r‖` 推出 `‖r‖+‖∇r‖`，没有除以零或把零维横截面排除。一维区间 d=0 仍属最终结论。

## 真实仿射 jet 与 T074 残差识别

`AffineCoefficients n` 是 ℝ×(ℝⁿ→L[ℝ]ℝ)，实际多项式为常数项加连续线性项；已有满射性保证全部仿射映射均可这样表示。`affineBoxJet` 的值是该多项式的原盒上 L² 类，各坐标导数是线性项在对应标准基向量上的真实常数 L² 类。`coordinateFirstJet` 将这些已经证明的完整弱坐标身份装配为实际 H¹ jet。

新线性映射没有默认“选择的 jet 应该线性”，而是将加法、数乘两边送入实际 value 映射，利用原开域与测度集中于该域条件下的 `WeakSobolevJet.value_injective`。该注入性逐阶使用完整弱导数唯一性，所以相等的不只是值，也包括全部真实导数字段。

T074 的 h2MeanAffine 由原弱梯度均值和正确的值均值构造，其 h2AffineResidual 已是完整 H¹ 弱残差。新第10项先将其值展开为 `u−boundedAffineLp(h2MeanAffine u)`；一阶截断减仿射 jet 的值展开为同一 L² 差，应用相同值注入性得整个 jet 相等。该辅助项显式接受“p 表示 h2MeanAffine u”的等式，但最终第11项从真实仿射系数满射性内部产生 p 和该等式，最终结果未留下该前提。

令 n=d+1。T074 的一般界为 `(2^n+1)n D²‖field₂u‖`，且左端为 `‖r‖+D‖field₁r‖`。新证明内部选 D=n，再用 n≥1 控制所需梯度项。因此无约束常数可取

`B=(2^n+1)n³>0`。

B 在任意 u 之前选择，只依赖 n。所有几何及弱正则适用条件由原单位域和原 jet 提供，没有将 T074 最终逼近估计当成新假设，也没有以全 H² 范数掩盖所要求的齐次 Hessian 半范数。

## 真正弱面迹及闭面校正

已直接读取所调用的坐标盒迹实现。`coordinateBoxChart` 是拆分第 i 个坐标并平移 a_i 的真实映射，限制 Lebesgue 测度精确变为横向盒测度与长度 b_i−a_i 的区间测度乘积；没有未计雅可比。原完整弱坐标导数传输为轴向 (0,1) 弱导数，然后已验收的全部弱切片定理产生真正连续区间代表。上下两面类分别等于同一个代表的右、左端点，满足实际 `2/L`、`2L` 范数界；它们不是原 L² 代表在零测面上的任意取值。

`weakJetBoxFaceLinearMap` 将真实原 jet 的 value 与第 i 个一阶分量送入这个实际迹映射。第7项逐一识别仿射 jet 的这两个输入，故其弱迹严格等于实际 `affineBoxFaceMap`。对长度1的单位域，先有 `‖Tr_F w‖²≤2‖w‖²+2‖∇w‖²`；借右端非负和平方比较得到第8项的常数2。这个界对所有原 H¹ jet 和所有上下坐标面成立，不要求 w 连续。

T078 的仿射面核已经使用真实面 L² 类及连续仿射多项式识别：零 L² 类给横向开盒 a.e. 零，连续性将其提升到开盒处处零，再由开盒闭包等于闭盒扩展到整个闭面，包括边、角。这里只对实际仿射多项式使用连续性，不要求原 u 有全局连续代表。零维横截面的真实 Lebesgue 测度和开放集正测度仍适用，未错误地假设所有点都零测。

所选面由任意 `Finset (Fin n × Bool)` 表示；由于全部面有限，这覆盖所有面子集。其面迹映射的目标是固定全部面的有限乘积，选中面取实际迹，未选中分量取零，范数为 max。已有有限维核校正先对每个该线性映射的真实 range 用有界原像定理校正入核，再在所有有限面集合上选统一正上界，得到 K；不是假设目标误差估计或面迹单射。K 依赖固定盒及维数，单位盒固定后仅依赖维数，且位于 J 和 p 之前。

第12项对选中面利用真实线性性写出

`Tr_F(w−affineJet p)=Tr_F w−Tr_F(affineJet p)=−Tr_F(p)`。

随后范数消去负号并使用第8项；未选中分量为零。max 范数允许同一个界控制整个所选迹族，无额外 |J| 因子，也没有把 max 冒写成原平方和范数。这个合法证明路线足以供应原校正；面集合为空时全部分量为零、零迹条件和闭面约束均为空，仍正常成立。

第13项调用 T078 得到 q 属于真实所选闭面核，并有 `E(p−q)≤K‖selectedTrace p‖`，其中 E 为实际 L² 值加全梯度范数。新仿射 jet 线性性给精确身份

`w−affineJet q=(w−affineJet p)+affineJet(p−q)`。

对这个真实 jet 身份应用分别的值／梯度三角界及所选迹界，独立重算得到 `E(w−q)≤(1+2K)E(w−p)`。故 A=1+2K>0 在 J、w、p 前选定。没有把未经识别的残差范数用于校正。

## 最终量词与原 B.1 对应

第14、15项的实际展开类型均为 `∀d, ∃C>0, ∀J, ∀u, [所选真实弱迹为零] → ∃...`。代码先取得 A、B，再选择 C=A·B>0，然后才引入 J、u；C 因而不依赖面集合、原状态或中间近似多项式。面零迹仅对原 u 的一阶截断要求，它是真正 L² 面类等于零，正是原 B.1 的零迹条件在参考域的表达。没有增加 H¹₀、光滑代表、节点、先验逼近或单独弱切片假设。

第15项返回实际仿射映射 p 和真实 H¹ jet r，明确选择 `r=truncate u−affineBoxJet q`。使用 Lp 差的代表身份与仿射值类 a.e. 身份证明 `value r=u−p` a.e.；由于 r 是完整弱 jet，其 field₁ 是该真实差的全部弱梯度，不是任意另选向量场。所选整个闭面上 p 逐点为零，同时 `‖value r‖+‖field₁r‖≤C‖field₂u‖`。

这完成了原 B.1 证明中单位参考立方体上无约束弱 H² 逼近、真实零迹、有限面仿射核校正及三角组合，覆盖所有面集合而非某种预选边界模式。原 B.1 还要求回到物理盒子 B_K 后的 `‖v−p_K‖+h‖∇(v−p_K)‖≤Ch²‖D²v‖`，其中 C 只依赖维数和网格比较界。当前四模块未供应实际弱 H²、体积范数及面迹的完整仿射缩放和该统一 h² 估计，不能把固定参考域常数误报为物理网格结论。原 H¹₀ 到物理面零迹的连接、两非平行面仿射核为零的明确后续结论及 B.2 也不在本批。保持 AUXILIARY，原文计数12/26，不提升完整 B.1/B.2/P1。

## 依赖版本、本机构建与公理

四模块的 Carleman 导入闭包共170模块，其中166旧模块与基线逐字相同，新增恰为本批四模块。关键既有成果的实际依赖闭包还分别与独立验收版本核对：

- [T074 / C090](T074-local-acceptance.md)：`ConvexH2AffineApproximation` 的130模块闭包与 `55dbf36858608cc7ff9300ef61430e18fa0bdadf` 完全相同。
- [T077 / C093](T077-local-acceptance.md)：`CoordinateBoxSobolevTrace` 的72模块闭包与 `8c4571e511be4cb48a8fd9b76c11ddba9a16e975` 完全相同。
- [T078 / C094](T078-local-acceptance.md)：`AffineBoundaryCorrection` 的129模块闭包与基线 `d0fb274fb6f24830fd03428cddb86bbf9f034474` 完全相同。

上述依赖已有固定版本 PASS；本次另直接核对其关键证明与当前调用，包括实际坐标／测度迹、闭面核、有限维原像校正、全弱 jet 定义及值注入性、Hessian 分量与 T074 误差链。验收范围仍按本批结论，不自动继承未完成的原文目标。

原稿、治理协议、Lean/mathlib pin 及 CI 工作流未由本批改变。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`；Lean 为4.35.0，本机 mathlib 实际 HEAD 为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且工作树干净。root 导入全部四模块，CheckAxioms 增量只增加15项完整类型与公理输出，既有全局递归检查器未削弱。

固定 `/tmp/carleman-unit-boundary-full.log` 实际含 `Build completed successfully (3716 jobs).` 和 `Axiom audit passed for all 5631 Carleman declarations.`。固定 `/tmp/carleman-unit-boundary-local-axioms.txt` 为 **1,626,068 bytes**，SHA256 **`e81a2110bc792e0977ee770cd3b4f904adf91ffd6e29f155656184c68b780f26`**。逐名检查15/15项完整类型及公理记录，每项只依赖 `propext`、`Classical.choice`、`Quot.sound`；全部1682条显式公理记录均无其他公理。递归检查包括生成的辅助声明，无 sorryAx 或无依据数学公理；四个新模块也无 sorry/admit/axiom/unsafe。

## 同 SHA 正式远端证据

已独立通过 GitHub connector 读取 [main CI 39177599750 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39177599750/attempts/1)：main/push，head SHA 精确匹配固定版本，run 为 completed/success。lean（117823386186）、state-check（117823386356）、dashboard / snapshot（117824109548）三项 jobs 均 completed/success。实际工具链准备、证明构建、checked source 记录、两份证据上传及同次看板生成成功。同 run 的 lean-ci-result artifact（12155205739）和 lean-declaration-evidence artifact（12154044536）均绑定固定 SHA、main 且未过期。

已实际读取 `/tmp/carleman-unit-boundary-main-ci/result.json`：status PASS，`checked_sha=source_head_sha=9e23cd8be8716b986762484e947b242ba8465323`，targets 为 Carleman，`finished_at=2026-10-18T23:44:38.229367+00:00`，ci_url 精确对应该 run/attempt。实际 Lean 4.35.0 提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib 为上述 pin。

原始远端 `/tmp/carleman-unit-boundary-main-axioms/axioms.txt` 与固定本机文件已独立逐字节比较，完全相同：**1,626,068 bytes**，SHA256 **`e81a2110bc792e0977ee770cd3b4f904adf91ffd6e29f155656184c68b780f26`**。远端15/15项完整类型和公理记录逐名匹配；全部1682条显式记录仅有三项正常基础公理，末行为 **`Axiom audit passed for all 5631 Carleman declarations.`**。未混用其他提交、其他 run 或后续工作区产物。

## 验收决定

**C095：PASS，可升级为 REVIEWED，scope 保持 AUXILIARY。** 固定15项未发现原弱状态范围、真实面迹、残差识别、闭面条件、常数量词、Hessian 半范数或退化情形方面需要修复的缺陷。完整同 SHA 三项 CI 与原始公理证据均已独立核实。

本次只写本报告，没有修改数学实现、台账、原稿或 root 导入，没有 commit/push。范围保持 AUXILIARY，原物理尺度 B.1 仍待，原文计数保持12/26。
