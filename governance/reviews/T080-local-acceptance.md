# T080 / C096 独立本机验收

- `checked_sha`: `68b77bdd9b152ba18e226a6a093892f548c2d90f`
- `base_commit`: `9e23cd8be8716b986762484e947b242ba8465323`
- `reviewed_at`: `2026-10-18T23:53:46+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：实际正对角盒图、真实体积和面测度换元、全部仿射多项式的拉回等价及真实L²／全梯度／h加权H¹缩放。完整原Lemma B.1的统一h²逼近组合尚待；原文保持 **12/26**。

独立从固定提交导出源码，读取四模块全部证明、35项完整展开类型及关键依赖，对照固定 `paper/main.tex` Appendix B的Lemma B.1（`lem:fd-boundary-affine`，TeX 2796–2838）。执行者规格与CI没有代替数学核对；后续工作区的物理盒逼近和校正模块不属于本报告。

## 全部35项声明

名称均省略公共前缀 `Carleman.`，位置以 `Carleman/` 为根；顺序与交付JSON一致。

| # | 声明 | 固定位置 | 独立数学核对 |
|---|---|---|---|
| 1 | `coordinateDilation` | `Geometry/CoordinateBoxScaling.lean:14` | PASS；实际正对角连续线性等价，逐坐标逆为除以正侧长。 |
| 2 | `coordinateDilation_apply` | `Geometry/CoordinateBoxScaling.lean:39` | PASS；实际坐标为ℓᵢxᵢ。 |
| 3 | `coordinateDilation_symm_apply` | `Geometry/CoordinateBoxScaling.lean:42` | PASS；实际逆坐标为ℓᵢ⁻¹xᵢ。 |
| 4 | `coordinateDilation_basis` | `Geometry/CoordinateBoxScaling.lean:45` | PASS；真实标准基eᵢ映为ℓᵢeᵢ。 |
| 5 | `coordinateDilation_norm_le` | `Geometry/CoordinateBoxScaling.lean:56` | PASS；逐坐标平方和给欧氏范数界L，无额外维数因子。 |
| 6 | `coordinateDilation_symm_norm_le` | `Geometry/CoordinateBoxScaling.lean:66` | PASS；m>0及m≤ℓᵢ给真实逆范数界m⁻¹。 |
| 7 | `coordinateDilation_jacobian` | `Geometry/CoordinateBoxScaling.lean:78` | PASS；真实标准基矩阵为diag(ℓ)，实际绝对行列式为∏ℓᵢ。 |
| 8 | `physicalBoxChart` | `Geometry/PhysicalBoxChart.lean:12` | PASS；实际同胚Φ(y)=a+Dℓy。 |
| 9 | `physicalBoxChart_apply` | `Geometry/PhysicalBoxChart.lean:16` | PASS；平移和每个轴的正尺度准确。 |
| 10 | `physicalBoxChart_preimage_open` | `Geometry/PhysicalBoxChart.lean:21` | PASS；物理开盒的原像恰为开单位盒。 |
| 11 | `physicalBoxChart_image_open` | `Geometry/PhysicalBoxChart.lean:34` | PASS；满射同胚把上述原像身份转为精确像身份。 |
| 12 | `physicalBoxChart_preimage_closed` | `Geometry/PhysicalBoxChart.lean:40` | PASS；全部非严格坐标不等式精确对应，保留边角。 |
| 13 | `physicalBoxChart_preimage_face` | `Geometry/PhysicalBoxChart.lean:53` | PASS；任意轴、上下两个整个闭面均精确对应。 |
| 14 | `physicalBoxChart_image_face` | `Geometry/PhysicalBoxChart.lean:64` | PASS；闭面像身份由真实同胚及原像身份得到。 |
| 15 | `physicalBoxChart_facePoint` | `Geometry/PhysicalBoxChart.lean:71` | PASS；insertNth面参数化与横向正对角图逐点交换。 |
| 16 | `integral_physicalBoxChart` | `Geometry/PhysicalBoxChart.lean:88` | PASS；真实Lebesgue换元给物理积分=J乘参考积分。 |
| 17 | `physicalBoxChart_face_jacobian` | `Geometry/PhysicalBoxChart.lean:100` | PASS；横向侧长积精确为J/ℓᵢ，分母严格正。 |
| 18 | `affineCoefficientChange` | `Spatial/AffineBoxPullback.lean:13` | PASS；对全部仿射系数给显式线性等价及双向逆。 |
| 19 | `affineCoefficientChange_apply` | `Spatial/AffineBoxPullback.lean:40` | PASS；对应实际多项式复合Ay+b。 |
| 20 | `affineBoxPullback` | `Spatial/AffineBoxPullback.lean:48` | PASS；真实盒图代入一般仿射系数等价。 |
| 21 | `affineBoxPullback_apply` | `Spatial/AffineBoxPullback.lean:52` | PASS；所有点上p̂=p∘Φ。 |
| 22 | `affineBoxPullback_derivative` | `Spatial/AffineBoxPullback.lean:58` | PASS；实际第i坐标导数为ℓᵢ∂ᵢp。 |
| 23 | `affineBoxPullback_zero_face_iff` | `Spatial/AffineBoxPullback.lean:66` | PASS；整个闭面的逐点消失双向等价，包括边角。 |
| 24 | `affineBoxValueMap_norm_sq` | `Spatial/AffineBoxNormScaling.lean:12` | PASS；真实bulk L²类的范数平方等于实际多项式平方积分。 |
| 25 | `affineBoxFaceMap_norm_sq` | `Spatial/AffineBoxNormScaling.lean:20` | PASS；真实弱迹类经连续代表身份等于实际面平方积分。 |
| 26 | `affineBoxValueMap_scaling_sq` | `Spatial/AffineBoxNormScaling.lean:31` | PASS；原物理L²范数平方因子恰为J。 |
| 27 | `affineBoxFaceMap_scaling_sq` | `Spatial/AffineBoxNormScaling.lean:38` | PASS；真实面L²范数平方因子恰为J/ℓᵢ。 |
| 28 | `affineBoxDerivativeMap_norm_sq` | `Spatial/AffineBoxNormScaling.lean:57` | PASS；真实常导数L²范数平方为盒体积乘坐标导数平方。 |
| 29 | `coordinateBox_volume_scaling` | `Spatial/AffineBoxNormScaling.lean:70` | PASS；以常函数1作真实换元得到体积缩放。 |
| 30 | `affineBoxGradientMap_norm_sq` | `Spatial/AffineBoxNormScaling.lean:75` | PASS；实际完整Euclidean梯度范数平方等于全部坐标导数平方和。 |
| 31 | `affineBoxGradientMap_scaling_sq` | `Spatial/AffineBoxNormScaling.lean:79` | PASS；参考梯度平方精确为J⁻¹Σℓᵢ²‖∂ᵢp‖²。 |
| 32 | `affineBoxGradientMap_scaling_bound_sq` | `Spatial/AffineBoxNormScaling.lean:91` | PASS；m≤ℓᵢ逐项平方比较，得到正确方向的m²界。 |
| 33 | `affineBoxValueMap_scaling` | `Spatial/AffineBoxNormScaling.lean:101` | PASS；两边非负，平方身份给精确√J因子。 |
| 34 | `affineBoxGradientMap_scaling_bound` | `Spatial/AffineBoxNormScaling.lean:108` | PASS；m>0、J>0保障平方比较还原真实范数界。 |
| 35 | `affineBox_h1_scaling_bound` | `Spatial/AffineBoxNormScaling.lean:116` | PASS；m=h/κ后合并真实bulk与梯度，系数恰为κ√J。 |

## 实际几何、Jacobian与零维情形

原空间是实际EuclideanSpace。`coordinateDilation`的正向、逆向分别为xᵢ↦ℓᵢxᵢ和xᵢ↦ℓᵢ⁻¹xᵢ；hℓ逐项严格正，因而双向逆和所有后续除法合法。加法与数乘按坐标验证，有限维性用于连续性。两个范数界用真实欧氏平方和以及侧长上下界逐项比较，没有把坐标函数空间的最大范数当作欧氏范数，也没有引入√d。

`affineJacobian`的原定义是实际连续线性等价之线性部分行列式的绝对值。证明在真实Euclidean标准正交基下计算矩阵为diag(ℓ)，再使用行列式与矩阵表示的一致性及对角行列式公式，得到J=∏ℓᵢ>0。这不是任意指定的Jacobian字段。

Φ(y)=a+Dℓy对任意位置a和任意正侧长ℓ成立。正侧长使每个开、闭区间不等式双向等价；闭面由闭盒与所选坐标等式定义，所以上下闭面以及全部边角一并精确传输。`facePoint`的逐坐标证明使用insertNth与succAbove，横向图没有漏掉或重复任何坐标。

所用真实仿射换元依赖已直接读取：线性图的Haar测度行列式公式和平移保测度先给map Φ volume=J⁻¹•volume，再处理域限制和积分。新定理用正J消去逆因子，得到∫B f=J∫Q f∘Φ。通用换元身份虽然允许任意f，新范数应用中的实际仿射多项式已由有界盒上的连续性证明MemLp，平方积分是真实可积积分，不依赖不可积积分的默认零值。

第i个面采用真实横向欧氏Lebesgue测度，横向行列式为∏j ℓ(i.succAbove j)=J/ℓᵢ。环境维数d可为0：空乘积为1，零维体积为单位点质量，空梯度为零。面命题使用环境d+1≥1，但允许横向d=0；一维端点的横向Jacobian恰为1，没有错误置零或选择不存在的横向坐标。

## 全部仿射多项式和真实面迹

`AffineCoefficients d`是ℝ与真实连续线性泛函空间的乘积。一般(A,b)的变换为(p₀,p₁)↦(p₀+p₁b,p₁∘A)，显式逆为(q₀,q₁)↦(q₀−q₁(A⁻¹b),q₁∘A⁻¹)。双向逆、加法和数乘均实际证明；已核对旧的仿射多项式表示与实际导数构造，因此量词覆盖所有仿射多项式，而非挑选的一组特定试函数。

物理图代入后，p̂(y)=p(Φ(y))逐点成立，导数坐标为ℓᵢp₁(eᵢ)。p₁是原实际仿射多项式的真实Fréchet导数及弱导数。闭面消失的等价使用真实面像／原像和逐点多项式身份；没有把面内a.e.消失未经证明地提升为整个闭面消失。

bulk映射通过实际多项式MemLp构造真实L²类；face映射是原弱迹线性映射作用于该真实值类及实际常导数。其a.e.面代表身份由T077的连续代表迹识别得到，仿射多项式具备全局连续性。新证明先用这些a.e.身份将范数平方化为真实积分，再换元，所以没有对任意L²代表直接取零测边界点值。

设Q为开单位盒、B=∏(aᵢ,aᵢ+ℓᵢ)，则实际结论为

\[
\|p\|_{L^2(B)}^2=J\|\widehat p\|_{L^2(Q)}^2,
\qquad
\|\operatorname{Tr}_{i,\pm}p\|_{L^2(F_{i,\pm})}^2
=\frac{J}{\ell_i}\|\operatorname{Tr}_{i,\pm}\widehat p\|_{L^2(\widehat F_{i,\pm})}^2.
\]

facePoint交换身份和横向真实换元共同决定J/ℓᵢ；这里没有J²、倒置因子或归一化面平均。系数空间的有限维范数没有进入这些物理L²常数。

## 全梯度与h加权H¹尺度

`affineBoxGradientMap`由所有坐标的真实常弱导数组成，使用 `firstGradientAssembly` 落在真实一阶Euclidean导数字段的L²空间。已读取该构造和 `coordinateFirstJet_gradient_norm_sq`：Sym.oneEquiv遍历全部一阶坐标，故梯度范数平方是全部坐标L²范数平方的精确和，不是单个方向或任意指定的系数范数。

常导数的实际L²范数平方等于物理体积乘p₁(eᵢ)²。结合真实体积缩放与导数身份，逐项消去正J得到

\[
\|\nabla\widehat p\|_{L^2(Q)}^2
=J^{-1}\sum_i\ell_i^2\|\partial_i p\|_{L^2(B)}^2.
\]

若m>0且m≤ℓᵢ，则逐项比较给m²‖∇p‖²≤J‖∇p̂‖²。两边非负后取平方根，结合bulk的精确√J身份，再令m=h/κ，得到

\[
\|p\|_{L^2(B)}+h\|\nabla p\|_{L^2(B)}
\le\kappa\sqrt J\bigl(\|\widehat p\|_{L^2(Q)}+\|\nabla\widehat p\|_{L^2(Q)}\bigr).
\]

最后定理实际量词为任意a、正侧长ℓ、h>0、κ≥1、全部h/κ≤ℓᵢ及全部仿射p；常数明确为κ√J，没有数据、位置、系数范数或额外维数因子。该方向只需侧长下界。后续B.1组合还需侧长上界ℓᵢ≤κh等条件，以控制物理域逼近和迹尺度；没有把这些后续义务当作本批已完成。

## 与原B.1的范围对应

原B.1要求全部原弱H²状态、指定物理面上的零迹，以及依赖维数和网格可比常数的统一h²仿射逼近。原文先拉回整个H²状态；本批采用的等价路线只拉回有限维仿射对象：物理凸盒上的全部弱H²状态由T074作无约束逼近，状态和残差留在物理域，利用物理弱迹界控制仿射迹，再在参考盒作有限面核校正并送回物理盒。这一路线不需要新增状态光滑性或预设逼近结论，但本批四模块仅完成其中的真实缩放接口。

因此本批没有证明或假设全部弱H²状态的拉回，亦没有将有限维仿射等价冒充全部Sobolev空间等价。参考校正、物理迹界、T074逼近及上下侧长比较的最终统一组合、两非平行面对应的仿射核零、H¹₀至物理面零迹的连接和B.2仍在本批范围之外。原文完整计数不能由本辅助结果增加。

## 固定依赖、构建与公理

四模块Carleman导入闭包共136模块，其中132旧模块与base不变，新增恰为本批四模块。另检查关键已验收声明版本：C062 AffineChangeVolume的34模块对 `0c632f37eadbcece6459555fef22a2bb4b3ca688`；C090 CoordinateFirstJet的42模块对 `55dbf36858608cc7ff9300ef61430e18fa0bdadf`；C094 AffineBoxTraceMap、ClosedCoordinateFaces、AffineBoundaryCorrection的123／27／129模块对 `d0fb274fb6f24830fd03428cddb86bbf9f034474`；C095 CoordinateBoxConvexity的28模块对base，均无变化。相关真实仿射换元、原弱迹、仿射全空间表示和全梯度平方和证明也已直接读取。

原稿、已读治理协议、工具链pin和CI工作流未由本批改变。原稿SHA256为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean为4.35.0，本机mathlib实际HEAD为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且工作树干净。root显式导入四模块，CheckAxioms包含35项完整类型及公理输出。

35项完整展开类型均已逐项核对，只依赖 `propext`、`Classical.choice`、`Quot.sound`。固定本机1717条显式公理记录无其他公理、无sorryAx；检查器通过privateToUserName遍历所有Carleman声明并递归collectAxioms。定向日志实际为3310 jobs；完整日志 `/tmp/carleman-box-scaling-full.log` 实际包含 `Build completed successfully (3720 jobs).` 与 `Axiom audit passed for all 5689 Carleman declarations.`。

已独立通过GitHub connector读取 [main CI 39178121016 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39178121016/attempts/1)：main/push、head SHA精确匹配固定版本，run为completed/success。state-check（117824935565）、lean（117824935916）、dashboard / snapshot（117825477795）三项jobs全部completed/success；工具链准备、完整构建、checked source记录、证据上传及同次快照步骤均success。同run的lean-ci-result（12154309521）和lean-declaration-evidence（12155086585）均绑定固定SHA。

已实际读取 `/tmp/carleman-box-scaling-main-ci/result.json`：status PASS，`checked_sha=source_head_sha=68b77bdd9b152ba18e226a6a093892f548c2d90f`，targets为Carleman，`finished_at=2026-10-18T23:51:29.708662+00:00`，ci_url与上述run/attempt一致。实际Lean 4.35.0提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib为上述pin。

原始远端 `/tmp/carleman-box-scaling-main-axioms/axioms.txt` 与固定本机 `/tmp/carleman-box-scaling-local-axioms.txt` 已独立逐字节比较，完全相同：**1,641,057 bytes**，SHA256 **`bf878da9a8c170099437ce92ced965a2f9c850804c3931e328d33a5bfb2fb1d8`**。另逐名核对远端35/35完整展开类型及基础公理，1717条显式记录无其他公理、无sorryAx；实际末行为 **`Axiom audit passed for all 5689 Carleman declarations.`**。未混用其他SHA或后续工作区产物。

## 验收决定

**C096：PASS，可升级为REVIEWED，scope保持AUXILIARY。** 固定35项未发现实际Jacobian、支撑／面对应、仿射覆盖、真实Lp迹、完整梯度、尺度方向、量词或常数方面需要修复的缺陷。同SHA正式三项CI及原始远端公理证据已独立核实。

本批不提升完整B.1/B.2/P1或其他原文命题，原文仍 **12/26**。本次仅写本报告，没有修改数学实现、台账、原稿或root导入，没有commit/push。
