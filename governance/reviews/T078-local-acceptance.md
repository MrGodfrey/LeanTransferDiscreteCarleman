# T078 / C094 独立本机验收

- `checked_sha`: `d0fb274fb6f24830fd03428cddb86bbf9f034474`
- `base_commit`: `8c4571e511be4cb48a8fd9b76c11ddba9a16e975`
- `semantic_checked_at`: `2026-10-18T23:36:51+00:00`
- `reviewed_at`: `2026-10-18T23:39:14+00:00`
- `result`: **PASS**。
- `axiom_check`: **PASS**。
- 范围：**AUXILIARY**。真实面迹的线性结构、全部闭面上的仿射核识别和单位立方体上的有限维核校正。完整 B1 的 H²/零迹组合及物理尺度统一、B2/P1 仍待，原文覆盖保持 12/26。

本报告直接读取固定提交七模块的全部 41 项完整展开类型及证明、关键实际依赖，并对照原 `paper/main.tex` 的 B1 证明、`governance/MATH_SPEC.md` 及 `governance/analysis/T078-affine-face.md`。未以执行者报告、旧验收或 CI 代替语义核查；后续工作树增量不在本次范围内。

## 全部 41 项声明

名称均加前缀 `Carleman.`；源码位置相对于固定提交的 `Carleman/`。

| # | 声明 | 源码位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `fiberEndpoint_integrable_slices` | `Spatial/FaceTraceLinearity.lean:13` | PASS；一般 SFinite 横向测度下，平方 Fubini 给 a.e. 切片 L²，再以有界区间系数给端点密度 L¹。 |
| 2 | `fiberEndpointLp_add` | `Spatial/FaceTraceLinearity.lean:30` | PASS；先有 a.e. 切片可积性，再拆分实际积分，得到 L² 类加法。 |
| 3 | `fiberEndpointLp_smul` | `Spatial/FaceTraceLinearity.lean:50` | PASS；实际代表的数乘与端点积分一致。 |
| 4 | `fiberEndpointLinearMap` | `Spatial/FaceTraceLinearity.lean:68` | PASS；真实端点算子组装为两份乘积 L² 数据上的线性映射。 |
| 5 | `finiteDimensional_kernel_correction` | `Spatial/FiniteKernelCorrection.lean:14` | PASS；实际有限维 range 的有界原像给核元素 q 和系数距离界。 |
| 6 | `finiteFamily_kernel_correction` | `Spatial/FiniteKernelCorrection.lean:30` | PASS；有限映射族取正总上界，使同一常数先于族索引和所有输入。 |
| 7 | `coordinateBoxTransportLinearMap` | `Spatial/CoordinateBoxTraceLinearMap.lean:12` | PASS；实际保测度盒图的逆拉回 L² 线性映射。 |
| 8 | `coordinateBoxTransportLinearMap_apply` | `Spatial/CoordinateBoxTraceLinearMap.lean:20` | PASS；逐字等于原 coordinateBoxLp，不是新定义的替代传输。 |
| 9 | `coordinateBoxFaceLinearMap` | `Spatial/CoordinateBoxTraceLinearMap.lean:24` | PASS；原实际传输与正确上下端点算子的线性复合。 |
| 10 | `coordinateBoxFaceLinearMap_apply` | `Spatial/CoordinateBoxTraceLinearMap.lean:33` | PASS；逐字等于原 coordinateBoxFaceTrace。 |
| 11 | `weakJetBoxFaceLinearMap` | `Spatial/CoordinateBoxTraceLinearMap.lean:37` | PASS；完整 H¹ jet 的实际 value/弱坐标导数送入同一面迹。 |
| 12 | `weakJetBoxFaceLinearMap_apply` | `Spatial/CoordinateBoxTraceLinearMap.lean:43` | PASS；逐字等于原 weakJetBoxFaceTrace。 |
| 13 | `AffineCoefficients` | `Spatial/AffineBoxTraceMap.lean:14` | PASS；ℝ×实际 Euclidean 空间上的 CLM，是完整有限维仿射系数空间。 |
| 14 | `affineCoefficientPolynomial` | `Spatial/AffineBoxTraceMap.lean:16` | PASS；构造真实 affine map。 |
| 15 | `affineCoefficientPolynomial_apply` | `Spatial/AffineBoxTraceMap.lean:19` | PASS；实际值精确为 c+A(x)。 |
| 16 | `affineBoxValueMap` | `Spatial/AffineBoxTraceMap.lean:23` | PASS；有界盒上的真实多项式 L² 类，线性性在 a.e. 代表层面证明。 |
| 17 | `affineBoxValueMap_ae` | `Spatial/AffineBoxTraceMap.lean:48` | PASS；值类 a.e. 等于同一多项式。 |
| 18 | `affineBoxDerivativeMap` | `Spatial/AffineBoxTraceMap.lean:52` | PASS；实际常导数 A(e_i) 的 L² 类及线性性。 |
| 19 | `affineBoxDerivativeMap_weak` | `Spatial/AffineBoxTraceMap.lean:77` | PASS；全部原 SpatialTest 下的实际弱导数身份。 |
| 20 | `affineBoxFaceMap` | `Spatial/AffineBoxTraceMap.lean:85` | PASS；将真实值类和弱常导数送入实际坐标面迹。 |
| 21 | `affineBoxFaceMap_ae` | `Spatial/AffineBoxTraceMap.lean:90` | PASS；实际面迹 a.e. 等于原闭面参数化下的多项式限制。 |
| 22 | `closedCoordinateBox` | `Geometry/ClosedCoordinateFaces.lean:13` | PASS；全部闭坐标区间的实际 Euclidean 盒。 |
| 23 | `closure_openCoordinateBox` | `Geometry/ClosedCoordinateFaces.lean:16` | PASS；所有正边长下，开盒闭包精确为闭盒，含零维横向情形。 |
| 24 | `coordinateFacePoint_continuous` | `Geometry/ClosedCoordinateFaces.lean:30` | PASS；insertNth 面参数化的真实连续性。 |
| 25 | `coordinateClosedFace` | `Geometry/ClosedCoordinateFaces.lean:37` | PASS；闭盒与坐标端点超平面的交集，保留边缘和角点。 |
| 26 | `coordinateClosedFace_eq_image` | `Geometry/ClosedCoordinateFaces.lean:41` | PASS；整个闭面精确为闭横截面的 insertNth 像，两个方向均证。 |
| 27 | `affineBoxFaceMap_eq_zero_iff` | `Spatial/AffineBoundaryKernel.lean:15` | PASS；真实面 L² 类为零 iff 同一多项式在整个闭面处处为零。 |
| 28 | `affineBoxSelectedFaceMap` | `Spatial/AffineBoundaryKernel.lean:49` | PASS；全部面真实 L² 类的有限乘积映射，未选面设零。 |
| 29 | `affineBoxSelectedFaceMap_apply` | `Spatial/AffineBoundaryKernel.lean:57` | PASS；逐面真实分量身份。 |
| 30 | `affineBoxSelectedFaceMap_kernel` | `Spatial/AffineBoundaryKernel.lean:65` | PASS；核精确等于全部所选闭面上的消失空间。 |
| 31 | `affineBox_uniform_kernel_correction` | `Spatial/AffineBoundaryKernel.lean:84` | PASS；固定盒上同一核校正常数先于任意面集 J 和任意仿射输入。 |
| 32 | `affineBoxSelectedFaceMap_norm_le_rss` | `Spatial/AffineBoundaryKernel.lean:95` | PASS；实际有限乘积 max 范数≤所选面 L² 范数平方和的平方根。 |
| 33 | `affineCoefficientPolynomial_surjective` | `Spatial/AffineBoundaryCorrection.lean:14` | PASS；任意 affine map 由其 p(0) 和实际导数表示，无斜率或边界限制。 |
| 34 | `affineBoxGradientMap` | `Spatial/AffineBoundaryCorrection.lean:25` | PASS；所有真实弱坐标类组装为完整 Euclidean 梯度 L² 类。 |
| 35 | `affineBoxJet` | `Spatial/AffineBoundaryCorrection.lean:29` | PASS；由已证全部弱坐标身份构造真正 H¹ jet。 |
| 36 | `affineBoxJet_value` | `Spatial/AffineBoundaryCorrection.lean:34` | PASS；jet 的值类等于实际多项式值类。 |
| 37 | `affineBoxJet_gradient` | `Spatial/AffineBoundaryCorrection.lean:37` | PASS；jet 完整一阶字段等于同一真实梯度映射。 |
| 38 | `affineBox_bulk_norm_bound` | `Spatial/AffineBoundaryCorrection.lean:40` | PASS；固定盒的两个有限维连续映射给实际 bulk 值范数加完整梯度范数界。 |
| 39 | `affineBox_uniform_h1_correction` | `Spatial/AffineBoundaryCorrection.lean:53` | PASS；系数核校正转为同一 p−q 的实际 bulk H¹ 误差。 |
| 40 | `affineBox_uniform_h1_correction_rss` | `Spatial/AffineBoundaryCorrection.lean:72` | PASS；以真实面迹平方和取代 max 范数，q 和核资格不变。 |
| 41 | `unitCube_uniform_affine_correction` | `Spatial/AffineBoundaryCorrection.lean:85` | PASS；固定单位立方体后 ∃C>0 先于全部 J、p；常数仅依赖环境维数。 |

## 原文对应和范围

原 B1 `lem:fd-boundary-affine`（`paper/main.tex:2803`）的证明先在单位立方体取得未校正仿射近似，随后在有限维仿射空间中，用面限制映射的核和正交补范数等价取得核中的修正项（`paper/main.tex:2823` 起）。本批证明这个面核校正步骤：给任意仿射 p，存在在所有所选闭面上消失的仿射 q，使真实 `‖p−q‖L²+‖∇(p−q)‖L²` 由 p 的真实所选面迹范数平方和控制。

原证明的正交补/最小化器路线被实际 range 上的有界原像路线替代。原论证所需的是存在核元素及其距离界，本批准确供应；没有声称 q 是正交投影或最小化器。最终的 L² 范数加梯度范数控制也足以给原 H¹ 范数控制。

尚未把此校正与 T074 全部弱 H² 状态的仿射逼近、原零迹及其迹线性组合成完整 B1，也未将一般物理盒子的 h/边长可比性统一缩放完成。原 H¹₀ 与物理面零迹接口、两非平行面迫使仿射核为零的专门结论及 B2 网格/权组合仍待；不能据此提升完整 B1/B2/P1。AUXILIARY 与原文 12/26 的范围陈述准确。

## 端点积分的真实性、线性与全部弱状态

直接核对 `FiberEndpointIntegral` 的真实定义为 `L⁻¹∫₀ᴸ[f(x,t)+(t−c)v(x,t)]dt`。当 v 是 f 的弱区间导数时，c=L 对应下端点、c=0 对应上端点。新 `coordinateBoxFaceLinearMap` 的 Bool 分支严格保持这一方向，未把 c 本身误当成所求端点。

新切片引理从 f²、v² 的乘积可积性和 Fubini 取得 a.e. 切片 L²；对 c∈[0,L]、t∈(0,L) 有 `|t−c|≤L`，从而 `(t−c)v` 仍为切片 L²。仅使用有限区间的测度有限性把和变为 L¹，横向 μ 只要求 SFinite，没有偷加 μ 有限。加法证明在拿到两个密度的实际可积性之后才调用 `integral_add`；数乘依照真实 a.e. 代表和积分数乘恒等式。没有利用不可积积分的默认值伪造线性。

`fiberEndpointLp` 的实际 L² 资格及 `2/L·‖f‖²+2L·‖v‖²` 界来自真实积分平均估计。对原弱状态，`ProductWeakSlices` 从全部乘积域 SpatialTest 推出 a.e. 切片弱恒等式；其 `CountableWeakTests` 依赖用可分 L² 测试/导数对、可数稠密集和配对连续性取得同一个零测例外集，未交换不合法的不可数 a.e. 量词。`WeakSliceEndpointTrace` 随后构造每片连续代表并识别真实两端点值。

坐标盒图是删除第 i 坐标并平移其原点的实际 Euclidean 保测度图，没有按边长缩放；区间长度恰为 b_i−a_i。新线性传输的值与已有 coordinateBoxLp 逐字一致。原弱坐标 e_i 经实际线性图变为 (0,1)，因此面迹是原盒子的实际弱坐标迹，不是另给的面数据。

`weakJetBoxFaceLinearMap` 取原 H¹ jet 的 scalar 值和该真实弱坐标分量，覆盖全部 H¹ 状态；未要求光滑代表。对仿射 p，才使用它本身的连续性及原 a.e. 值身份。`coordinateBoxFaceTrace_eq_continuous` 在每个 a.e. 切片上将连续弱代表与 p 的连续限制识别，然后延伸到两个端点，故 `affineBoxFaceMap_ae` 确为原面多项式限制。

## 全部仿射对象与完整闭面核

`AffineCoefficients n=ℝ×(SpatialCoordinates n→Lℝℝ)` 包含全部常数和斜率，实际多项式为 c+A(x)。`affineCoefficientPolynomial_surjective` 对任意 affine map 取 `(p(0),affineScalarDerivative p)`，用实际仿射差分身份得到逐点相等。不存在只对某个子空间或预先满足边界模式的输入证明校正的限制。

真实值类由有界盒上 affine function 的 L² 资格构造，其线性性通过 Lp 的 a.e. 加法/数乘身份证明。方向导数类是实际 A(e_i) 常函数的 L² 类；弱身份由真实 affine HasFDerivAt、Lipschitz 积分分部及全部原 SpatialTest 得到。面映射是这些实际值/导数类与真正面迹的复合。

所有边长为正时，`closure_openCoordinateBox` 通过 Euclidean/Pi 同胚与各 Ioo 的闭包证明开盒稠密于整个闭盒。`coordinateClosedFace` 是闭盒与坐标端点超平面的交集；insertNth 像等式两方向都证明，故包括面边缘及角点，而非仅相对开面。

若 affineBoxFaceMap(p)=0，实际限制函数在开横截面 a.e. 为零。该限制连续；使用 Lebesgue 测度对非空开集为正的 `eqOn_open_of_ae_eq` 得到开横截面上处处为零，再以连续性和闭包等式得到整个闭横截面为零，最后用像等式转到完整闭面。反方向由整个闭面处处为零及 a.e. 限制身份得到 L² 类零。因此该等价并不把任意 Lp 代表在零测边缘的点值当作迹。

最终环境维数为 d+1，d∈ℕ；包含一维区间，此时横向维数 d=0，横截面是零维 Euclidean 空间，其真实 Lebesgue 测度和开集唯一性仍适用。它没有声称一个零维环境中的坐标面定理。所有中间闭盒和仿射值构造本身允许零维，未加入未声明的维数下界。

## 有界原像、统一面族和真实 H¹ 误差

对任意有限维实赋范 V 和任意实际线性 L:V→W，先将 L 限制为 `f:V→L.range`。有限维性使其连续，并提供源空间及实际 range 所需的完备性；f 对该 range 的满射性由 range 的定义直接证明。已核对 mathlib `exists_preimage_norm_le` 是有界满射的实际开映射结论，并非假设目标核距离界。对 y=f(p) 取原像 r，令 q=p−r，即得 Lq=0 和 `‖p−q‖=‖r‖≤C‖Lp‖`。未要求 L 对整个 W 满射，也未假定一个未证明的有界投影。

有限映射族的常数取 `1+∑j c_j`，每个 c_j>0，故它同时大于所有单映射常数，并先于族索引及 p；空族和零映射同样包含。应用中的索引是全部有限面集合 J，而非只对一个调用时选定的 J 选常数。`affineBoxSelectedFaceMap` 对全部 2(d+1) 个实际面 L² 空间取同一有限乘积，未选面分量置零，故整个 family 有固定的目标空间。其核逐分量等价于在 J 的全部闭面上消失。

该 Pi 范数实际是 max 范数，证明没有把它冒充 Hilbert 平方和。`norm_le_rss` 逐分量用单项平方≤所选平方和及非负平方根，直接证明 max≤RSS；未选面是零，空 J 的 RHS 也确为零。零迹输入时核校正界迫使 q=p，不会破坏原已满足的核元素。

`affineBoxJet` 由真实值类和所有已证明的弱坐标类组装；其 value 和完整 Euclidean 一阶字段明确分别等于 affineBoxValueMap 和 affineBoxGradientMap。于是 jet(p−q) 的真实值和梯度正是同一多项式 p−q 的真实 L² 值和完整梯度，未用系数范数替代最终物理范数。

固定盒上这两个从有限维系数空间出发的线性映射自动连续，以 `B=1+‖V‖+‖G‖` 得 `‖value(p)‖+‖gradient(p)‖≤B‖p‖`。与系数核校正常数 K 组合得到正数 BK，再使用 max≤RSS。所有步骤保持同一 q 的实际闭面核资格。

一般盒的 K、B 可以依赖 a、b，完整类型明确在 a、b 后才出现 ∃C；未把这一点误称网格统一。单位立方体将端点固定为 0、1，最终 `∀d, ∃C>0, ∀J,p, ∃q`，常数只依赖环境维数 d+1，不依赖面集、仿射状态或后续网格/权参数。它没有把“仅依赖维数”误说成“与维数无关”。

## 固定版本、构建与递归公理

七新模块的 Carleman 导入闭包共 129 个模块，其中 122 个既有模块相对 base 逐字节不变；root 明确导入七模块。AGENTS、治理流程、原论文、Lean/mathlib pin 和两个 CI workflows 均未改变。原论文 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

固定 `/tmp/carleman-affine-face-full.log` 实际含 `Build completed successfully (3712 jobs).`。固定 `/tmp/carleman-affine-face-local-axioms.txt` 的 41 项完整类型全部逐项与源码核对，每项恰有一条类型和一条递归公理打印。全部 1667 条显式公理打印（1663 个不同声明）均已扫描，只有 `propext`、`Classical.choice`、`Quot.sound`；末行确认全部 5600 个 Carleman 声明（含生成声明）递归审计通过。

公理审计程序相对 base 未改，仍遍历全部 Carleman 声明、递归收集公理并拒绝白名单外项。本批新增显式类型/公理打印；七新模块无 sorry/admit 或新增公理。本机固定产物为 1,616,594 bytes，SHA256 `85db3f2c37a61a7c87a1a50ad05c67c49ece104fdd121c0829ce9e1250a5f42d`。Lean 4.35.0，mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`。

## 远端证据与签发状态

已独立读取真实 [main/push run 39177128793](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39177128793/attempts/1)，attempt 1，head SHA 精确匹配 checked SHA，顶层 completed/success。三个 jobs 均 completed/success：state-check `117821994819`、lean `117821995024`、dashboard / snapshot `117822620409`。未在任何 job 仍运行时签发。

同次 artifact 元数据已独立读取：`lean-ci-result` id `12154717954`、`lean-declaration-evidence` id `12154514335` 均绑定该 run、main 和同一 head SHA。实际读取 `/tmp/carleman-affine-face-main-ci/result.json`，status=PASS，checked_sha/source_head_sha 均为 `d0fb274fb6f24830fd03428cddb86bbf9f034474`，ci_url 精确对应该 run/attempt，finished_at=`2026-10-18T23:37:07.712911+00:00`，target 为 `Carleman`。Lean 4.35.0（commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）及 mathlib pin 均匹配。

实际读取 `/tmp/carleman-affine-face-main-axioms/axioms.txt`，与固定本机副本逐字节完全相同：1,616,594 bytes，SHA256 `85db3f2c37a61a7c87a1a50ad05c67c49ece104fdd121c0829ce9e1250a5f42d`。远端产物再次核对 41 项完整类型和递归公理，全部 1667 条显式公理打印无白名单外项，末行确认所有 5600 项递归审计通过。

最终结论：**T078 / C094 PASS，可将 C094 升为 REVIEWED，保留 AUXILIARY。** 41 项及所声明真实面迹/仿射核校正范围通过，未发现数学缺陷。完整 B1/B2/P1 仍待，原文覆盖保持 12/26。本 Agent 仅写本报告，未修改实现、台账、root 或原稿，未 commit/push。
