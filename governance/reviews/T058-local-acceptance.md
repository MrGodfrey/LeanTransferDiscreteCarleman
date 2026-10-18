# T058 / C074 独立本机验收

- `checked_sha`: `9b4962ef9d03bb7bce6cc906a508857d57398c8c`
- `base_commit`: `fbcd888532fe88caff4907495fad399fe6feeb55`
- `reviewed_at`: `2026-10-18T20:59:58+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：真实有界弱梯度的Lipschitz代表、完整H¹₀分片仿射空间的真实节点表示，以及原Section 6 Step 1的 **`eq:p1-weighted-projection` 四类权投影稳定性**。完整 `prop:p1` 尚需H²插值、超逼近等义务，原文完整结果计数保持 **12/26**。

本次独立读取固定提交四个新模块全部证明、10项实际展开类型、相关真实依赖和T058规格，对照原 `paper/main.tex` Section 6的一致质量P1空间、Γ_d、四类权及投影估计。执行者说明和CI均未代替语义审查；后续工作区增量不属于本报告。

## 全部10项声明

完整名称均以前缀 `Carleman.` 开始；位置属于固定版本的 `Carleman/Spatial/`。顺序与固定C074、T058及交付JSON完全一致。

| # | 声明（省略 Carleman.） | 固定位置 | 独立数学核对 |
|---|---|---|---|
| 1 | `SpatialTest.convolution_ae_norm_bound` | `BoundedWeakGradient.lean:15` | PASS；非负单位质量真实光滑核和弱导数的a.e.界直接控制实际卷积积分，结果为B。 |
| 2 | `spatialLinearMap_norm_of_basis_bound` | `BoundedWeakGradient.lean:32` | PASS；完整正交坐标展开及每个坐标的范数界给实际CLM算子范数≤dB，含d=0。 |
| 3 | `convolution_lipschitz_of_bounded_weak_derivatives` | `BoundedWeakGradient.lean:51` | PASS；真实弱导数卷积交换和光滑性给实际fderiv全部坐标界，均值定理推出全局Lipschitz常数dB。 |
| 4 | `exists_lipschitzRepresentative_of_bounded_weak_derivatives` | `BoundedWeakGradient.lean:67` | PASS；实际mollifier序列a.e.收敛，同一全测集合上的距离极限保留Lipschitz界，再作真实实值扩张得到原L²类的全局代表。 |
| 5 | `SimplicialPartition.conforming_gradient_bounded` | `ConformingLipschitzRepresentative.lean:17` | PASS；任意完整空间成员的实际局部仿射多项式及真实常弱梯度给一个有限B，a.e.分区合法拼回全域。 |
| 6 | `SimplicialPartition.conforming_dirichlet_lipschitz_representative` | `ConformingLipschitzRepresentative.lean:32` | PASS；原H¹₀闭包清偿零延拓的全部全空间坐标弱身份，逐分量界在域外为零，因而构造实际零延拓的Lipschitz代表。 |
| 7 | `continuous_zeroExtend_zero_compl` | `FullConformingNodal.lean:12` | PASS；闭域外开集上的a.e.零值经连续性提升，再用开凸域interior(closure S)=S扩展到整个补集；空域分支明确。 |
| 8 | `SimplicialPartition.conforming_representative_affine_on_cells` | `FullConformingNodal.lean:35` | PASS；实际cell测度单调性、两个连续函数及真实单纯形内部稠密给整个闭单元的逐点仿射身份。 |
| 9 | `SimplicialPartition.conforming_dirichlet_nodal_representation` | `FullConformingNodal.lean:49` | PASS；任意完整conformingSpace成员内部取得真实连续代表，共享节点值唯一、边界节点为零，并证明原L²类精确等于nodalLp。 |
| 10 | `allowed_weight_full_projection` | `FullWeightedProjection.lean:12` | PASS；对完整空间实际orthogonalProjectionOnto的成员内部供应上述表示，消去T056的全部节点／边界表示前提，任意L²输入及原四类权获得统一δ、C。 |

## 有界弱导数到真实Lipschitz代表

第一步使用的卷积是实际Bochner积分∫v(y)κ(x−y)dy。κ为真实全空间C∞紧支测试，逐点非负且积分为1；反射／平移保持核的可积性和积分。a.e.的‖v(y)‖≤B乘非负核后，以真实积分范数界得卷积范数≤B。没有把卷积定义成任意逼近算子或假设所求导数界。

已直接复核WeakConvolution：以κ(x−·)作为原完整全空间弱测试，反射导数的负号与分部积分负号消去，得到u与核导数的卷积等于v与核的卷积。L²状态的局部可积性及核的紧支／光滑性给真实HasFDerivAt和卷积存在性，因此这一身份确实识别实际fderiv，而不是指定任意导数候选。新证明对每个Euclidean正交基方向都调用该身份。实际连续线性映射A由全部基向量展开，|x_i|≤‖x‖给‖A‖≤dB；真实全空间均值定理遂给同一个dB Lipschitz常数。

所用spatialMollifier为实际归一化ContDiffBump，内外半径分别1/(n+1)、2/(n+1)。半径趋零、比值恒为2，归一化核非负且质量1。原L²代表局部可积，固定mathlib的Lebesgue微分／逼近恒等核定理给整列卷积在同一个全测集合A上收敛到该代表。对任意x、y∈A，距离函数极限把所有卷积的共同Lipschitz不等式传到原值u(x)、u(y)。随后用真实 `LipschitzOnWith.extend_real`，保留同一常数扩张到全空间，且在A上与u相等，所以所得f与原L²类a.e.相同。扩张定理没有要求A闭，也包含空集和零常数分支；这里没有从逐点可选子序列错误推出两点统一收敛。

d=0时正交坐标集为空，实际CLM算子范数为0，dB=0；证明没有除以维数。Euclidean零维空间中的结论合法，未添非零维假设。首个卷积界虽用实B，其a.e.上界及单位质量已足以支持积分不等式；后续B为NNReal。

## 完整空间、全空间零延拓及常数隔离

conformingSpace的实际定义是全部分片坐标仿射L²函数与给定V的交，具有双向成员刻画；不是先定义成节点插值像。dirichletSubspace则是原H¹图范数中紧支光滑测试线性空间闭包的零阶像。任何z∈M.conformingSpace(dirichletSubspace S)因此内部具有真实H¹₀ jet见证u及value u=z，无需调用者另给光滑代表、节点数据或谱限制。

conforming_gradient_bounded利用T048的真实局部多项式／弱梯度识别，为每个单元取得p_K，使整个一阶fiber a.e.等于真实Dp_K的坐标向量。仿射导数恒定，B取Σ_K‖derivativeOneFiber(Dp_K)‖；有限索引保证这个和是有限非负实数。真实cell积分测度等式与a.e.分区把各单元界拼回S。它明确允许依赖网格、状态及单元数，仅用于代表存在性。

零延拓步骤没有假设一般H¹函数可零延拓。已直接复核DirichletTestPairing／DirichletZeroExtension：紧支于S的原光滑测试对任意全空间紧支光滑测试满足真实分部积分；两边是H¹ jet的连续线性配对，故身份通过原H¹闭包传给全部H¹₀成员。实际zeroExtendLp由同一函数的S-indicator构造，积分准确限制到S，给零延拓状态及各坐标梯度的完整全空间弱身份，域外梯度为零。

新证明将完整一阶fiber的界降到各坐标分量，再用zeroExtendLp的实际a.e.身份在S上保留B、在S外取0，满足上一节的全空间有界弱导数定理。由此产生C=dB及f。最终投影证明只使用f的存在、连续性、a.e.身份及边界零值，既没有读取C，也没有把B传给投影估计。δ与最终投影常数早于M及u选择；网格／状态相关dB不会进入统一常数。

## 边界零值、闭单元身份与节点表示

对实际零延拓的连续代表f，代码首先在开集(closure S)ᶜ上由indicator身份得到f=0 a.e.；Lebesgue测度在非空开集上正，故连续性把该身份提升到这个开集处处成立。连续函数的零集合闭，再扩展到closure((closure S)ᶜ)。S非空且开凸时，真实凸集内部闭包定理给interior(closure S)=S，因而这个闭包恰为Sᶜ；S为空单独化简。这样包括边界的整个补集上f=0，不曾把任意开集都当成正则开集，也没有仅由边界零测就推出边界逐点零值。

对于每个单元，原value与p_K在volume.restrict K下a.e.相等。代表f与value在S测度下a.e.相等，借已证volume.restrict K≤volume.restrict S准确转移到K；两个身份合成给f=p_K a.e.。非退化全维单纯形具有非空内部，真实凸性给K⊆closure(interior K)。因此两个连续函数在内部由开集正测度提升为逐点相等，再由稠密性扩到整个闭单元。原节点和共享面均被包含，不是对任意Lp代表进行点值求值。

任意完整空间成员先取得上述同一个全空间f，故一个实际空间顶点无论属于哪个单元都使用同一数值。frontier S不属于开S，因而所有边界节点值为0。FaceMatching保证已构造的局部节点插值在共享面相容；实际nodalFunction_unique用每个闭单元上的仿射身份及节点值准确再现f。结合nodalLp的a.e.身份和真实分区，Lp.ext最终给z=nodalLp f。没有把此反向表示写成新的前提，或通过改变原空间定义来使之自动成立。

空域仍合法：所有限制测度及L²类为零，a.e.结论和已有节点成员证明的空域分支处理该情形，没有擅自选域内点。非退化单元及d=0均按实际ambient拓扑／体积解释，相关内部稠密和连续提升定理仍适用。

## 原四类权和完整一致质量投影估计

最终投影是真实L²内积下对X=M.conformingSpace(dirichletSubspace S)的orthogonalProjectionOnto。X的有限维性来自完整有限分片仿射空间，因此X在L²中闭且实际投影存在；并未误用仅在H¹中闭、在L²中稠密的dirichletSubspace本身作为可投影闭空间。投影值的X成员资格由子类型property提供，新节点表示定理内部生成f及零边界节点值，然后直接清偿T056估计的全部表示前提。最终类型只量化任意u∈L²(S)，无需u在H¹、连续、具节点值或属于离散空间。

已直接复核所调用统一投影估计及其关键依赖：实际节点最小权由邻接单元正采样权的有限最小值构造；有效等级为θ=(γ+Γ_d)/2，而非直接套原网格γ。真实a.e.分片尺度身份给四类实际乘子及其倒数，倒数同时反转τ、η，逆尺度分支还反转ℓ以形成实际互逆乘子。节点平方加权测试是p_(ω²c)，其零边界节点使之通过已证H¹₀成员桥进入同一个完整X；未误认成点态ω(x)²p_c。

实际质量积分强制性给μ(d,θ)E≤(z,q)，真实正交投影关系给(z,q)=(u,q)。实际互逆乘子及L² Cauchy–Schwarz给右侧≤‖ζu‖‖ζ⁻¹q‖，两项真实加权范数平方估计为Z²≤θ⁴(d+2)E、T²≤θ²(d+2)E。标量消去单独处理E=0，再在E>0时合法消去，得

\[
\|\zeta\Pi_hu\|_{L^2}\le C\|\zeta u\|_{L^2},\qquad
C=\frac{\theta^3(d+2)}{\mu(d,\theta)},\quad
\mu(d,\theta)=1-\frac{(d+1)(\theta-1)^2}{4\theta}>0.
\]

θ<Γ_d保留正余量。没有隐藏节点数、最小网格尺寸、T或代表构造中的B因子；这个C甚至只依赖d、固定γ。δ由固定域上C¹ profile的真实Lipschitz界和正阈值构造供给，δ>0、δ≤1；δ、C都在全部网格、ℓ、TimeWeight、τ、t、η、inverseSize与u之前选择。hqmax≤δ通过q(t)≤qmax控制所有时刻。

实际ζ为q(t)^τ exp(ηρq(t))或其ℓ⁻¹倍，|η|=1；取(−τ,−η)得到整个乘子的倒数，因此涵盖原σ、σ⁻¹、ℓ⁻¹σ、ℓ⁻¹σ⁻¹。任意实τ的辅助结论蕴含原允许指数族上的统一结论，没有要求扩大数值主定理权族。权正性及倒数存在均由正q、正ℓ和指数函数内部清偿，分片面上的身份保持a.e.。

最终假设为开凸S、紧闭包及其所供的有限体积、固定C¹ profile、原1≤γ<Γ_d、真实有限单纯形分区、FaceMatching、BoundaryFitted、正ℓ、共享顶点尺度分级与hqmax小量。FaceMatching定义为单元交包含于共同顶点凸包，BoundaryFitted定义为单元边界部分由其边界顶点凸包覆盖，均是原贴合域边界的conforming网格所给几何内容。原双侧ℓ比值通过已证对称邻接引理供给最终全称单侧条件；原形状正则与ℓ≈diam是更强条件，本步无需再使用。原d=2、3、有界凸多面体和光滑profile是这些条件的特例。故本批完成原eq:p1-weighted-projection，而不单是有节点表示条件的弱化版本。

## 固定依赖、构建与公理

导入闭包含161个Carleman模块，157个旧模块与base逐字节一致，新增恰为本次四模块；Carleman.lean显式导入全部四模块。另对实际引用的C072 UniformNodalProjection闭包152模块、C073 DirichletZeroExtension闭包69模块、C064 ConformingLocalPolynomial闭包84模块，分别与其已验收版本 `14bdf0cb11fcc8ac2c51297c2307fb5745ee49b5`、`fbcd888532fe88caff4907495fad399fe6feeb55`、`2ccd0e5f1ae783f69c70d18593e09c79dfe7d7bd` 比较，全部逐字节不变。相关实际定义、证明及关键mathlib定理均已直接读取。

原稿、治理协议、工具链pin及CI工作流与base一致。原稿SHA256为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean pin为4.35.0，本机实际mathlib HEAD为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且其工作树干净；实际Lipschitz扩张、均值定理、mollifier a.e.收敛和连续函数a.e.身份提升均来自该pin。

10项实际展开类型已逐一核对，与固定C074/T058和交付JSON清单完全相同。CheckAxioms逐项 `#check @...` 和 `#print axioms ...`，再按privateToUserName遍历全部Carleman声明并递归collectAxioms，仅许可 `propext`、`Classical.choice`、`Quot.sound`。10项公理集合均恰为这三项；固定本地全部1346条显式公理输出也无其他公理，无sorryAx。

`/tmp/carleman-full-projection-full.log` 实际包含 `Build completed successfully (3629 jobs).` 及 `Axiom audit passed for all 4900 Carleman declarations.`。固定 `/tmp/carleman-full-projection-local-axioms.txt` 为 **1,394,394 bytes**，SHA256 **`6f65bda73c8f7d95d68f8ab0c48641ecab5d618d3b0205778db0fa63be265648`**。

已独立通过GitHub connector读取 [main CI 39165540866 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39165540866/attempts/1)：main/push、head SHA为固定 `9b4962ef9d03bb7bce6cc906a508857d57398c8c`，completed/success。state-check（117787590933）、lean（117787591085）、dashboard / snapshot（117788142688）三项jobs均completed/success；工具链准备、root构建、checked source记录、两份证据上传和同次快照生成步骤均success。同run的lean-ci-result artifact（12149714138）及lean-declaration-evidence artifact（12150675753）均绑定固定SHA。

已实际读取 `/tmp/carleman-full-projection-main-ci/result.json`：status PASS，`checked_sha=source_head_sha=9b4962ef9d03bb7bce6cc906a508857d57398c8c`，targets为Carleman，`finished_at=2026-10-18T20:57:32.190857+00:00`，ci_url与上述run/attempt完全一致。实际Lean 4.35.0提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib为上述pin。

原始远端 `/tmp/carleman-full-projection-main-axioms/axioms.txt` 与固定本机副本已独立逐字节比较，完全相同：**1,394,394 bytes**，SHA256 **`6f65bda73c8f7d95d68f8ab0c48641ecab5d618d3b0205778db0fa63be265648`**。另逐名复核远端10/10完整展开类型及每项正常基础公理集合，末行实际为 **`Axiom audit passed for all 4900 Carleman declarations.`**，无sorryAx或未批准数学公理。未混用其他提交、运行或后续工作区产物。

## 验收决定

**C074：PASS，可升级为REVIEWED，scope保持AUXILIARY。** 固定版本10项未发现需要修复的真实导数、代表、边界、节点身份、完整状态、四类权或统一常数量词缺陷；实际展开类型、递归公理和同SHA正式main CI均已独立核实。

本批清偿节点／边界表示缺口并完成原eq:p1-weighted-projection。完整Proposition 6.1仍需H²点值／插值、超逼近及其余义务；不能因此提升P011/P014/P015或其他完整原文结果，原文仍12/26。

本次仅写本报告，没有修改证明、台账、覆盖表、原稿或root导入，没有commit/push。
