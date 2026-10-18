# T066 / C082 独立本机验收

- `checked_sha`: `1f04be4f79db9d40ac1af37271eb8e9dc58639a3`
- `base_commit`: `9c354128a5ebd5e3eeb36f3e15e5fa9ae4a27158`
- `reviewed_at`: `2026-10-18T21:58:23+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：原Section 6 Step 3的完整P1空间投影测试超逼近 `eq:testsuper`，及其到既有 `Physical.GalerkinSuperapprox` 的接入。接口保留原 `hw` 蕴含，一般A2保持性未清偿；完整prop:p1仍需一般H² N3等义务，原文保持 **12/26**。

独立读取固定提交三模块的全部证明、六项实际展开类型及其所用真实对象和依赖，对照原 `paper/main.tex` 的N4、Section 6 Step 1–3、9.26-eq10/11/12及eq:testsuper。执行者说明与CI没有代替数学审查；后续工作区增量不属本报告。

## 全部六项声明

完整名称均以前缀 `Carleman.` 开始；顺序与交付JSON完全一致。

| # | 声明（省略 Carleman.） | 固定位置 | 独立数学核对 |
|---|---|---|---|
| 1 | `WeakSobolevJet.heat_weightedNorm_le_fields` | `Spatial/WeakProjectionResidual.lean:13` | PASS；实际m=1弱Sobolev平方范数身份及非负性给N≤q‖σu‖+‖σ∇u‖，未更换原范数。 |
| 2 | `projection_error_of_residual` | `Spatial/WeakProjectionResidual.lean:22` | PASS；真实L²正交投影线性且固定I∈X，从e=v−I得Πv−v=Πe−e，符号和空间一致。 |
| 3 | `weak_projected_residual_estimate` | `Spatial/WeakProjectionResidual.lean:33` | PASS；真实弱范数三角式、两项L²投影界和梯度逆界推出完整三项估计，系数CI Cp及1+Cp准确。 |
| 4 | `allowed_full_projected_superapproximation` | `Weights/FullProjectedSuperapproximation.lean:15` | PASS；在完整原V_h内部构造Πe的真实弱jet，组合两种倒数权投影／逆界／同一节点残差，得到实际Π(σ²u)−σ²u的原N估计及统一δ、C。 |
| 5 | `SpatialProfile.scaled_neg` | `Control/FullP1Superapproximation.lean:12` | PASS；任意实η下完整SpatialProfile结构相等，实际值和bound分别由−ηρ及\|−η\|=\|η\|核对。 |
| 6 | `full_p1_galerkin_superapproximation` | `Control/FullP1Superapproximation.lean:19` | PASS；实际F*F=Π(σ²·)、连续弱导数唯一性及原canonical jet把上一估计接入既有接口，保留其hw蕴含，无额外超逼近假设。 |

## 原弱范数和真实L²投影

`WeakSobolevJet`的所有一阶分量满足针对原完整紧支光滑测试的弱导数身份。`weightedNorm`是全部实际带权导数字段平方和的平方根；m=1时，已实际证明N_σ(u)²=q²‖σ value(u)‖²+‖σ field₁(u)‖²。新上界引理通过这个等式与两边非负性比较平方，得到N_σ(u)≤q‖σu‖+‖σ∇u‖。减法三角式来自真实加权字段到Hilbert乘积的线性映射，未使用与论文N无关的替代范数。

投影恒等式在实际L²(ν)中成立，X仅需闭子空间所对应的CompleteSpace，I必须真实属于X。代码使用正交投影线性、ΠI=I，准确得到Πv−v=Π(v−I)−(v−I)，没有反转目标误差。在最终应用中，X=M.conformingSpace(dirichletSubspace S)是完整分片仿射L²空间与真实H¹₀空间的交，不是预先挑选的节点表示像或受限状态集合。X的有限维性内部给出完备性和实际投影；未把在L²中稠密的H¹₀本身误作L²闭子空间。

T065为每个真实输入弱jet u（其value属于完整X）给同一个节点插值I∈X和真实弱H¹残差e，满足value(e)=σ² value(u)−I，同时具有原9.26-eq10、9.26-eq11两项估计。已复核其调用链：完整空间成员内部获得真实共享节点表示，节点乘积的零边界值给I∈X；实际全域残差的弱jet及值／梯度身份连接真实积分，三项平方估计对同一个I、e成立，最后按实际m=1范数取非负平方根。这里没有从三个各自存在的残差错误合并为同一残差。

新代码令pe=Π(value(e))。pe的子类型成员资格直接给pe∈X，再经X⊆dirichletSubspace取得弱jet p、其H¹₀闭包成员资格及value(p)=pe。因而逆估计适用于p的全部真实弱梯度。输入e只需真实弱H¹，未额外假设e∈H¹₀，也未使用一般权乘法保持性hw。最终p−e是同一弱jet线性空间内的真实差，其value精确等于Π(σ²u)−σ²u。

## 两种倒数权、逆界与小量合并

σ=(ρ.scaled η).multiplier(w,τ,t)实际等于q(t)^τ exp(ηρq(t))。ξ同时反转指数与符号，即(ρ.scaled(−η)).multiplier(w,−τ,t)=σ⁻¹，|−η|=1明确清偿。T058投影估计分别取inverseSize=false及true，给

\[
\|\xi\Pi e\|\le C_p\|\xi e\|,
\qquad \|\ell^{-1}\xi\Pi e\|\le C_p\|\ell^{-1}\xi e\|.
\]

inverseWeight是实际分片常数ℓ_K⁻¹乘子与ξ的乘积，单元重叠只以a.e.身份处理。这里第二项并非普通ξ投影界的重复，也未遗漏原逆尺度权。T050的真实加权逆估计取同一ξ及完整空间成员p，给‖ξ∇p‖≤C_I‖ℓ⁻¹ξp‖。它内部由每个真实局部仿射多项式、全部弱梯度识别、实际加权单元逆积分界和无重复的全网格求和得到，调用者不用提供节点表示或人为梯度字段。

将上述界代入真实范数三角式和第一条新引理，准确得到

\[
N_\xi(p-e)\le\|\xi\nabla e\|
+C_I C_p\|\ell^{-1}\xi e\|
+(1+C_p)q\|\xi e\|.
\]

泛型代数引理只需q≥0、C_I≥0；没有暗用未提供的C_p符号。具体应用的C_p、C_I、C_E均严格为正。T065给第一、第二残差项之和≤C_E hq_max N_σ(u)，故加权组合≤(1+C_I C_p)C_E hq_max N_σ(u)。零阶项原为q‖ξe‖≤C_E h²q_max²N_σ(u)，由0≤hq_max≤δ≤1得(hq_max)²≤hq_max。两项相加采用

\[
C=(2+C_p+C_I C_p)C_E>0,
\qquad
N_{\sigma^{-1}}\bigl(\Pi_h(\sigma^2u)-\sigma^2u\bigr)
\le Chq_{\max}N_\sigma(u).
\]

未除以h、q_max、N或状态范数，没有零状态例外，没有额外时间区间长度或节点数因子。hq(t)≤hq_max≤δ≤1也明确供给节点误差与逆估计的单元小量条件；没有将时刻q(t)当成q_max而漏掉一次比较。

## 原几何条件和常数量词

固定参数是d、开凸S及紧闭包、实际C² profile ρ、κ>0、c>0、B>0和1≤γ<Γ_d。δ、C先于有限网格索引类型、网格、a/r/ℓ、TimeWeight、τ、t、η及全部状态选择；最终wrapper还先于TimeGrid g选择。因此同一常数适用于所有时刻、所有时间区间、两种权符号和原允许指数族，不依赖T、节点数、网格最小尺度或状态。辅助结论对全部实τ成立，原有限允许指数族是其特例，没有扩大数值主定理的权前提。

δ沿用真实全空间投影定理的正阈值及δ≤1。该依赖使用有效等级θ=(γ+Γ_d)/2<Γ_d，C_p=θ³(d+2)/μ(d,θ)，μ=1−(d+1)(θ−1)²/(4θ)>0；没有把原网格等级γ直接当作实际权等级。真实共享顶点邻接与固定profile的Lipschitz界供给γ exp(2Lhq)≤θ，δ由固定L、γ、Γ_d预先选出。Γ_d=(√(d+2)+1)/(√(d+2)−1)与原文一致。

保留的网格假设为真实有限非退化单纯形分区、FaceMatching、BoundaryFitted、正内球半径与ball(a_K,r_K)⊆K、h_K≤κr_K、正ℓ_K、c h_K≤ℓ_K≤B h_K及共享顶点的ℓ_j≤γℓ_i。这些分别供应节点插值连续／零边界、形状正则、逆尺度残差和逆估计；原双侧ℓ比值由对称邻接准确转换为全称单侧不等式。类型中的有限测度由紧闭包的原有界域条件提供，不构成新增实质假设。

X覆盖完整原V_h的每个状态。空域／空索引在已有零L²和有限和分支中合法；d=0时正ℓ及ℓ≤B h_K不能容纳直径为0的非空单元，本结论未凭空构造这样的网格。证明不存在除以d或非零状态的步骤。

## canonical弱梯度与实际Galerkin接口

`galerkinWeightedTest`原定义为F*F，其中F是实际σ乘法与X到L²的包含复合。其已证实际作用公式为Π_X(σ.map(σ.map z))，等于Π_X((σ.mul σ).map z)，不是新定义的任意线性测试算子。`domainSobolevJet`是完整弱jet的value线性等价的逆，其value恰为给定V元素。

wrapper展开原 `GalerkinSuperapprox`，对任意t∈[0,g.period]、任意原hw及z∈X构造canonical输入u。hw的准确内容是∀v∈V，σ.map(v)∈V；它仅让两次真实σ乘法及目标误差v=R_h F*F z−σ²R_hz在原V中可写。新代码没有证明或假装清偿这一一般保持性。

上一主定理无需hw产生实际弱H¹ jet e，其value为同一投影误差。代码用 `WeakSobolevJet.value_injective` 证明e=domainSobolevJet(v)：在开S、支持于S的实际限制Lebesgue测度下，全部弱导数字段由零阶L²值唯一决定；该唯一性来自原全部空间测试的弱导数唯一性。两边value身份使用F*F实际作用公式和真实乘法组合，符号相同。因此不能选择一个有利但非canonical的梯度来减小N。`scaled_neg`同时识别实际逆权profile，最终不等式正是原接口的conformingWeightedNorm。

据此，实际完整V_h上的H¹量 `eq:testsuper` 已证明；接入既有GalerkinSuperapprox时仍保留该接口原有hw蕴含。不能从这个wrapper声称一般H¹₀权保持性A2、完整N4数值实例或完整prop:p1均已清偿。一般H² N3、连续Dirichlet正则性、A2/A3及连续Carleman等义务仍按原范围保留。

## 固定依赖、构建与公理

三模块的Carleman导入闭包共401模块，398旧模块与base不变，新增恰为本批三模块。另逐文件比较四个实际关键依赖闭包：GalerkinWeightedTest的285模块与C049已验收SHA `d999e5b3779aa82efee2da8e162b86148dc1f715`、ConformingAllowedInverse的92模块与C066 SHA `9ea552502177ccffb3f50593567578fc207c2568`、FullWeightedProjection的161模块与C074 SHA `9b4962ef9d03bb7bce6cc906a508857d57398c8c`、FullNodalSuperapproximation的185模块与C081 SHA `9c354128a5ebd5e3eeb36f3e15e5fa9ae4a27158` 均无变化。已直接读取本批实际调用和关键对象／证明。

原稿、已读取的治理协议、工具链pin和CI工作流保持一致。原稿SHA256为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean为4.35.0，本机mathlib实际HEAD为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且工作树干净。root显式导入三新模块；CheckAxioms逐项包含六声明的完整 `#check @...` 与 `#print axioms ...`。

六项实际展开类型已逐一核对，每项仅依赖 `propext`、`Classical.choice`、`Quot.sound`。固定本地全部1427条显式公理输出也仅含正常基础公理，无sorryAx。检查器按privateToUserName遍历全部Carleman声明并递归collectAxioms，不仅审查六个公开入口。

`/tmp/carleman-projected-superapprox-full.log` 实际包含 `Build completed successfully (3661 jobs).` 与 `Axiom audit passed for all 4987 Carleman declarations.`。固定 `/tmp/carleman-projected-superapprox-local-axioms.txt` 为 **1,483,921 bytes**，SHA256 **`d54d8aa662ea330ab6f4b604c59e8de04420ca7d9dc5b88bdb9c2c7c4d51d479`**。

已独立通过GitHub connector读取 [main CI 39169654262 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39169654262/attempts/1)：main/push，head SHA精确匹配固定版本，run为completed/success。lean（117799863532）、state-check（117799863782）、dashboard / snapshot（117801140389）三项jobs均completed/success；实际构建、checked source记录、两份证据上传及快照步骤均success。同run的lean-ci-result artifact（12152157082）与lean-declaration-evidence artifact（12152565474）均绑定固定SHA。

已实际读取 `/tmp/carleman-projected-superapprox-main-ci/result.json`：status PASS，`checked_sha=source_head_sha=1f04be4f79db9d40ac1af37271eb8e9dc58639a3`，targets为Carleman，`finished_at=2026-10-18T21:54:56.631897+00:00`，ci_url与上述run/attempt相同。实际Lean 4.35.0提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib为上述pin。

原始远端 `/tmp/carleman-projected-superapprox-main-axioms/axioms.txt` 与固定本机副本已独立逐字节比较，完全相同：**1,483,921 bytes**，SHA256 **`d54d8aa662ea330ab6f4b604c59e8de04420ca7d9dc5b88bdb9c2c7c4d51d479`**。另逐名复核远端六项完整展开类型及每项正常基础公理集合，全部1427条显式输出无其他公理，末行实际为 **`Axiom audit passed for all 4987 Carleman declarations.`**。无sorryAx，未混用其他版本或后续工作区产物。

## 验收决定

**C082：PASS，可升级为REVIEWED，scope保持AUXILIARY。** 六项未发现需要修复的真实投影、完整状态、弱梯度、逆权、尺度、常数量词或接口对应缺陷；实际展开类型、递归公理与同SHA正式main CI均已独立核实。

本批完成原eq:testsuper的实际H¹估计并按原hw蕴含接入既有接口。完整prop:p1的一般H² N3等仍待，不能提升P011/P014/P015或其他完整原文结果，原文仍12/26。本次仅写本报告，未修改证明、台账、原稿或root导入，未commit/push。
