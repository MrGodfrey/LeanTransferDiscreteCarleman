# T071 / C087 独立本机验收

- `checked_sha`: `d65579460032f15bcba3c77709ccfd3f1642b8fc`
- `base_commit`: `c5e99b4f0aa241a24dcf27262fced6bc147a60d8`
- `reviewed_at`: `2026-10-18T22:32:56+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：真实m=1 Dirichlet形式和原完整算子域的A2/A3结论接入既有AllowedWeightData、AllowedFamily。原域嵌入H²仍是显式剩余A1前提，未证明该嵌入、定量椭圆正则性或完整Appendix A；原文完整结果计数保持 **12/26**。

独立从固定提交导出源码，读取两新模块全部证明、三项完整展开类型、接口定义及实际调用依赖，并对照原 `paper/main.tex` A2、A3及Appendix A。数学判断依据真实证明与类型；执行者规格和CI未代替数学审查。后续工作区文件不属本次验收。

## 全部3项声明

完整名称均以前缀 `Carleman.` 开始；顺序与交付声明JSON一致。固定位置以 `Carleman/` 为根。

| # | 声明（省略 Carleman.） | 固定位置 | 独立数学核对 |
|---|---|---|---|
| 1 | `dirichlet_domain_lower_sum` | `Spatial/DirichletDomainOrders.lean:13` | PASS；实际H² jet截断为H¹，经value唯一性识别为原域canonical jet；零阶字段精确等距，Fin 2和等于q²‖z‖+q‖∇z‖，没有附加范数常数。 |
| 2 | `dirichlet_allowed_data_uniform` | `Weights/DirichletAllowedData.lean:16` | PASS；内部供应原接口全部五个字段，C=max(1,C0)、c=1/2、Ccomm>0先于hD及全部权参数；原算子、完整域和真实H¹₀均未更换。 |
| 3 | `dirichlet_allowed_family_uniform` | `Weights/DirichletAllowedData.lean:60` | PASS；同一常数同时覆盖signed两种profile、原有限指数族、真实倒数权及实际上界，τStar也在常数之后；没有假设A2/A3或目标结论。 |

## 原域、H²截断与原A2的阶数和

记D为 `(boundedDirichletOriginalForm hS hd hb).model.domain`。这是原Dirichlet梯度形式的完整变分算子域，由对所有H¹₀测试的关联条件定义；本批没有把它重新定义成H²∩H¹₀或某个正则核心。V仍是真实SpatialTest线性空间在H¹图范数中的闭包所实现的H¹₀空间。条件hS、hd、hb分别是开域、正维数和有界性，没有增加凸性或光滑边界假设。

第1项明确接收 `hD : D ≤ sobolevSubspace d 2 (volume.restrict S) S`。由hD取得实际H² jet J，其零阶值就是原L²状态z；truncate只截去二阶字段，保留零阶、一阶及所有相应弱测试恒等式。`WeakSobolevJet.value_injective`在开S和支持于S的限制测度上，从相同零阶L²值证明truncate J与原 `dirichletDomainJet` 相等。这一步以全部弱测试的导数唯一性保证梯度一致，不是任意选取一组较小导数字段。

`weighted_zero_eq BoundedMultiplier.one`给出‖field₀ J‖=‖z‖的精确身份；一阶字段通过上述jet等式和截断定义精确相等。展开Fin 2的两个指标，实际原A2右端因此为

\[
\sum_{k\in\mathrm{Fin}\,2}q^{2-k}\|D^kz\|_{L^2}
=q^2\|z\|_{L^2}+q\|D^1(\mathrm{dirichletDomainJet}(z))\|_{L^2}.
\]

恒等式对任意实q成立；后续使用原TimeWeight的q≥1。不需要H²范数受Az控制，不引入嵌入常数、维数范数等价系数或网格因素。hD仍是实质空间分析前提，不能因它仅以证明参数出现而视为已经证明。

## AllowedWeightData全部字段

已展开旧接口本身：它恰含form_preserving、domain_preserving、inverse_preserving、coercive、commutator五字段；并未把任何图范数、误差或观测目标放进定义。m实际为1，hV是既有真实H¹₀到H¹的嵌入，hD是上述全原域到H²的显式嵌入，a和A分别是原scalarForm与原model.operator。

form_preserving由已证明的真实允许权H¹₀保持供应，对全部v∈V、全部时刻成立。domain_preserving由实际弱负Laplacian乘积公式及完整变分图刻画供应，对全部z∈D成立，不要求z来自一个更小的H²核心。inverse_preserving将同一定理用于(−η,−τ)，并通过完整SpatialProfile身份 `ρ.scaled (-η) = (ρ.scaled η).neg` 识别为原倒数乘子；有界性字段的证明也作合法传输。这里的倒数是q^(−τ)exp(−ηqρ)，没有只反转一个符号。

coercive字段所需的右端是a(v,σ²v)：接口通过同一个form_preserving把σ连续作用两次，正是实际σ²乘法。既有真实形式下界给c=1/2及C0>0；本批取C=max(1,C0)，由于(q‖σv‖)²非负，把负余项系数从C0增大到C只会降低左端。证明中的sub_le_sub_left方向正确，所得仍为原未平移形式下界，而非换成某个新加权形式。

commutator字段展开后就是实际 `[A,σ]σ⁻¹z`。已读 `allowedCommutatorPath` 和 `conjugatedCommutator` 定义，前者仅将后者作用到常值原域路径；σ与σ⁻¹的真实乘积身份给A(z)−σA(σ⁻¹z)。本批调用先前对该真实算子的估计，再用第1项阶数身份替换右端。dependent domain资格只通过相同乘子身份和证明无关性传输，没有增加域保持、交换子界或其他目标假设。

同时直接复核其关键依赖：真实算子乘积公式含−Σᵢ(2DᵢσDᵢu+Dᵢ²σu)；实际wordDerivative的相对界给q、q²阶数；对u=σ⁻¹z使用完整弱乘积法则和真实逆乘法恒等式，将其加权H¹参数范数估为z的实际H¹参数范数。最终是Ccomm(q²‖z‖+q‖∇z‖)，不是以H²范数替代原低阶和。该依赖及本批均未使用待证H²正则估计。

## AllowedFamily、全部允许权与常数量词

实际展开类型的量词次序为：固定d、S、hS、hd、hb、ρ及原SmoothOnClosure后，先存在C、Ccomm且1≤C、0<Ccomm，再对所有hD、TimeWeight、τ、η量化；family定理还在同一存在量词之后量化任意τStar。因此常数独立于T、q及qmax、τ、t、η、状态和τStar，也不依赖hD的定量估计。它们允许依赖固定空间与profile导数界，符合原文统一性要求。未加入空间离散量或节点数。

原SmoothOnClosure是内禀闭包光滑接口：profile在closure S连续、域内真实C∞，每阶实际Fréchet导数具有闭包连续延拓。有界域紧闭包供应所需有限导数界；没有偷偷要求外部光滑延拓。指数乘子及其导数界均是实际q^τexp(ηqρ)的身份。参数|η|=1恰覆盖两种实符号，q≥1保证所有实指数有定义。

AllowedFamily只有data和upper两个字段。data将Bool的signed profile分别识别为ρ.scaled 1和ρ.scaled (−1)，调用上述全参数结论；它可以不使用|τ|≤τStar，因为上一步已对全部实τ成立。upper调用真实原梯度形式的Cauchy–Schwarz估计，其两侧恰是σ与σ⁻¹的实际conformingWeightedNorm，原常数为1；用C≥1及两范数非负放宽到接口要求的C，乘积括号和系数方向正确。

upper依赖中的梯度身份由canonical jet唯一性给出，σ与σ⁻¹在L²梯度配对中实际抵消；没有把CLM范数替代Euclidean梯度，也没有额外状态可积性假设。lower依赖展开真实a(v,σ²v)，由坐标乘积交叉项和Young不等式得到1/2主项及q²‖σv‖²余项，故两界使用相同原V和原a。

单个AllowedWeightData仅显式含σ对V的保持与σ、σ⁻¹对D的保持；原A2要求的逆权V保持由family在反号profile、反指数处的data供应。已核对旧 `AllowedFamily.inverse` 正是以!e、−τ和abs_neg实现这一点。因此两种符号和整个原有限允许指数族内的正、逆权都完整覆盖。任意τStar的类型包含原τStar>0情形；负τStar时范围为空，并未用该空情形替代原应用。

## 固定依赖、构建与公理

两模块Carleman导入闭包共227模块，其中225旧模块与base完全不变，新增恰为本批两模块。另对照已验收版本核查关键依赖闭包：C023 SobolevTruncation的30模块对 `e4b308fc21cd669906716aa9af53f1c2a263b1a7`，C037 AllowedFamily的196模块对 `a315bdc449c58a705a982f0d009f1dde24d6af66`，C085 DirichletCommutator的86模块对 `d13e4bc8af28b91a2c2d65091a911baa174950c4`，C086 DirichletAllowedForm的87模块对base，均无变化。关键旧接口、截断、域jet、真实交换子和形式估计的实际证明另已直接读取。

原稿、已读治理协议、工具链pin及CI工作流未被本批改变。原稿SHA256为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean为4.35.0，本机mathlib实际HEAD为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且工作树干净。root显式导入两新模块，CheckAxioms包括三项完整 `#check @...` 和 `#print axioms ...`。

三项实际展开类型逐项核对，均只依赖 `propext`、`Classical.choice`、`Quot.sound`。固定本机1477条显式公理记录也无其他公理，无sorryAx。检查器通过privateToUserName遍历所有Carleman声明并递归collectAxioms，不只审计本批公开入口。完整日志 `/tmp/carleman-dirichlet-data-full.log` 实际包含 `Build completed successfully (3676 jobs).` 和 `Axiom audit passed for all 5145 Carleman declarations.`。

已独立通过GitHub connector读取 [main CI 39172416462 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39172416462/attempts/1)：main/push、head SHA精确匹配固定版本，run为completed/success。lean（117808073967）、state-check（117808074120）、dashboard / snapshot（117808736931）三项jobs全部completed/success；工具链准备、实际构建、checked source记录、两份证据上传及同次快照步骤均success。同run的lean-ci-result artifact（12152069692）和lean-declaration-evidence artifact（12152812360）均绑定固定SHA。

已实际读取 `/tmp/carleman-dirichlet-data-main-ci/result.json`：status PASS，`checked_sha=source_head_sha=d65579460032f15bcba3c77709ccfd3f1642b8fc`，targets为Carleman，`finished_at=2026-10-18T22:30:55.963524+00:00`，ci_url与上述run/attempt一致。实际Lean 4.35.0提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib为上述pin。

原始远端 `/tmp/carleman-dirichlet-data-main-axioms/axioms.txt` 与固定 `/tmp/carleman-dirichlet-data-local-axioms.txt` 已独立逐字节比较，完全相同：**1,521,336 bytes**，SHA256 **`8c79409d504771bad68f9a7eee53bd2ae442a4867dc7df70341087dabe148cef`**。另逐名核对远端3/3完整展开类型及正常基础公理集合，1477条显式公理记录无其他公理；实际末行为 **`Axiom audit passed for all 5145 Carleman declarations.`**。无sorryAx，未混用其他SHA或后续工作区产物。

## 验收决定

**C087：PASS，可升级为REVIEWED，scope保持AUXILIARY。** 三项声明未发现原算子／域替换、弱导数字段不一致、逆权符号、形式估计方向、常数量词或循环目标假设方面需要修复的缺陷；同SHA正式main CI及原始公理证据均已独立核实。

本批在显式H²域嵌入前提下完成真实Dirichlet A2/A3的原接口组装。该hD、定量椭圆界、具体几何域的完整A1以及一般系数／高阶Appendix A仍需另证；本报告不提升原文命题、连续Carleman或数值误差结论，完整结果仍为12/26。本次只写本报告，没有修改数学代码、台账、原稿或root导入，没有commit/push。
