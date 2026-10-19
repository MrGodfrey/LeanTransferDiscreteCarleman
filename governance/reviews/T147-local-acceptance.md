# T147 / C163 独立本机验收

- checked_sha / source_sha：`e3a9cd6fa7134bdb9d924c56686a14d0bb64029d`。
- base_commit：`c598090a2e592f2e2a5441e5d05eaec994e9b1b3`。
- reviewed_at：`2026-10-19T09:58:11+00:00`。
- reviewer：独立本机 Agent `/root/accept_spatial_lemma`，未参与本批数学实现。
- result：**PASS**；axiom_check：**PASS**；12/12 项声明通过。
- scope：**AUXILIARY — 光滑面通量步骤**。C163 可在本固定版本登记为 REVIEWED；P024 / `prop:continuousCE` 不提升，原文完成数保持 **17/26**。

本报告从固定 Git 对象读取三模块全部定义和证明、原稿、T147 分析、MATH_SPEC、C163/T147 台账、关键依赖，并逐项读取实际 raw 中的完整展开类型与公理。独立查询正式 GitHub run/jobs/artifacts，自行下载同 run 的原始 result/axioms 后逐字节比对。执行者说明、既有依赖验收和 CI 本身均未替代本批数学核查。仅新增并单独提交本报告，不修改数学、台账、原稿或根导入，不 push；后续 T148 工作树与动态 `.ci/axioms.txt` 不属于本次证据。

## 原文对应与准确范围

原 `paper/main.tex:2696–2704` 先对光滑周期状态设置 `z=exp(L)u`，再要求同一真实空间通量在每个面上等于 `2q∂νφ(∂νz)²≤0`；随后还需 Green 积分、时间端点、系数估计、吸收、密度与时间反射。本批清偿实际有限严格半空间域的面几何、外法向和原 frontier 零值到上述光滑符号结论的衔接；不清偿整条原 Proposition A.3。固定原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，本批未改稿。

实际域为 `S={x | ∀i, bᵢ<ℓᵢx}`，ℓᵢ 是真实连续线性泛函，c 满足全部严格不等式并同时作为 Gaussian 中心。相对面内部点满足指定 j 等式及所有 i≠j 的严格不等式。新法向是同一 ℓⱼ 的 Riesz 向量的负向单位化；真实状态是输入全时空光滑 u，边值是对原 `frontier S` 的逐点零值，z 在结论内部定义为 `exp(L)u`。没有外给抽象法向、局部平面零值或目标通量符号。

闭面结论另要求一个真实相对内部见证 w，满足 ℓⱼw=bⱼ 和全部其它严格不等式。它对同一闭面上的任意 x（指定等式、其它弱不等式，包括棱角）证明指定面法向下的同一 V·n≤0。此见证并非任意重复/冗余半空间表示自动满足；本批明确保留该输入，不声称已经覆盖所有表示或所有多面体边界。C∞、经典边值、面见证是本辅助步骤的实际适用条件；相对于完整原 P024，这些光滑准备条件尚需后续清偿，不能由 AUXILIARY 验收转成 PAPER 完成。

## 全部 12 项声明

名单与 `/tmp/carleman-t147-halfspace-faces-declarations.json`、固定 C163/T147 台账逐项相同。位置为 checked_sha 下的 `Carleman/` 路径。三模块全部由固定 `Carleman.lean` 导入；各项均有固定 `tools/CheckAxioms.lean` 中的 `#check @...` 和 `#print axioms ...`，并实际出现于原始产物。

| # | 完整声明 | 固定源码位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `Carleman.finite_halfspace_mem_closure` | `Geometry/FiniteHalfspaceFaces.lean:14` | PASS；由同一严格内部点 c 和真实凸插值路径证明全部弱不等式点属于原严格交的真实闭包；本项实际不需要有限索引。 |
| 2 | `Carleman.finite_halfspace_closure_iff` | `Geometry/FiniteHalfspaceFaces.lean:35` | PASS；连续泛函的闭半空间给正向包含，前项给反向包含；严格内部点前提保留。 |
| 3 | `Carleman.finite_halfspace_face_neighborhood` | `Geometry/FiniteHalfspaceFaces.lean:44` | PASS；有限非活跃严格条件给真实开邻域，指定平面内的邻点属于原 frontier，而非另定义的边界。 |
| 4 | `Carleman.finite_halfspace_face_mem_closure` | `Geometry/FiniteHalfspaceFaces.lean:78` | PASS；以真实面内部见证 w 为终点的凸插值保持指定等式，使其它弱不等式严格化；实际不需要有限索引。 |
| 5 | `Carleman.halfspaceOutwardNormal` | `Geometry/HalfspaceOutwardNormal.lean:11` | PASS；实际定义 n=−‖L‖⁻¹Riesz(L)，符号对应域 Lx>b。 |
| 6 | `Carleman.halfspaceOutwardNormal_norm` | `Geometry/HalfspaceOutwardNormal.lean:14` | PASS；L≠0 下 Riesz 等距性与真实算子范数给 ‖n‖=1。 |
| 7 | `Carleman.halfspaceOutwardNormal_eval` | `Geometry/HalfspaceOutwardNormal.lean:21` | PASS；实际对偶恒等式为 L(v)=−‖L‖⟨v,n⟩，负号和范数因子准确。 |
| 8 | `Carleman.halfspaceOutwardNormal_plane` | `Geometry/HalfspaceOutwardNormal.lean:33` | PASS；L≠0 使真实线性平面核与 n 的正交核精确等价。 |
| 9 | `Carleman.halfspaceOutwardNormal_support` | `Geometry/HalfspaceOutwardNormal.lean:43` | PASS；Lx=b、Ly>b 内部给 ⟨y−x,n⟩≤0，方向确为外侧。 |
| 10 | `Carleman.pointwiseHeatFlux_contDiff` | `Spatial/HalfspaceHeatBoundary.lean:14` | PASS；原 V 全部五项由真实方向导数、乘积和有限和取得 C∞，未删去含 k/p 项。 |
| 11 | `Carleman.finite_halfspace_gaussian_heat_flux` | `Spatial/HalfspaceHeatBoundary.lean:27` | PASS；内部排除 ℓⱼ=0，构造单位外法向、支持条件及局部 z 零值，得到同一 V 的非正法向分量。 |
| 12 | `Carleman.finite_halfspace_closed_face_gaussian_heat_flux` | `Spatial/HalfspaceHeatBoundary.lean:58` | PASS；面见证给相对内部集合的真实闭包，固定 n 下真实 V 连续，闭集传递将非正性延伸至全部该闭面点。 |

## 数学证明、实际对象与前提

**闭包和面邻域。** `finite_halfspace_mem_closure` 使用真实连续路径 f(t)=(1−t)y+tc。对 0<t<1，每个约束的差为 `(1−t)(ℓᵢy−bᵢ)+t(ℓᵢc−bᵢ)>0`，因为第一项非负、第二项严格正；t=0 位于 Ioo(0,1) 的闭包，故 f(0)=y 位于 S 的闭包。不存在“闭包与无限交可交换”的未经证明步骤；这条共同插值路径使前两项可对任意索引成立。反向仅逐约束使用连续泛函给出的闭半空间包含。

面邻域证明明确使用 `[Fintype ι]`：把除 j 外的全部严格条件组成有限开交 U，x∈U 给实际 r>0 的球包含。若 y 在球内且 ℓⱼ(y−x)=0，则 ℓⱼy=bⱼ，其余条件仍严格。弱不等式和 c 给 y∈closure S；若 y∈interior S，则 y∈S，与指定等式矛盾。因此 y 属于真实 `frontier S`，并非把该约束平面直接当成边界。r 可依赖原约束、j、x；本批未声称全域统一面半径。

**Riesz 法向及退化情形。** `halfspaceOutwardNormal` 使用真实 Euclidean Hilbert 对偶同构的逆，向量范数等于连续泛函的算子范数。非零前提只在单位范数、精确对偶求值和核等价定理中使用；总定义即使 L=0 仍有 Lean 意义，但不会据此声称单位法向。最终相对面定理由 ℓⱼc>bⱼ 与 ℓⱼx=bⱼ 内部推出 ℓⱼ≠0，合法使用逆范数。对任意 y∈S，有 `0<ℓⱼ(y−x)=−‖ℓⱼ‖⟨y−x,n⟩`，因此 n 是实际外侧支持方向。不是输入一个恰好使通量有利的抽象 n。

允许其它冗余零泛函约束，只要它们与严格内部点相容；指定活跃零泛函则与前提矛盾。空索引集没有可选 j，d=0 时不存在相容的活跃非零泛函。本批没有除以零或虚构零维单位面。

**原边值到同一 z 的平面零值。** 新通量定理把上述真实面邻域代入原 `hboundary : ∀s, ∀y∈frontier S, u(s,y)=0`。经法向平面核等价，得到该真实局部平面上 `z(s,y)=exp(L(s,y))u(s,y)=0`，对全部时间成立。z 的全时空 C∞ 由同一 L、u 的 C∞ 内部供应。输入并未包含 z 的边界零值、切向导数零、时间导数零、支持条件或所求 V·n≤0。

已直接读取 `SmoothPlaneBoundary` 与 `PlaneHeatFlux` 的实际证明。局部平面上的零函数沿 x+sv 的真实邻域恒等性给切向导数零；任意方向减去其 n 分量后为切向，故真实空间导数等于 `(∂n z)nᵢ`。全时间的 z(s,x)=0 给真实时间导数零。随后处理的同一通量是

`Vᵢ=2z_tzᵢ+4(∇L·∇z)zᵢ−2|∇z|²Lᵢ−2pzzᵢ+2kz²Lᵢ`。

单位 n 给 ∑nᵢ²=1；前项由 z_t=0 消失，含 p、k 的两项由 z=0 消失；第二、第三项在法向相加为精确 `2D_nL(∂n z)²`。实际 `L(t,y)=q(t)ρ(y)` 以及真实 Gaussian 导数把它变为 `2q(t)∂nφ(∂n z)²`。中心 c 满足原全部严格半空间条件，因而支持方向给 ∂nφ≤0；l≥0、q(t)≥0 完成符号。未改换通量定义、漏掉五项之一或改变原系数 2。

相对面内部版本允许任意 k、p，不要求它们光滑；这是因为所用点态法向公式中的含 k、p 项实际消失，既未对它们求导也未假设其大小。它可用于原真实共轭 k、Ψ，同时不将这些特定系数的完整方程识别算作本批新增结论。

**闭面和棱角的连续延伸。** 对固定 j 和真实见证 w，路径 `(1−t)x+tw` 保持 ℓⱼ=bⱼ，其余约束在 t>0 时由 w 的严格性变为严格。故任何闭面 x 都属于集合 `Y={y | ℓⱼy=bⱼ ∧ ∀i≠j, bᵢ<ℓᵢy}` 的真实闭包，包括多个约束同时活跃的棱角。此处也不需要把无限交的闭包交换出去。

固定面的 n 只依赖 ℓⱼ，未随逼近点 y 改变。固定 t 后，F(y)=∑Vᵢ(t,y)nᵢ 是真实连续函数：`pointwiseHeatFlux_contDiff` 对 V 全部五项使用真实方向导数光滑性，时间切片、有限和与乘常数保持连续。相对面定理给 Y⊆{F≤0}；后者为真实闭集，`closure_minimal` 将非正性传到 x。没有假设边界迹连续，也没有将棱角处不同面的法向混成一个法向。结论针对每个有见证的指定面分别成立；闭面定理输出符号，单位法向性质仍来自前述同一个 Riesz 构造和非零性。

为采用这条连续性路线，闭面版本明确要求 L、u、k、p 全时空 C∞。这比仅点态内部面结论的 k/p 前提更强，但在本光滑准备范围内已明示；不能按此类型宣称原 C² 时间权及完整弱轨道已处理。它没有面测度、法向迹或 Green 公式，也无需以棱角零测替代棱角处的实际符号证明。

**见证与最终量词。** w 在闭面任意 x 之前给定，不要求每个角点自带相对内部邻域，也不要求逼近过程中存在统一半径。若半空间列表重复了同一面，可能不存在“其它约束全部严格”的 w；本批没有移除冗余约束或构造不可约表示，故该见证仍是待实际域实例供应的显式输入。原坐标盒的具体见证尚未由本批内部提供。所有状态、时间、选面和闭面点均按实际类型保留；没有有界域、网格或时间周期的新条件，但也没有由缺少这些条件推称已完成相应积分/周期步骤。

## 依赖版本与公理

三新模块的 `Carleman` import 递归闭包为 **95** 模块，其中 **92** 个旧模块与固定 base 逐文件相同。关键依赖完整 import 闭包另与其已验收版本比较：

| 依赖 | 已验收 declaration_version | 核查根及闭包规模 | 结果 |
|---|---|---|---|
| C159，真实半空间几何基础 | `90ca06c7cd42fae4b870fae9a67219fa729226f7` | `Geometry/FiniteHalfspaceCharts`，28 模块 | 全部内容相同。 |
| C162，真实局部平面及同一 V | `c598090a2e592f2e2a5441e5d05eaec994e9b1b3` | `Spatial/PlaneHeatFlux`，87 模块 | 全部内容相同。 |

固定独立报告 [T143](T143-local-acceptance.md)、[T146](T146-local-acceptance.md) 已读；对实际调用的边界导数、五项通量、Gaussian 支持符号另从固定源码核查。半空间图册依赖并未被用来假定 Green 或原弱法向迹；本批局部面与闭包论证直接来自真实线性不等式。

独立解析 raw 得 **2,741** 条显式公理打印记录：**2,732** 条仅依赖 `propext`、`Classical.choice`、`Quot.sound` 的子集，**9** 条无公理。12 项本批声明全部存在，未发现 `sorryAx` 或其它数学公理；三新源模块没有 `sorry`、`admit` 或新增 `axiom`。实际末行为 `Axiom audit passed for all 7453 Carleman declarations.`，递归审计包含生成辅助声明。

Lean 固定为 `4.35.0`，compiler commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；本机实际版本与远端一致。mathlib 固定 `56a005855ea17e0b0958f73ec801ae140b0a1679`，本机 checkout 同 SHA 且无修改。AGENTS、PROJECT_OPERATIONS、state/README、MILESTONES 及工具链文件的固定哈希与此前已读版本相同，适用原独立验收协议。

## 构建与实际同 SHA CI

固定 `/tmp/carleman-t147-halfspace-flux-target.log` 记录定向 **3,239 jobs** 成功；`/tmp/carleman-t147-halfspace-faces-build.log` 记录全库 **3,987 jobs** 成功；`/tmp/carleman-t147-halfspace-faces-axioms.log` 记录 **7,453** 项递归审计 PASS。这里核对的是固定既有日志，不声称重跑另一轮全库构建。

本人独立访问 [run 39233525574 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39233525574/attempts/1)：push/main、head SHA 精确等于 checked_sha，最终为 `completed/success`。曾实际看到 lean 运行、dashboard 排队，等待终态后才签发；三个 jobs 最终为：

| job | ID | 状态 | completed_at（UTC） |
|---|---|---|---|
| lean | `117996980417` | completed / success | `2026-10-19T09:57:23Z` |
| state-check | `117996980737` | completed / success | `2026-10-19T09:54:29Z` |
| dashboard / snapshot | `117998233690` | completed / success | `2026-10-19T09:57:35Z` |

实际 API 中两证据 artifact 均关联同 run/head SHA 且未过期；本人以 `gh run download` 分别成功下载：

| artifact | ID | API 压缩大小 | 独立下载位置 |
|---|---|---|---|
| lean-ci-result | `12178203680` | 493 bytes | `/tmp/carleman-t147-halfspace-faces-main-ci/result.json` |
| lean-declaration-evidence | `12177409217` | 212,581 bytes | `/tmp/carleman-t147-halfspace-faces-main-axioms/axioms.txt` |

实际 result 为 `PASS`、`checked_sha=source_head_sha=e3a9cd6fa7134bdb9d924c56686a14d0bb64029d`，target=`Carleman`，`finished_at=2026-10-19T09:56:20.994132+00:00`；文件 **537 bytes**，SHA256 **`1883bcdc0fee6a5442f2db6d3e34c264700a281dd475a3bc7cb063004289cf5e`**。远端原始 raw 与固定 `/tmp/carleman-t147-halfspace-faces-local-axioms.txt` 独立逐字节相同：均 **2,289,584 bytes**，SHA256 **`e747883038fe047997c952b18ea8512c2678d7032ae4255568297ceaebc1ed87`**。

API 压缩包 digest 分别为 result `sha256:e6183b0628dd4b8bb95830405e1505394fd8a9e2dd75bcefaaaffb601b407e58`、axioms `sha256:23baaad173e9d20b37258439ea201fedb3e31039a4083727260c5e0fad996356`。压缩包记录未与解压后原始文件 hash 混同。

## 签发结论

**T147 / C163：12/12 PASS，axiom_check PASS，未发现阻断性数学缺陷。** 真实有限半空间的闭包/局部面、Riesz 单位外法向、原 frontier 边值到同一五项 V 的符号、带明确面见证的闭面棱角连续延伸均已证明，可登记 REVIEWED / AUXILIARY。

冗余表示的面见证、真实面 Green 积分、原弱轨道与 C² 时间权衔接、系数估计/吸收及完整 CE 均不由本批完成；P024 不提升，原文保持 17/26。只单独提交本报告，不 push；通知主 Agent 后冻结上述 reviewed_at 和报告内容，不再修改。
