# T143 / C159 独立本机验收

- checked_sha / source_sha：`90ca06c7cd42fae4b870fae9a67219fa729226f7`
- base_commit：`13c8977bd4c50a11d6bed5fdab64b09aeee0203f`
- reviewed_at：`2026-10-19T09:22:51+00:00`
- reviewer：独立本机 Agent `/root/accept_spatial_foundations`，未参与本批实现。
- result：**PASS**；axiom_check：**PASS**；11/11 项声明通过。
- scope：**AUXILIARY**。C159 可登记 REVIEWED；本批不提升 P023 / `prop:analytic-realizations` 或 P024 / `prop:continuousCE`。固定台账原文覆盖为 **17/26**，本批不增加该数。

本报告从固定 Git 对象读取五新模块全部定义、完整证明，原稿、分析、MATH_SPEC、C159 台账及实际关键依赖，并逐项读取固定原始产物中的 11 项展开类型。数学判断独立于执行者说明和 CI。远端 run、三个 jobs 及 artifacts 均由本人独立查询，两个原始产物独立下载并与固定本地证据比较；工作树未来增量及动态 `.ci/axioms.txt` 均排除。按本轮授权，只新增并单独提交本报告，不改数学、台账、原稿或导入，不 push。

## 原稿对应和实际范围

原 `paper/main.tex:284–374` 的 A1–A3 要求原真实形式、算子域的完整 Sobolev 图估计、全部允许正/逆权的域保持、交换子和加权形式界；常数对 T 与权族统一。`paper/main.tex:647–661,863–879,964–977,1023–1036` 分别给出连续移位图估计、Euler 图估计、冻结系数图估计及完整时间误差。`paper/main.tex:2659–2664` 的 Corollary A.2 / `prop:analytic-realizations` 同时涵盖一般凸多面体和任意固定正维数的盒，不能以盒子情形替代整个命题。

本批在任意正边长坐标盒 S 上，使用同一个 `boundedDirichletOriginalForm`，其 V 是实际原 H¹₀ 测试闭包对应的 L² 子空间，形式是实际完整弱梯度 L² 内积，算子域是该闭形式的原变分域。`box_analytic_data_uniform` 内部提供 canonical H² 图估计与所有 `TimeWeight`、所有实数 `τStar` 的 AllowedFamily；`box_analytic_realization` 还从原 `SmoothOnClosure` 函数内部构造同值 profile。最终 `box_section3` 内部供应真实 Lipschitz 边界图册和 H² 正则性，再返回同一形式/算子的完整 `Section3.Conclusions` 及它所需要的全体 AllowedFamily。没有留下外部图册、H² 嵌入、图估计或加权形式估计的输入。

固定原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，本批未改稿。证明路线可以使用实际盒域奇延拓与内部正则性，但一般凸多面体正则性、P024 连续 Carleman 估计仍未由本批获得。

## 全部 11 项声明

清单与固定 C159 的 `lean_declarations`、`/tmp/carleman-t143-box-analytic-declarations.json` 完全一致。五模块均由固定 `Carleman.lean` 导入；每项都有固定 `tools/CheckAxioms.lean` 的 `#check @...` 与 `#print axioms ...`，且在独立下载的原始产物中实际出现。位置均指固定 SHA，路径前缀为 `Carleman/`。

| # | 完整声明 | 固定源码位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `Carleman.box_dirichlet_graph_estimate` | `Spatial/BoxAnalyticData.lean:15` | PASS；从原算子图取得同一 H¹₀ 弱解，真实 H² 提升以值唯一性识别 canonical jet，完整图范数由实际 Az 控制，Creg>0 先于所有 z。 |
| 2 | `Carleman.box_analytic_data_uniform` | `Spatial/BoxAnalyticData.lean:40` | PASS；实际 hD 内部供应；Creg、C、Ccomm 先于所有 w 和 τStar，同一原形式、算子及全部正/逆允许权。 |
| 3 | `Carleman.box_analytic_realization` | `Spatial/BoxAnalyticData.lean:61` | PASS；紧闭包与原光滑性给真正有界可测 profile，明确 ρ.value=f，没有修改原函数或增加有界代表前提。 |
| 4 | `Carleman.shearDirectionCoordinates` | `Geometry/DirectionalCoordinates.lean:13` | PASS；实际剪切/缩放公式及显式逆映射，s≠0，线性和双逆均直接证明。 |
| 5 | `Carleman.shearDirectionCoordinates_direction` | `Geometry/DirectionalCoordinates.lean:37` | PASS；同一变换严格将 (v,s) 送到 (0,1)。 |
| 6 | `Carleman.exists_directional_coordinates` | `Geometry/DirectionalCoordinates.lean:42` | PASS；非零 Euclidean 向量内部选非零坐标，真实 coordinateSplit 与剪切复合给可逆连续线性坐标。 |
| 7 | `Carleman.finite_linear_max_lipschitz` | `Geometry/FiniteHalfspaceCharts.lean:16` | PASS；非空有限组实际连续线性泛函之最大值，Lipschitz 常数由有限算子范数最大值证明。 |
| 8 | `Carleman.finite_halfspace_graph_charts` | `Geometry/FiniteHalfspaceCharts.lean:29` | PASS；有限严格半空间交与真实严格内点，全部活跃面同时给最大图函数，非活跃面在真实开邻域保持严格，覆盖任意边角。 |
| 9 | `Carleman.finite_halfspace_bounded_lipschitz` | `Geometry/FiniteHalfspaceCharts.lean:114` | PASS；实际开性、有界性和前项图册构成原局部 Lipschitz 域接口；有界性作为通用定理明确前提。 |
| 10 | `Carleman.openCoordinateBox_bounded_lipschitz` | `Geometry/BoxLipschitzDomain.lean:13` | PASS；每轴上下两条真实线性不等式与实际中点构造盒图册，外部有界性/图册/边界光滑前提均内部清偿。 |
| 11 | `Carleman.box_section3` | `Spatial/BoxAuxiliaryEstimates.lean:14` | PASS；同一原算子返回全 AllowedFamily 和完整 Conclusions，K、L₀、δ 先于全部时间网格、权、时间方向及状态；无外部正则性或图册输入。 |

## 数学审查

**原算子、canonical jet 与完整图范数。** 已读取 `DirichletForm`、`BoxDirichletRegularity`、`BoxPoissonRegularity`、`SobolevGraph` 的相关实际证明。原形式的闭性、L² 稠密性和对称性来自真实 H¹₀ 闭包；其强制性由 Poincaré 证明。`box_dirichlet_domain_le_h2` 通过 `dirichlet_operator_graph_iff` 对实际原算子域元素提取原 H¹₀ 弱解，再用已验收的实际盒上正则性给 H² 成员；不是将模型域重新定义为 H²。

新图估计先得到固定盒的 K≥0，再对任意 `z : a.model.domain` 使用其真实右端 `a.model.operator z`。正则性给 v，且 v 的一阶截断为该原弱解；由原弱解值等于 z 及 `domainSobolevJet_value`，开域弱导数唯一性给 `v=domainSobolevJet ... z`。因此被控制的是 canonical jet 的全部 0、1、2 阶实际 L² 字段，而非只控制值或某个替代解。`Creg=max(1,K)` 严格为正，并先于所有 z。这里的有限乘积图范数是实际完整 H² 范数的等价范数，未省略梯度/Hessian。

C157 的所用结论已从实际代码核对：对原 H¹₀ 弱解进行有限个真实上下盒面奇延拓，原闭盒严格进入固定扩大盒内部，原完整一阶 jet 限制恢复；再用实际内部 H² 定理提升，弱右端唯一性恢复同一个 f。纯 RHS 的完整图范数界还通过原弱方程与 Poincaré 控制值、梯度。因此本批 hD 与图估计没有将所需正则性重新当作未证输入。

**全部允许权、逆权与原 profile。** `DirichletAllowedData` 的真实结论在 w、τ、η 以及 hD 之前选 C、Ccomm；η 满足 |η|=1，空间反号与 τ→−τ 同时给逆权。其 `AllowedWeightData` 的字段是原 form/domain 保持、逆权 domain 保持、真实 σ² 测试的下界，以及原交换子对 canonical 低阶导数字段的界；没有把目标图估计或误差作为字段。`AllowedFamily` 还对所有 Bool 符号、|τ|≤τStar、全部时刻和全部 V 状态给加权形式上界，反权 V 保持由相反符号、相反指数的数据供应。

`box_analytic_data_uniform` 使用这一同一形式/算子的证明，并用实际盒 hD 实例化。常数 1/2、C≥1、Ccomm>0 的符号及非负放大步骤正确；Creg、C、Ccomm 均在所有 w、τStar 之前。空间乘法中的时间标量 q^τ 不引入未声明的空间导数因子。`box_analytic_realization` 用紧闭包上真实连续函数界，给 volume.restrict S 上 a.e. 可测、有界的 `SpatialProfile`，且值逐点等于给定 f。`SmoothOnClosure` 是原域内实际光滑函数及各实际导数的闭包连续延拓，未要求任意域外延拓光滑。原稿的负 profile 是这里更一般结论的特例，未增加符号限制或缩小允许权族。

**真实方向坐标与有限活跃面图册。** 剪切公式为 `(y,t)↦(y−(t/s)v,t/s)`，逆为 `(y,t)↦(y+tv,st)`；s≠0 保证真正双逆。对非零方向选实际非零坐标后，与真实坐标拆分复合，严格得到 e(v)=(0,1)。有限维自动连续性只用于这个固定几何线性同构；没有据此声称随网格、时间或状态统一的算子范数。图册允许连续线性等价坐标，旧 `LocalLipschitzCharts` 与实际圆柱局部图接口之间的转换已核查，既不要求正交，也不把剪切当成保体积换元。

在边界点 c，闭包最小性逐条给 bᵢ≤ℓᵢ(c)，开性给 c 不在 S，故实际活跃集 `{i | bᵢ=ℓᵢ(c)}` 非空。真实严格内点 x₀ 给 v=x₀−c≠0，且对全部活跃 i 有 ℓᵢ(v)>0。坐标分解 `x−c=e⁻¹(y,0)+tv` 将每条活跃不等式精确改写成 `−ℓᵢ(e⁻¹(y,0))/ℓᵢ(v)<t`；分母严格正，符号及不等式方向正确。于是有限最大值就是实际边界图函数，Lipschitz 界由这些真实线性泛函的有限范数最大值给出。

所有非活跃不等式在包含 c 的真实开集 U 内仍严格成立，取实际正半径物理球后得到局部集合双向等价。没有忽略额外活跃面，因此任意棱、角点均覆盖。旧局部图转换通过边界闭包及连续性证明图函数在 0 处为 0，再以 e⁻¹ 的真实范数缩小圆柱；这不是新增图册假设。一般半空间定理明确保留有界性，但盒实例用 ±坐标投影、阈值 lo/−hi 和真实中点清偿全部条件。任意正边长、平移及正维数均保留；一维盒使用零维水平坐标空间，未排除。原稿本就要求 d≥1，最终 `d+1` 参数化没有额外维数限制。

**Section 3 的量词和原完整状态。** `box_section3` 只在固定盒、profile、β>0、τStar≥0 后选常数。内部 hD、Creg、真实 bounded Lipschitz 资格均已供应，随后调用同一 `OriginalForm.section3`。返回的 `Conclusions` 虽在各字段保留原 AllowedFamily 参数，但同一结果的前半部分已经对每个 w 返回恰好该族，并非把待证条件留给调用者。

已展开 `Conclusions`、`EulerEstimate`、`ContinuousEstimate`、`TemporalEstimate`：K>0、L₀(B)≥1、0<δ≤1 先于任意 TimeGrid、任意周期、w、两个 `Orientation`、空间权符号、τ 和所有载荷/解。冻结系数还独立量化两种 cell extension。原连续图空间含实际 H 时间弱导数、a.e. 原算子域成员和周期 H 迹；Euler 覆盖所有 L² 节点载荷与全部原 D(A) 节点状态，均给存在唯一性及实际图范数估计。时间误差使用同一任意连续/离散解的真实差，保留 δt 的 L² 阶和 sqrt(δt) 的能量阶，相关可积性是结论，不是额外输入。原 |τ|≤τStar、时间权正则性及 δt·qmax²≤δ 的条件保留；因 δ≤1 且 qmax≥1，原 δt≤1 也受控制。没有 T 因子、谱截断或数据相关常数。形式上界允许依赖固定 L，强制性保留任意指定 B，与原文一致。

这些是 Section 3 的移位辅助估计；其中命名为 `ContinuousEstimate` 的接口不是 A4 的带观测 Carleman 估计。一般凸多面体 H² 与真正连续 CE 均不在本批完成范围。

## 固定依赖、公理和构建

五新模块的 `Carleman` import 递归闭包共 **366** 模块，其中 **361** 个旧模块与固定 base 逐文件相同。基线至 proof 的数学增量只有这五模块及根导入/公理检查登记，原稿无变化。关键已验收版本的完整 import 闭包另逐文件比对，全部相同：

| 依赖 | declaration_version | 本次比较根 / 模块数 | 结果 |
|---|---|---|---|
| C157 | `b818f314b275265490aa9b797779f7db0005ddb9` | `Spatial/BoxDirichletRegularity` / 224 | 全部相同 |
| C087 | `d65579460032f15bcba3c77709ccfd3f1642b8fc` | `Weights/DirichletAllowedData` / 227 | 全部相同 |
| C037 | `a315bdc449c58a705a982f0d009f1dde24d6af66` | `Section3/Complete` / 199 | 全部相同 |
| C037 | `a315bdc449c58a705a982f0d009f1dde24d6af66` | `Section3/OriginalWeights` / 201 | 全部相同 |
| C036 | `cfd7d038d322779b1e9bc1cdd076af65e0e829d1` | `Geometry/LocalLipschitzCharts` / 2 | 全部相同 |

Lean 固定 `leanprover/lean4:v4.35.0`，编译器 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；本机实际版本与远端 result 一致。mathlib 固定且本机实际为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，checkout 无修改。新增几何用现有真实有限维连续化、Finset 有限 supremum 和基本开集/线性代数结论，未引入额外数学公理。

固定 raw 中独立解析到 **2,629** 条显式公理记录，其中 **2,620** 条仅依赖正常基础公理子集，**9** 条无公理；所有依赖均在 `{propext, Classical.choice, Quot.sound}` 内，没有 `sorryAx` 或新公理。本批 11 项全部在 raw 中，末行实际为 `Axiom audit passed for all 7310 Carleman declarations.`，递归审计覆盖 **7,310** 声明。

实际读取的日志为 `/tmp/carleman-t143-box-analytic-target.log`（早期 `BoxAnalyticData` 定向 **3,576 jobs**）、`/tmp/carleman-t143-box-auxiliary-target.log`（最终 `BoxAuxiliaryEstimates` 定向 **3,580 jobs**）和 `/tmp/carleman-t143-box-analytic-full.log`（全库 **3,972 jobs**，随后 7,310 项公理审计通过）。任务消息提到的 `-build.log` 与 `-axioms.log` 在约定前缀下不存在；本报告依据实际存在的上述文件及 `-local-axioms.txt`，不虚称读取不存在的日志，也不声称另行重跑全库。

## 正式同 SHA 远端核验

本人独立查询的 [run 39229089450 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39229089450/attempts/1) 是 main 的 push，head SHA 精确为 `90ca06c7cd42fae4b870fae9a67219fa729226f7`；run 已 `completed/success`，更新于 `2026-10-19T09:22:30Z`。全部实际 jobs 最终为：

| job | ID | 结论 |
|---|---|---|
| lean | `117982425826` | completed / success |
| state-check | `117982426119` | completed / success |
| dashboard / snapshot | `117983919230` | completed / success |

本人分别通过 `gh run download` 独立下载该 run 的两个原始产物：

| artifact | ID | 独立本机位置 |
|---|---|---|
| lean-ci-result | `12176247146` | `/tmp/carleman-t143-box-analytic-main-ci/result.json` |
| lean-declaration-evidence | `12175947609` | `/tmp/carleman-t143-box-analytic-main-axioms/axioms.txt` |

实际 result 为 `status=PASS`，`checked_sha=source_head_sha=90ca06c7cd42fae4b870fae9a67219fa729226f7`，`finished_at=2026-10-19T09:21:18.895790+00:00`，target 为 `Carleman`。远端原始 axioms 与固定 `/tmp/carleman-t143-box-analytic-local-axioms.txt` 独立逐字节比较完全相同：均 **2,235,148 bytes**，SHA256 均为 **`cf8df18c5505c03754f5f85457e249b9ba50b770ed654766f054c7afb21fd02a`**。

## 签发

固定版本 T143/C159 的 11 项声明在数学对象、完整量词、真实依赖、公理及同 SHA 正式 CI 上均通过；可升级 REVIEWED / AUXILIARY。未发现阻断性缺陷。盒域解析数据和完整 Section 3 实例已清偿本批列出的内部义务；一般凸多面体正则性与连续 Carleman 估计不得据此提升。只提交本报告，通知主 Agent 后冻结报告内容与签发时间。
