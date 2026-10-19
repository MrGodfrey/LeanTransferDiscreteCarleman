# T102 / C118 独立本机验收

- `checked_sha`: `c749c4620eb0cba6f74a8a6ae58f6ce114645897`
- `base_commit`: `88306d8177aee83bfc8c6011f9d964a273e042b9`
- `reviewed_at`: `2026-10-19T03:06:45+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**；原 FD 对角测试的真实算子时间导数、端点及条件性周期身份，以及原统一 `eq:testtime`。完整空间超逼近、观察及 FD/P012 仍待，原文保持 **14/26**。

本验收直接读取固定提交三模块全部源码与证明、12 项实际完整展开类型、`governance/analysis/T102-fd-test-time.md` 和关键依赖，并对照原 `paper/main.tex` 的 `eq:qclass`、允许权定义、N4/`eq:testtime` 及 Appendix B Step 3。执行者说明和构建结果没有代替数学核查。后续工作树中的单纯形形状与乘子唯一性模块未混入本次范围。本验收自行查询同 SHA main CI，并自行下载、读取、逐字节比较同 run 两份原始产物。

## 全部 12 项声明

名称均省略公共前缀 `Carleman.`；源码位置相对于固定提交的 `Carleman/`。名单与交付 JSON、固定 C118 和 T102 台账一致。

| # | 声明 | 固定位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `finiteDiagonalOperatorFamily` | `Spatial/FiniteDiagonalOperator.lean:14` | PASS；从全部有限系数向量到连续线性算子空间的实际 CLM，目标具有真实算子范数。 |
| 2 | `finiteDiagonalOperatorFamily_apply` | `Spatial/FiniteDiagonalOperator.lean:20` | PASS；准确作用为 b_i f_i，没有转成其他测试或能量对象。 |
| 3 | `finiteDiagonalOperatorFamily_hasDerivWithinAt` | `Spatial/FiniteDiagonalOperator.lean:23` | PASS；有限 Pi 导数与真实 CLM 的 Fréchet 链式法则给算子值路径的 HasDerivWithinAt。 |
| 4 | `cartesianPhysicalInner_diagonal_bound` | `Spatial/FiniteDiagonalOperator.lean:30` | PASS；逐项绝对值及正物理质量给原配对界，不使用节点空间范数等价常数。 |
| 5 | `cartesianAllowedTestOperator` | `Spatial/CartesianTestTimeDerivative.lean:13` | PASS；原允许权在实际内部节点的平方构成真实连续对角算子路径。 |
| 6 | `cartesianAllowedTestDerivative` | `Spatial/CartesianTestTimeDerivative.lean:19` | PASS；实际候选导数系数为 2σ_i² 乘原对数时间导数，随后由第 8 项证明它确为导数。 |
| 7 | `cartesianAllowedTestOperator_apply` | `Spatial/CartesianTestTimeDerivative.lean:27` | PASS；逐状态严格等于 T101 的同一原 σ² 节点测试。 |
| 8 | `cartesianAllowedTestOperator_hasDerivWithinAt` | `Spatial/CartesianTestTimeDerivative.lean:33` | PASS；在真实闭时间区间上证明算子范数导数，含两个端点。 |
| 9 | `cartesianAllowedTestOperator_endpoint` | `Spatial/CartesianTestTimeDerivative.lean:43` | PASS；只使用原 q 的端点相等，得到算子端点严格相等。 |
| 10 | `cartesianAllowedTestDerivative_pairing_bound` | `Spatial/CartesianTestTimeDerivative.lean:51` | PASS；原真实时间导数及节点轮廓界给系数 2β(绝对幂值+R)q² 的原物理配对界。 |
| 11 | `cartesianAllowedTestOperator_periodic` | `Spatial/AllowedCartesianTestTime.lean:13` | PASS；以实际 q 的 Function.Periodic 为明确前提，保留同一周期，未从 TimeWeight 上下界虚构周期性。 |
| 12 | `allowed_weight_cartesian_test_time` | `Spatial/AllowedCartesianTestTime.lean:21` | PASS；紧闭包真实点值界及原全允许权质量比较内部供应，C 先于全部网格、周期、权、幂、符号、时刻和状态。 |

## 原命题与实际算子范数导数

原 N4 要求原 σ² 对角测试是可微算子族、具有匹配端点，且在原物理内积中满足 `|(f,T′_σ f)_X|≤C‖qσR_hf‖²`。原允许权为 `σ(t,x)=q(t)^τ exp(ηρ(x)q(t))`，τ 是固定实数且其绝对值不超过固定 τStar，η 为两种符号。原 q 的 C²、正下界、导数界和端点匹配供应本批需要的一阶时间数据。

第 1 项不只定义每个固定状态上的逐坐标乘法，而是定义从 `ι→ℝ` 到 `((ι→ℝ)→L[ℝ](ι→ℝ))` 的连续线性映射。内部算子由全部坐标投影和标量乘法构成；系数到算子的加法、齐次性逐坐标证明，再通过有限维定义域上的 `LinearMap.toContinuousLinearMap` 得到真正连续线性映射。

第 3 项先以 `hasDerivWithinAt_pi.mpr` 将每个坐标的导数装配成有限系数向量的真实导数，再调用这个 CLM 的 `hasFDerivAt.comp_hasDerivWithinAt`。结论的值域确是连续线性算子空间，其拓扑来自算子范数，因而不是仅对每个固定 f 的强逐点求导声明。辅助结论对任意有限 ι、任意时间子集 S 及其相对导数成立，空有限指标也没有额外非空假设。

实际形式化使用有限函数空间的标准范数及其连续算子范数，没有在该定义中重新安装物理内积诱导范数。对每个固定正网格，原物理内积给同一有限维空间上的一个正定范数，与该标准范数有相同拓扑，因此这一真实线性导数适用于原有限维算子路径；这里不需要任何网格统一的范数等价常数。尤其是后续定量估计并未通过此拓扑比较传递：所有数值不等式都直接在原物理配对中逐节点证明，未使用 `finiteDiagonalOperatorFamily` 的算子范数上界或节点数因子。报告不将代码中的标准范数实例误称为已经重装的物理 Hilbert 范数实例。

## 原 σ² 路径、真实导数与端点范围

已直接读取 `TimeWeightRegularity`、`TemporalDerivatives` 和 `AllowedWeight`。H 的 `derivative` 字段伴随对所有 t∈[0,T] 的真实 `HasDerivWithinAt q (derivative t)` 身份及原绝对导数界，绝不是只命名一个候选 q′。原 q≥1 保证正性和所有除法、实幂、对数求导合法。已有 `TimeWeightRegularity.ofContDiffOn` 用原闭区间 C² 假设供应该接口；本批不需要 q″ 或 q′ 的端点迹匹配，使用较弱的一阶数据覆盖原完整 q 类。

第 5 项真实系数是 `[q(t)^τ exp(ηρ(x_a)q(t))]²`。第 7 项为定义性相等，确认其作用就是 T101 已验收的原 `cartesianSquaredWeightTest`，没有换算子。已验收的物理自伴性、正定性和 `eq:test-norm` 因此仍针对同一测试，而非另一个具有相似估计的对象。

已有实际标量链式法则先给 σ′=σ[τq′/q+ηρ(x_a)q′]。新证明对该实际 σ 使用平方求导，然后通过第 3 项得到整个算子路径的导数；系数准确为

`2 σ(t,x_a)² [τ q′(t)/q(t) + ηρ(x_a)q′(t)]`。

τ、η、ρ 和节点位置在时间路径中均固定，故没有遗漏它们的导数；2、σ²、q 分母和指数符号都与真实平方路径一致。证明是在 `[0,g.period]` 上的真实 within 导数：内部给通常时间导数，两个端点给相应区间导数。g.period>0 保留真实非退化时间区间，不能把端点导数证书视为任意值。

端点相等和全局周期性由两个独立声明处理。第 9 项只需 H.endpoint，即 q(0)=q(T)，直接代入真实实幂和指数，给 T_σ(0)=T_σ(T)。第 11 项明确要求 `Function.Periodic w.q T` 后才断言完整实轴上的算子周期性。原周期延拓可以供应这个前提；仅有 TimeWeight 的上下界或 H 的端点相等并不会被误读为全局周期函数。本批也未从仅一阶端点值条件声称全局跨周期拼接处的导数相等。

## 原物理配对与内部点值界

实际 `cartesianPhysicalInner δ N f g` 定义为 `ω Σ_a f_a g_a`，其中 ω=∏δ_j，是原完整内部节点空间的物理配对。节点能量是同一 ω 乘全部 `(σ(x_a)f_a)²` 之和，已直接读取定义。第 4 项用 ω≥0、有限和绝对值不等式以及 `f_a(b_af_a)=b_af_a²`，将每项系数界乘非负 f_a² 后求和，准确给 `|(f,diag(b)f)_X|≤K E_σ(f)`。它没有通过不带质量的标准函数空间范数估计物理配对，没有吸收物理质量到 C，也没有损失节点基数。

第 10 项使用原 `|q′|≤βq²` 和 q≥1 得到 `|q′/q|≤βq²`，再由真实对数权导数界和 η 的绝对值为 1，得到 `|τq′/q+ηρ(x_a)q′|≤β(绝对幂值+R)q²`。乘以非负的 2σ_i² 后，正好满足第 4 项的系数前提。ρ 节点绝对值界在这一辅助接口明示，但最终第 12 项内部清偿，没有留下为主结论的新增网格条件。

最终定理固定原环境 S、紧闭包与真实 C¹ 轮廓后，从紧集上连续函数的有界性取得 R₀，并取 R=max(0,R₀)+1>0。每个原内部节点真正属于网格开域 Ω_g，经 hTS 落入 S⊆closure S，因此实际 `|ρ(x_a)|≤R`。这里没有将 SpatialProfile 的 a.e. 有界证书错误用于有限节点，也不要求选择节点避开某个空间零测集。原光滑闭域轮廓足以供应所需 C¹；没有域外光滑延拓前提。

全部 f 遍历原完整 `CartesianInteriorIndex N→ℝ`，不要求特殊支持、额外光滑性、非零状态或归一化。空内部索引、零状态以及空网格域的求和、配对均一致；最后仍能选正 C。对有限节点取值的对象是实际平滑轮廓及真实有限数据，不是任意 L² 等价类。

## 全允许权、真实 L² 右端及量词

已直接读取实际调用的 `allowed_weight_cartesianKuhn_stability`、Kuhn 闭单元权比较、`smooth_profile_lipschitz`、原有界乘子与子域限制定义。固定开凸 S 的真实闭域导数界内部给轮廓 Lipschitz 常数 L；实际闭单元距离≤dh 与 hq(t)≤1 给权比较因子 W=exp(Ld)。q^τ 在比值中精确抵消，所以该质量比较常数 C₀=W⁴(d+2) 本身不依赖 τ、q、周期、网格或状态。

质量比较使用的 σ 是 `((ρ.scaled η).multiplier w τ t).onSubdomain hTS`。`onSubdomain` 保留原实际 value 函数，只限制测度及可积性；其节点值恰为时间算子中使用的同一允许权。半范数按定义是实际有界乘子作用于原重构 L² 类后的 L² 范数，乘积的 MemLp 资格有真实证明。因此右端不是将节点能量重新命名为连续范数，也没有使用不可积积分或无穷 eLpNorm 的总化值。

类型明确在固定 d、S、轮廓、β>0、τStar≥0 之后先给 ∃C>0，然后量化所有 o、正 δ、N、网格域包含关系、h>0 和 δ_j≤h；其后才是全部 TimeWeight、TimeGrid、H、τ、η、t、原幂界、两符号、闭区间资格、hq(t)≤1 及全部 f。证明取 A=2β(τStar+R)>0，再取 C=A·C₀。该选择先于全部网格、h、周期 T、时间步数、qmax、时间权、幂、符号、时刻与状态；没有通过任一变化参数的有限维范数等价引入依赖。

最终实际不等式为 `|(f,T′_σ(t)f)_X|≤C q(t)² (σ.seminorm(R_hf))²`。q(t) 是固定时刻的正空间常数，故这就是原 `C‖qσR_hf‖²`；此解释不需要扩大允许幂族来调用额外估计。η 的绝对值等于 1 在实数中涵盖两种原符号，同一个 C 有效；τStar=0 的辅助退化范围也无问题，原 τStar>0 全部包含。原固定物理矩形取 Ω_g=S；原 hqmax≤1 和 q≤qmax 供应各时刻的 hq(t)≤1，没有额外时间步长限制。

## 依赖和范围边界

已读取 [T101 独立验收报告](T101-local-acceptance.md)，并直接核查本次使用的原测试、物理配对、允许权质量界、时间导数和乘子接口。三新模块 Carleman 导入闭包共 310 模块，307 个旧模块相对 base 全部不变。关键已验收版本亦逐闭包比较：

- `AllowedCartesianDiagonalTest` 的 306 模块闭包，与 T101 SHA `88306d8177aee83bfc8c6011f9d964a273e042b9` 逐字节相同。
- `AllowedCartesianKuhnStability` 的 252 模块闭包，与 C108 已验收 SHA `1c3da9ffc54b5624f27760db5368aa05cbdfc0a5` 逐字节相同。
- `TemporalDerivatives` 的 19 模块闭包，与已验收 SHA `a315bdc449c58a705a982f0d009f1dde24d6af66` 逐字节相同。

本批没有修改 T101 残差的方向：其 nodalProductResidual 仍是 σ²R_hf−R_hT_σf，与原 `eq:testsuper` 的残差相反。该既有接口事项不影响本批时间导数或物理配对；后续空间超逼近仍须显式处理符号。本报告不宣称原 Ptest 全部义务、观察或完整 FD 已完成。

root 明确导入三模块。已读 AGENTS、治理与 state 协议、原论文、Lean/mathlib pin 和两个 CI workflows 相对 base 均未变；原文 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean pin 为 4.35.0，本机 mathlib 实际 HEAD 为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且工作树干净。固定覆盖表为 14 个 PAPER/REVIEWED、总计 26 项，C118 的 AUXILIARY 范围及无新增额外前提记录与实际类型一致。

## 本机与同 SHA 远端证据

实际 `/tmp/carleman-fd-test-time-target.log` 为定向 **3501 jobs** 成功，`/tmp/carleman-fd-test-time-full.log` 为全库 **3809 jobs** 成功及 **6285** 声明递归公理审计通过。三新模块无 sorry、admit、新数学公理或 unsafe 证明。`tools/CheckAxioms.lean` 只添加本批 12 项 #check 与 #print axioms；原全 Carleman 声明环境的 `privateToUserName` / `collectAxioms` 递归检查未改。

固定本机产物的 12 项实际完整类型均逐名读取，各有恰一条类型及一条显式公理记录；全部仅依赖 `propext`、`Classical.choice`、`Quot.sound`。全产物实际 2104 条带公理记录、8 条无公理记录，合计 2112 条打印、2108 个不同声明名，没有白名单外公理。末行实际为 `Axiom audit passed for all 6285 Carleman declarations.`，递归环境计数未与显式打印数混淆。

已独立查询 [main CI run 39192583763 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39192583763/attempts/1)：event 为 push，branch 为 main，head SHA 精确为 `c749c4620eb0cba6f74a8a6ae58f6ce114645897`，run 最终 `completed/success`，updated_at 为 `2026-10-19T03:03:12Z`。三项 jobs 及各自步骤均最终成功：

| Job | ID | 最终状态与完成时间 |
|---|---|---|
| `state-check` | `117868404846` | `completed/success`，2026-10-19T03:00:27Z |
| `lean` | `117868404508` | `completed/success`，2026-10-19T03:03:00Z |
| `dashboard / snapshot` | `117869072647` | `completed/success`，2026-10-19T03:03:11Z |

同 run 的 `lean-ci-result`（ID `12159589994`）和 `lean-declaration-evidence`（ID `12161025129`）artifact 元数据均未过期，均绑定 main 与该固定 SHA。本验收已自行通过 `gh run download 39192583763` 下载两份原始 artifact。

实际读取 `/tmp/carleman-fd-test-time-main-ci/result.json`：status 为 PASS，checked_sha 与 source_head_sha 均精确为该固定 SHA，ci_url 对应上述 run/attempt，targets 为 Carleman，finished_at 为 `2026-10-19T03:02:02.471128+00:00`。实际 Linux Lean 4.35.0 commit 为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib commit 与固定 pin 相同。

远端 `/tmp/carleman-fd-test-time-main-axioms/axioms.txt` 与固定本机 `/tmp/carleman-fd-test-time-local-axioms.txt` 已独立逐字节比较，**完全相同**：**1,876,081 bytes**，SHA256 **`46c448b59813bfd47159daee68fbe0b1afe4974393fc26c062469f82d5916e50`**。另逐名重核远端 12 项类型、公理记录及末行 6285 递归审计，均通过。没有混入后续 `.ci/axioms.txt` 或其他 SHA 产物。

## 验收决定

**C118：PASS，可记录为 REVIEWED，scope 保持 AUXILIARY。** 固定 12 项未发现真实算子范数导数、σ² 时间路径、端点/周期前提、原物理配对、节点真实点值界、允许权或常数量词方面需要修复的缺陷。同 SHA 三项最终 CI 和自行下载的原始证据已独立核实。

本次通过仅清偿上述时间测试义务；原空间超逼近、观察与完整 FD/P012 不随本报告提升，原文保持 **14/26**。本 Agent 仅写此报告，未修改实现、台账、原稿或 root，未 commit/push。
