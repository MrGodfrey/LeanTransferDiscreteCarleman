# T065 / C081 独立本机验收

- `checked_sha`: `9c354128a5ebd5e3eeb36f3e15e5fa9ae4a27158`
- `base_commit`: `7d5b98f23e305b99c69543c953bb545fefc42cb7`
- `semantic_checked_at`: `2026-10-18T21:46:44+00:00`
- `reviewed_at`: `2026-10-18T21:48:29+00:00`
- `result`: **PASS**。
- `axiom_check`: **PASS**。
- 范围：**AUXILIARY**。原尺度下界导出的 ℓ⁻¹ 残差界、同一真实节点测试/弱残差的三项平方范数界，以及原 m=1 N 范数形式的 `9.26-eq10/11` 节点残差估计。未声称投影测试 `eq:testsuper`、残差 e 的 H¹₀ 成员资格或完整 `prop:p1`；完整原文覆盖保持 12/26。

本 Agent 直接读取固定提交五模块、全部 7 项完整类型及证明、实际调用依赖，并对照原 `paper/main.tex` 和 `governance/analysis/T065-scaled-nodal-norms.md`。旧执行者报告、旧验收和 CI 不替代语义检查。后续工作树中的投影残差/超逼近模块不纳入本次结论。

## 全部 7 项声明

名称均加前缀 `Carleman.`；源码位置相对于固定提交的 `Carleman/`。

| # | 声明 | 源码位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `inverseScale_diameter_four_bound` | `Spatial/ScaledResidualIntegral.lean:11` | PASS；c>0、ℓ>0、0≤k≤h、ck≤ℓ 推出 ℓ⁻²k⁴≤c⁻²h²，不除以 k 或 h。 |
| 2 | `SimplicialPartition.inverseWeight_residual_sq_sum` | `Spatial/ScaledResidualIntegral.lean:26` | PASS；真实 ℓ⁻¹ξ 乘子 seminorm 平方等于各单元 ℓ_K⁻²∫e²/σ² 的精确和，正确传递同一残差 a.e. 身份。 |
| 3 | `allowed_scaled_nodal_residual` | `Weights/ScaledNodalResidual.lean:12` | PASS；原局部值平方界乘尺度后精确求和，得到 C h²E，C 的尺度依赖仅由 c⁻² 引入。 |
| 4 | `allowed_full_nodal_scaled_norms` | `Weights/FullNodalScaledNorms.lean:13` | PASS；任意完整 V_h 状态内部产生同一 I/e，实际 Lp 差值身份和三平方界同时成立，统一常数 C₁+C₂。 |
| 5 | `WeakSobolevJet.heat_weightedNorm_sq` | `Spatial/HeatNormSquare.lean:10` | PASS；原 m=1 弱 Sobolev 范数准确等于 q²‖σu‖²+‖σ∇u‖²，没有引入替代范数。 |
| 6 | `nonneg_le_sqrt_mul_of_sq_le` | `Spatial/HeatNormSquare.lean:20` | PASS；非负 x、C、b 的平方界推出 x≤√C·b；零值情形保持，无除法。 |
| 7 | `allowed_full_nodal_superapproximation` | `Weights/FullNodalSuperapproximation.lean:14` | PASS；同一 I/e 得原梯度加尺度界 C h qmax N，以及 q‖ξe‖≤C h²qmax²N，常数 2√C 先于全部数值数据。 |

## 原文映射与结论范围

原 `paper/main.tex:1474–1485` 给正局部尺度 ℓ_K、下界 c h_K≤ℓ_K 和完整 V_h=H¹₀∩分片仿射空间；`paper/main.tex:1569–1593` 的 Step 3 对 e=σ²z_h−I_h(σ²z_h) 需要梯度、ℓ⁻¹ 值和零阶三项估计。对应的 `9.26-eq10` 是 `‖σ⁻¹∇e‖+‖ℓ⁻¹σ⁻¹e‖≤Chqmax Nσ(z_h)`；`9.26-eq11` 是 `q‖σ⁻¹e‖≤Ch²qmax² Nσ(z_h)`。本批在真实弱 H¹/L² 解释下给出这两个节点残差公式。

公共入口以 ∃I,e 表述；实际证明中的 I 明确选择 `nodalLp (σ²f)`，其中 f 是原完整状态内部构造的零边界节点代表，e 是同一节点残差的真实弱 jet。证明未选择任意替代近似，也未为三项估计分别更换 I/e。公共结论给 I∈完整 V_h 及 `value(e)=(σ.mul σ).map(value(u))−I`，尚未把 I 包装成一个独立命名的节点或投影测试算子。

I 的 H¹₀ 成员性由既有真实节点密度构造供应；e 此处只陈述为 WeakSobolevJet d 1，即真实 H¹。不能仅凭该类型或逐点边界行为把 e 当成已经登记 H¹₀ 的成员。原后续 Π_h e−e 的投影/逆估计组合、`eq:testsuper`、一般 H² 插值及完整 P1 命题仍待；这两条证明中间公式不增加 26 个具名结果的完成计数。

## 原尺度与真实 ℓ⁻¹ 范数

标量引理先由 ck≤ℓ 得 k/ℓ≤c⁻¹，再在非负条件下平方，并利用 k²≤h²：`ℓ⁻²k⁴=(k/ℓ)²k²≤c⁻²h²`。只除以原正数 c、ℓ；不要求正单元直径，不排除 h=0，不引入 h/h_K 之类的准均匀性比值。原尺度上界和相邻尺度比在该阶段未使用，省略它们是更强的辅助结论，而非隐藏额外条件。

已直接核对 `inverseScale`/`inverseWeight`：前者是各闭单元指示函数乘实际 ℓ_K⁻¹ 的有限和，后者再乘 ξ。a.e. 唯一单元性保证在 K 上等于 ℓ_K⁻¹ξ，零测共享边界不会进入积分或产生额外项。其构造时的有限和上界可以依赖网格，只用于保证真实乘子有界；最终估计并未使用该上界，因此不导致常数随单元数增长。

`inverseWeight_residual_sq_sum` 先使用既有真实 seminorm 平方积分与精确网格分解，再将全域 a.e. 残差身份通过 `cell_measure_le_domain` 限制到每个闭单元。ξ 由同一 profile 的 −η 和指数 −τ 构造，实际等于 σ⁻¹；`allowedSquaredWeight` 正是 σ²。因此平方后被积函数为 e²/σ²，尺度为 ℓ_K⁻²，负号、指数和倒数次序正确。原范数是实际 L² 乘子范数，不是自由定义的数值权范数。

新尺度估计逐单元乘 ℓ_K⁻²，使用原局部值误差 C₀ h_K⁴E_K，再乘上述标量尺度界和非负 E_K，得到 C₀c⁻²h²∑E_K。两种原状态加权平方密度的实际可积性已经调用；`integral_eq_sum_cells` 给 ∑E_K=E，没有单元数量因子，也未用未证明可积的积分默认值。所有闭单元/域测度切换均依赖真实内部包含及零测边界。

## 同一 I/e、原状态及实际弱梯度

`allowed_full_nodal_scaled_norms` 一次调用 `allowedSquaredWeight_full_weak_residual`，取出同一 f、e、节点测试成员性和两条残差积分界，然后把这个 e 的 value 送入新尺度估计。I 定义为同一个 f 上的 σ² 节点插值。使用 `nodalProductResidual_lp` 的 Lp.ext 和真实乘子 a.e. 身份，得到精确等价类差值；不是只在节点或某个代表上成立。

弱残差依赖已直接检查：零边界节点函数及其加权节点函数有真实全空间 Lipschitz 性和紧支撑；权只需在 closure S 上有界/Lipschitz，支撑外零值处理跨界情形，不附加权在边界外可微或有界的假设。`compactLipschitzSobolevJet` 和限制映射给真正弱导数；其 field 1 a.e. 等于实际 fderiv 的 Euclidean fiber。该成员性构造的 Lipschitz 界允许依赖状态、网格和权，但没有传入误差常数。

原 u 仅要求其 scalar 属于完整 `conformingSpace (dirichletSubspace S)`，没有新增节点 ansatz。内部节点表示和 `nodal_representation_weak_gradient` 把同一 u 的全体弱方向导数识别成节点函数实际梯度。因此新尺度估计的右端被精确换为 `E=q⁴(σ.seminorm(value u))²+q²(σ.seminorm(field 1 u))²`。零阶和梯度积分也通过真实正/倒数权平方范数身份变为实际 seminorm，三条界都作用于同一 e。

总常数选 C₁+C₂，选取发生在网格、权参数、尺度和状态之前。对零阶使用 h⁴E≥0、另外两项使用 h²E≥0，分别合法放大到同一常数；未改变三项的幂次。空域、空网格、零状态及 d=0 没有被额外排除。

## 原 N 范数与 qmax 幂次

原 `paper/main.tex:303–312` 定义 N² 为各阶 `q^(m−j)σD^j` 的 L² 范数平方和。项目的 `weightedSq` 正是完整弱 jet 的该有限和，`weightedNorm` 为其非负平方根。m=1 时 Fin 2 求和给 `(q·σ.seminorm(field 0 u))²+(σ.seminorm(field 1 u))²`；`weighted_zero_eq` 经真实空多重指标 fiber 的范数身份等于 scalar value 范数。因此新平方身份严格给原 N²=q²‖σu‖²+‖σ∇u‖²，并有 E=q²N²。

非负平方根引理使用平方单调性和 (√C)²=C，无除以范数或平方根。三个平方界依次开方为 `√C h²qN`、`√C hqN`、`√C hqN`。后两项相加得到 `2√C hqN`；第一项再乘外面的 q，得到 `√C h²q²N`。随后只在非负量上使用 q≤w.max 及 q²≤w.max²，恰好产生一次和二次 qmax 幂，再把第二式常数也放大到 2√C。

已检查 TimeWeight：lower 给 q(t)≥1，upper 给 q(t)≤max；max 只需是上界，与原 qclass 明说 qmax 可以仅为上界一致。新显式 hq 前提已由 TimeWeight.lower 蕴含，不增加限制。没有把局部条件 hq(t)≤1 强化成 hqmax≤1；原全时刻条件当然蕴含本批逐时刻条件。

## 量词、假设与统一性

固定 d、开凸 S、紧闭包、SpatialProfile ρ 的闭域 C² 值、形状 κ≥0 及原下界常数 c>0 后，先选 C>0，再量化任意有限索引类型、网格、FaceMatching/BoundaryFitted、整个 TimeWeight、τ/t/η、内球和局部尺度、任意完整状态。C 可以依赖这些固定空间/profile/形状/尺度下界资料，不能依赖网格、单元数、ℓ 的具体值、qmax、时间权、时刻、τ、η 或状态。最终 2√C 仍保持这个顺序。

所有 τ∈ℝ、|η|=1 均保留，因此覆盖原有限指数范围和两个允许指数权方向。省略 τ 范围、q 的周期性及时间导数条件仅因该结论是空间估计；结论对更大类 TimeWeight 成立，不代表已经构造了周期时间测试算子。常数先于整个 TimeWeight，故没有隐藏 T 依赖。

SpatialProfile 的本质有界/可测数据由原固定有界域上的光滑 profile 可供应；闭域 C² 比原光滑假设弱。有限测度实例由紧闭包保证。几何仍为真实满维单纯形分区、共有面及边界贴合、正内球和 diam(K)≤κr，局部 ℓ>0 与 c diam(K)≤ℓ 恰是原尺度下界。没有新增目标超逼近假设、准均匀性、状态范数下界或正直径要求。

## 固定版本、构建与公理

五新模块的 Carleman 导入闭包为 185 个模块，其中 180 个既有模块相对 base 逐字节不变；root 明确导入全部五模块。AGENTS、流程规则、原论文、Lean/mathlib pin 和 CI 流程在该差异中未改。原论文 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

固定 `/tmp/carleman-scaled-nodal-norms-full.log` 实际含 `Build completed successfully (3658 jobs).`。固定 `/tmp/carleman-scaled-nodal-norms-local-axioms.txt` 的 7 项完整类型与固定源码一致；7 项递归公理均仅为正常 `propext`、`Classical.choice`、`Quot.sound`。全部 1417 项不同显式打印声明的公理集合扫描也通过，末行确认全部 4981 个 Carleman 声明（含内部生成声明）的递归审计通过。

实际审计程序只增加这 7 项显式打印，遍历所有 Carleman 声明、递归 collectAxioms 并拒绝白名单外公理的逻辑未改，无 sorry 或额外数学公理。本机固定产物为 1,474,727 bytes，SHA256 `8a80935a08fc131baf3ff91a1f9947dc428f8b7abb4ce1082a4baf0a4a63226e`。Lean 4.35.0，mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`。

## 远端证据与签发状态

已独立读取真实 [main/push run 39169211832](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39169211832/attempts/1)，attempt 1，head SHA 精确匹配 checked SHA，顶层 completed/success。三个 jobs 均 completed/success：lean `117798567772`、state-check `117798567896`、dashboard / snapshot `117799208326`。

已独立核对同次 artifact 元数据：`lean-ci-result` id `12151877198`、`lean-declaration-evidence` id `12151897025` 均绑定该 run、main 和同一 head SHA。实际读取 `/tmp/carleman-scaled-nodal-norms-main-ci/result.json`，status=PASS，checked_sha/source_head_sha 均为 `9c354128a5ebd5e3eeb36f3e15e5fa9ae4a27158`，ci_url 精确对应该 run/attempt，finished_at=`2026-10-18T21:47:11.914135+00:00`，target 为 `Carleman`。Lean 4.35.0（commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）及 mathlib pin 均匹配。

实际读取 `/tmp/carleman-scaled-nodal-norms-main-axioms/axioms.txt`，与固定本机产物逐字节完全相同：1,474,727 bytes，SHA256 `8a80935a08fc131baf3ff91a1f9947dc428f8b7abb4ce1082a4baf0a4a63226e`。远端产物再次核对全部 7 项完整类型/递归公理，并扫描全部 1417 项不同显式打印声明的公理集合，均只依赖正常基础公理；末行确认全部 4981 项递归审计通过。

最终结论：**T065 / C081 PASS，可将 C081 升为 REVIEWED，保留 AUXILIARY。** 7 项和所声称范围通过，未发现数学缺陷。保留投影 `eq:testsuper`、e 的 H¹₀ 资格和完整 P1 命题未清偿的范围，原文计数 12/26 不变。本 Agent 仅写本报告，未修改证明、台账、root 导入或原稿，未 commit/push。
