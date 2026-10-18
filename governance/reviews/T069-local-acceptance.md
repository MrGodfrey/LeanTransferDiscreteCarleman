# T069 / C085 独立本机验收

- `checked_sha`: `d13e4bc8af28b91a2c2d65091a911baa174950c4`
- `base_commit`: `3eeba97f7b274bd8ffd473d2f57aad2b4e722845`
- `semantic_checked_at`: `2026-10-18T22:17:26+00:00`
- `reviewed_at`: `2026-10-18T22:20:27+00:00`
- `result`: **PASS**。
- `axiom_check`: **PASS**。
- 范围：**AUXILIARY**。真实 Dirichlet form-operator 在完整原域上的 m=1 允许权交换子界；结合 T067/T068 的能量空间和算子域保持，完成该模型的 A2。未完成 H² 椭圆正则、A3、一般 m 或整个 Appendix A；完整原文覆盖保持 12/26。

本报告直接读取固定提交三模块、全部 12 项完整类型及证明、实际相关依赖，并对照原 `paper/main.tex` A2/Appendix A 与 `governance/analysis/T069-dirichlet-commutator.md`。未以旧执行者报告、旧验收或 CI 成功替代数学核对；后续 WeakWeightedForm 等工作树增量不属于本次范围。

## 全部 12 项声明

名称均加前缀 `Carleman.`；源码位置相对于固定提交的 `Carleman/`。

| # | 声明 | 源码位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `derivativeComponent_weighted_norm_le` | `Spatial/LaplacianCorrectionBounds.lean:14` | PASS；真实加权 L² 坐标投影范数不超过完整 Euclidean 导数 fiber 范数。 |
| 2 | `WeakSobolevJet.heat_parameterNorm` | `Spatial/LaplacianCorrectionBounds.lean:25` | PASS；m=1 的真实参数范数精确等于 q‖σu‖+‖σ∇u‖。 |
| 3 | `smoothLaplacianCorrection_norm_le` | `Spatial/LaplacianCorrectionBounds.lean:34` | PASS；实际一、二阶相对系数界给修正项≤2dCq·parameterNorm，有限坐标和及系数 2 正确。 |
| 4 | `allowed_laplacian_correction_uniform` | `Spatial/LaplacianCorrectionBounds.lean:77` | PASS；固定 profile 内部供应一、二阶相对导数界，常数 2dB+1 先于所有允许权和状态。 |
| 5 | `dirichletDomainJet` | `Spatial/DirichletCommutatorIdentity.lean:13` | PASS；通过原域⊆真实 H¹₀⊆H¹ 的包含及实际 scalar/jet 等价取得 canonical H¹ jet。 |
| 6 | `dirichletDomainJet_value` | `Spatial/DirichletCommutatorIdentity.lean:19` | PASS；canonical jet 的 value 精确等于原域状态 z 的 L² 类。 |
| 7 | `dirichletDomainJet_graph` | `Spatial/DirichletCommutatorIdentity.lean:24` | PASS；完整原图刻画和弱导数唯一性证明该同一 canonical jet 属于 H¹₀，且负 Laplacian 为原 Az。 |
| 8 | `conformingWeight_operator_of_graph` | `Spatial/DirichletCommutatorIdentity.lean:35` | PASS；同一原子空间内由 scalar 相等识别域元素，转移实际算子作用，不更换或缩小域。 |
| 9 | `dirichlet_operator_mul_eq` | `Spatial/DirichletCommutatorIdentity.lean:46` | PASS；原算子的乘积公式 A(σz)=σAz−真实修正项。 |
| 10 | `dirichlet_conjugatedCommutator_eq` | `Spatial/DirichletCommutatorIdentity.lean:62` | PASS；真实 conjugatedCommutator 精确等于在 ξz 的 canonical jet 上的负修正项。 |
| 11 | `allowed_laplacian_correction_conjugated` | `Weights/DirichletCommutator.lean:13` | PASS；真实 v=σu 的 scalar 身份和弱乘积范数比较，给 C(q²‖v‖+q‖∇v‖)。 |
| 12 | `dirichlet_allowed_commutator_uniform` | `Weights/DirichletCommutator.lean:39` | PASS；σ、ξ=σ⁻¹ 的域资格和互逆身份全部内部供应，对任意原域 z 得实际 [A,σ]σ⁻¹z 的统一 m=1 界。 |

## 原文对应与范围

原 `paper/main.tex:354–361` 的 A2 要求全部允许权及其逆保持 V、D(A)，并给 `[A,σ]u=A(σu)−σAu` 与 `‖[A,σ]σ⁻¹z‖≤C∑_{j=0}^{2m−1}q^{2m−j}‖D^jz‖`。m=1 的右端恰为 `C(q²‖z‖+q‖∇z‖)`，本批最终声明保留这两个真实 L² 项及其幂次。

Appendix A `paper/main.tex:2615–2667` 的一般空间算子命题同时包含 A1/A2/A3；Dirichlet 推论还通过椭圆正则性识别 H² 域。此次只完成真实 Dirichlet 模型的 A2 交换子部分。T067 的实际允许权 H¹₀ 保持和 T068 的完整算子域保持已被本批按同一对象调用，合起来可登记该模型 m=1 A2 已清偿；不能据此登记完整 `prop:spatial-operators` 或 `prop:analytic-realizations` 完成。

此处 A 是纯梯度形式 `a(u,v)=⟨∇u,∇v⟩L²` 的真实关联算子，不是新增质量项或只对 H² 子域定义的替代算子。最终假设为正维 d、任意有界开集 S、固定原闭域光滑 profile。原凸多面体和盒域均包含在内；没有新增凸性、边界光滑性、谱限制、状态正则假设或网格条件。一般有界开集上的 form-domain 结论更广，但不把尚未证明的 H² 域等同写成事实。

## 原域、canonical H¹ jet 与弱图

已直接检查 `OriginalForm`：其数据是闭稠密 Sobolev 能量空间及有界对称强制形式，定义本身不包含 H² 椭圆正则。`boundedDirichletOriginalForm` 取真实 H¹₀ scalar 像和实际完整 L² 梯度内积，通过 Poincaré 给强制性。`model.domain` 是该形式的完整关联算子域，`operator_isAssociated` 及 `associated_iff` 在两个方向识别完整变分图；不是任意给定的子域。

`dirichletDomainJet` 调用 `domainSobolevJet` 时只使用 `OriginalForm.domain_le` 和 `dirichletSubspace_sobolev`，阶数明确为 1。虽然所导入文件还包含供别处使用的高阶图估计，引入该定义不要求也未调用任何 H² bound。scalar/弱 jet 等价源自开集上真实弱导数的唯一性，其 value 定理直接返回 z。

`dirichlet_operator_graph_iff` 已检查为：给定 L² 的 x/f，原域元素满足 scalar=x 且作用=f，当且仅当存在真实 H¹ jet u，value=x、u∈H¹₀，并对全部 SpatialTest 有 `⟨∇u,∇φ⟩=⟨f,φ⟩`。测试族是全部紧支 C∞ 测试，连续配对沿真实 H¹₀ 图闭包延伸到全部能量状态，因此图刻画覆盖整个原域。

新 `dirichletDomainJet_graph` 从此图得到一个 H¹₀ 弱解 jet，再以 scalar 相等及 `value_injective` 证明它等于 canonical jet。于是右端梯度确为原 z 的唯一完整 Euclidean 弱梯度，不能被任意选择的辅助梯度替代。没有通过 H² 强导数来定义它。

## 实际修正项与交换子符号

`smoothLaplacianCorrection` 的值是实际 L² 有限和 `Σᵢ[2(∂ᵢσ)(∂ᵢu)+(∂ᵢᵢσ)u]`。`intrinsicWordMultiplier [i]` 和 `[i,i]` 分别是真实坐标一阶、同方向二阶导数乘子；已核对 wordDerivative 的实际迭代 Fréchet/坐标定义及其 derivative 身份，不是自由系数。

既有 `WeakLaplacianProduct` 在真实测试 φ 上用弱坐标乘积法则，得到 `−Δ(σu)=σ(−Δu)−Σᵢ[2(∂ᵢσ)(∂ᵢu)+(∂ᵢᵢσ)u]`。乘积 jet 保持 H¹₀ 已经由真实弱乘积和测试闭包证明。把该弱图送入同一原关联算子图刻画，得到 σu 的域元素及算子值。

`conformingWeight_operator_of_graph` 仅用 Subtype.ext 将这个图中域元素与 conformingWeight σ z 识别；原 A、原 D 和乘积 L² 值始终相同。`dirichlet_operator_mul_eq` 因而是实际 A 的恒等式。展开真正的 `conjugatedCommutator` 得 `A(σ(ξz))−σA(ξz)`，两项 σA(ξz) 消去后恰为负修正项。符号与原 A=−Δ_D、原 `[A,σ]` 的次序一致。

通用恒等式允许任意域保持 ξ，因此那里并不需要互逆假设；最终入口再明确令 ξ 使用同一 profile 的 −η 和指数 −τ，并证明 `σ(x)ξ(x)=1`。这一区别没有导致把普通 ξ 当成 σ⁻¹ 的漏洞。

## 相对系数界、完整梯度和常数

坐标分量引理先利用真实乘子与 derivativeComponent 交换，再以完整 Euclidean fiber 的坐标范数收缩和 L² 范数单调性证明 `‖σ∂ᵢu‖≤‖σ∇u‖`，未偷换成不同的梯度范数。

若 `|∂ᵢσ|≤Bq|σ|`、`|∂ᵢᵢσ|≤Bq²|σ|`，实际乘子范数比较分别给 Bq‖σ∇u‖ 和 Bq²‖σu‖。每个坐标修正项用真实三角不等式及系数 2 控制为 `2Bq(q‖σu‖+‖σ∇u‖)`，d 项有限和给 `2dBq·parameterNorm`。m=1 parameterNorm 的精确展开使用 field 0 的真实 scalar 范数身份，不是把 square-sum N 范数错误展开成线性和。

`SmoothOnClosure` 已检查为 profile 在闭域连续、域内 C∞，各实际域内 Fréchet 导数有连续闭域延拓。它不要求域外光滑代表。S 有界使固定有限阶导数在紧闭包有界；实际指数链式法则给相对导数常数 B，在 q≥1、τ∈ℝ、|η|=1 和空间点之前选定。`allowed_laplacian_correction_uniform` 取 `2dB+1`，保证 d=0 的纯修正项辅助定理也有正常正数常量；最终原算子入口仍明确要求 d>0。

这里没有以固定 σ 的绝对 BoundedSmooth 常数替代统一相对导数界。前者仅保证真实导数乘子存在，允许随参数增长；最终估计使用的是来自固定 ρ 的相对界。两者已在调用链中区分。

## 共轭范数、倒数域资格与最终量词

`intrinsic_allowedWeight_parameterNorm_uniform (n:=1)` 通过实际弱 Leibniz 身份同时控制两个方向。新证明使用其反向比较：若 value(v)=σ.map(value(u))，则 `parameterNorm(q,σ,u)≤D·parameterNorm(q,1,v)`。D 同样先于 q、τ、η 和所有真实弱状态。结合修正项 Bq 界和精确 m=1 展开，得到 `BD(q²‖v‖+q‖∇v‖)`。没有额外假定目标交换子、图估计、插值或 H² 控制。

最终入口将 u 取为原域元素 ξz 的 canonical jet，将 v 取为 z 的 canonical jet。`allowed_weight_mem_dirichlet_domain` 分别用于 (τ,η) 和 (−τ,−η)，内部供应 σ、ξ 的全部原域保持资格；它们在最终类型中是 let 构造的证明，不是留给调用者的新前提。正 q、实指数负幂和指数互逆给逐点 σξ=1，实际 L² map_inverse 再给 value(v)=σ.map(value(u))。带入真实交换子恒等式并消去负号的范数，即得最终原式。

固定 d、S 和原 SmoothOnClosure profile 后，∃C>0 先于整个 TimeWeight、τ、t、η 和全部原域 z。常数不含 T、qmax、网格或状态。两符号以及所有实 τ 都覆盖原有限允许指数族；τ 只是固定时刻的空间常数，扩大其范围合法。省略 q 的周期性及时间导数条件是空间估计的加强，未声称时间算子结论。q≥1 由 TimeWeight.lower 提供，原 qclass 已蕴含。零状态无需额外处理或范数除法。

## 版本、构建与递归公理

三新模块的 Carleman 导入闭包共 86 个模块，其中 83 个既有模块相对 base 逐字节不变；root 明确导入三模块。AGENTS、流程规则、原论文、Lean/mathlib pin 和 CI 流程均未在该差异中改变。原论文 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

固定 `/tmp/carleman-dirichlet-commutator-full.log` 实际包含 `Build completed successfully (3671 jobs).`。固定 `/tmp/carleman-dirichlet-commutator-local-axioms.txt` 的 12 项完整类型逐项与固定源码核对一致；12 项递归公理仅有正常 `propext`、`Classical.choice`、`Quot.sound`。全部 1460 项不同显式打印声明的公理集合扫描也通过，末行确认所有 5131 个 Carleman 声明（含内部生成声明）递归审计通过。

公理审计程序本批仅增加 12 项显式打印；实际遍历所有 Carleman 声明、递归 collectAxioms 并拒绝白名单外项的代码未改，无 sorry 或额外数学公理。本机固定产物为 1,509,770 bytes，SHA256 `00febb2d246d290a6ba3aa5b5b6a401f66616780a2e13c4e596fab335eb40232`。Lean 4.35.0，mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`。

## 远端证据与签发状态

已独立读取真实 [main/push run 39171448579](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39171448579/attempts/1)，attempt 1，head SHA 精确匹配 checked SHA，顶层 completed/success。三个 jobs 均 completed/success：lean `117805180222`、state-check `117805180444`、dashboard / snapshot `117806019069`。Lean 上传证据和 post-cache 等收尾步骤也已全部 success，未在 job 仍运行时签发。

已独立核对同次 artifact 元数据：`lean-ci-result` id `12152528640`、`lean-declaration-evidence` id `12152593195` 均绑定该 run、main 和同一 head SHA。实际读取 `/tmp/carleman-dirichlet-commutator-main-ci/result.json`，status=PASS，checked_sha/source_head_sha 均为 `d13e4bc8af28b91a2c2d65091a911baa174950c4`，ci_url 精确对应该 run/attempt，finished_at=`2026-10-18T22:18:35.073799+00:00`，target 为 `Carleman`。Lean 4.35.0（commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）及 mathlib pin 均匹配。

实际读取 `/tmp/carleman-dirichlet-commutator-main-axioms/axioms.txt`，与固定本机产物逐字节完全相同：1,509,770 bytes，SHA256 `00febb2d246d290a6ba3aa5b5b6a401f66616780a2e13c4e596fab335eb40232`。远端产物再次核对 12 项实际完整类型及递归公理，并扫描全部 1460 项不同显式打印声明的公理集合，均只依赖正常基础公理；末行确认所有 5131 项递归审计通过。

最终结论：**T069 / C085 PASS，可将 C085 升为 REVIEWED，保留 AUXILIARY。** 12 项及所声称范围通过，未发现数学缺陷。结合 T067/T068 可确认该原 Dirichlet 模型 m=1 A2 已清偿，不能据此提升 A1/H²、A3、一般 m 或完整 Appendix A，原文计数保持 12/26。本 Agent 仅写本报告，未修改证明、台账、root 导入或原稿，未 commit/push。
