# 数学规格与桥接接口

依据 `paper/main.tex` / `paper/paper.pdf`（原 PDF 44 页，哈希见 `paper/SOURCE_MANIFEST.md`）。允许保留原始版本与清晰差异的论文修正、等价重述和证明路线调整，并同步本规格与覆盖映射；实质弱化最终结论或增加限制按 PROJECT_OPERATIONS 交用户决定。以下是实现规格与核对点，不是对全文数学正确性的重新审定。

## 原文目标

Theorem 2.1（`thm:main`，PDF p.10）保留 (A1)–(A4)、(N1)–(N5)、`eq:weightcoverage`、`eq:error-scales`、`eq:transfer-defects`、`eq:transfer-state-defect`。结论为 `eq:finalCE` 的载荷版本与由右逆推出的 `eq:rawCE` 残差版本。对所有允许的周期离散状态和两种方向成立，不能增添低频/频率截断或固定网格的限制。

固定结构数据及假设界以后，先选统一常数和阈值，再对所有允许的 T、h、δt、权函数与状态成立。统一性包括 T（TeX 330、387 行），不能为每个 T 任意另选常数；显式允许的参数依赖单独记录。

`X_h` 有限维；载荷空间 `𝔉_h` 仅要求原文范数空间条件，控制空间 `U_h` 不必有限维。`eq:massinterface`、`eq:transfer-compositions` 定义 R、J、Q=RJ、G=JR；不假定 Q 为投影或 G 为恒等。各映射独立于时间（pp.8–9，TeX 392–406）。

周期差分为 `D_+ zⁿ=(zⁿ-zⁿ⁻¹)/δt`，`D_- zⁿ=(zⁿ-zⁿ⁺¹)/δt`，伴随为 `D_+* = D_-`（p.10，TeX 495–500）。不能把 D_- 写成相反符号。共享模块统一 N>0、δt>0、T=Nδt、周期索引和加权 ℓ² 定义。

C001 共享接口位于 `Carleman/Periodic/TimeGrid.lean` 与 `SummationByParts.lean`：`TimeGrid` 存储 `N>0`、`δt>0`，`period=N*δt`，`Index=Fin N`，全部状态为 `Index → H`；`next/prev` 是互逆的模 N 移位。原文 TeX 477 使用 N≥2，本辅助恒等式对所有 N>0 成立。`dPlus/dMinus` 用实数逆的数乘表达向量除以 δt，`pairing=δt*∑ inner ℝ`。`pairing_dPlus/pairing_dMinus` 对任意实内积空间成立，因而包含原文的有限维实 X_h 及实 Hilbert 空间，无完备性或有限维限制。T001 当时仅建立时间步长加权配对；空间权 σ、相应加权范数与延拓已由 T002–T004 的后续共享模块接续。该辅助结果不清偿 B1–B5，不计 Section 5 或 Theorem 2.1 完成。

Corollary 2.2（`cor:general-scales`、`eq:scalerule`，p.11）中 α_x、α_t 的 minimum **略去分母为零的比值**。用非零条件筛选的有限集合或等价分支表达；不能沿用 Lean 实数除零等于零的默认值。Corollary 2.3（`cor:scales`）保留热算子参数与 4/5、2/5 指数。

## M2：有限、明确的桥接前提包

M2 连接真实空间、算子、权函数和范数，覆盖 Section 5 的 `eq:transfer-load` 至 `eq:transfer-absorption`（pp.19–20）。暂用前提逐项登记，后续证明后才消去：

| 接口 | 所需数学内容 | 后续来源 |
| --- | --- | --- |
| B1 冻结连续辅助解 | 对辅助载荷有满足周期端点的解 U，具备应用 (A4) 和误差估计的正规性，常数统一 | Lemma 3.4 `lem:frozen`；Lemma 3.1 `lem:graph` |
| B2 离散对应 | T002 已证明所选 transfer load 的存在唯一离散解就是 z：`existsUnique_auxiliary_dPlus/dMinus`；只用原文 R 单射、A_h 非负、μ_n>0、普通函数相容 JL=Γ 和状态方程；不假定 Γ 线性 | `Carleman/Transfer/Load.lean`；这不替代任意连续载荷的 B1 |
| B3 权与延拓比较 | 节点权、连续权、分片延拓和冻结移位的统一比较，足以连接真实载荷、状态、观测和误差范数 | Lemma 3.2 `lem:cell`、`eq:cellbounds`、`eq:cellwise-extension` |
| B4 权族误差估计 | 所需每个权的统一能量/L² 误差，ε_E=a_E+η_A+√δt、ε_0=a_0+a_E²+η_A+δt | Theorem 3.5 `thm:timeerror`、Lemma 4.1 `lem:spatialEuler`、Theorem 4.2 `thm:combined` |
| B5 统一吸收 | 比较与误差组合产生统一 C；先固定 C 再取 c_* 使 C c_*≤1/2，并推出两种残差版本 | Section 5 `eq:transfer-comparison`、`eq:transfer-absorption` 及共享实数吸收引理 |

B4 的能量权为正指数时 `q^((c_j-2(m-j))/2) θ`，否则 θ；L² 权包括 `q^(c0/2)θ`、`q^(o/2)θ`、`q^(2m)θ`，须由 `eq:weightcoverage` 覆盖。冻结移位和误差项不能另用未经匹配的抽象标量代替。

该表是需要逐项关闭的接口清单，不要求把 B5 整个结论直接当作假设。已在 M2 证明的接口从额外前提中移除；真正暂用的条款完整登记在 `extra_hypotheses`，写明量词/常数和预期消去目标。B2 可用等价证明架构，不机械复制原文唯一性步骤。单独实数吸收引理只算 AUXILIARY；直接假设最终离散估计不算 M2。

## 分层成果与模块复用

- 条件性 Section 5：`scope=CONDITIONAL`，逐项列出上述尚未证明的桥接条款；即使核对完成也不计入原文目标完成。
- 原始 Theorem 2.1：`scope=PAPER`，只保留原文前提，消去新增桥接前提；(A1)–(A4)、(N1)–(N5) 不属于额外前提。
- 具体应用：验证热方程/格式满足抽象前提。Proposition A.3 是应用层依赖，并非抽象 Theorem 2.1 要无条件证明 (A4)。

共享周期序列、加权范数、R/J/Q/G 和误差接口放在独立 Lean 模块；改变接口时同 PR 更新调用者与规格。首轮先完成书面规格、基础对象和小证明，完整主定理类型随接口建立逐步落实。

Section 3 保留 L² 的 δt 阶和能量 √δt 阶；Section 4 保留 a_E+η_A 与 a_0+a_E²+η_A。后续覆盖全部结果见 `PAPER_COVERAGE.md`；附录的证明位置映射到对应结果，避免重复计数。

## T002：重构代数与辅助载荷的实现边界

- `TimeGrid.map` 复用 mathlib `LinearMap.compLeft`；`dPlus_map/dMinus_map` 对任何实向量空间、任意节点状态成立，直接使用 T001 的 `TimeGrid/dPlus/dMinus`。
- `Reconstruction V X` 以 `V : Submodule ℝ H` 表示线性 conforming 子空间，`R : X →ₗ[ℝ] V`、`J : H →ₗ[ℝ] X` 及原文 `mass_adjoint` 为数据。`RH`、`QH` 仅显式加入 V→H 嵌入，保留 `Q=RJ : H→V`、`G=J(RH) : X→X`。V 的能量范数/拓扑未在此层声明，后续不得拿其 H 诱导范数冒充能量范数。
- `Reconstruction.ofLinearMap` 在原文有限维 X、Hilbert H 下，仅从 R 构造 mathlib 的实际有界伴随 J；`existsUnique_mass_adjoint` 证明原文质量伴随存在唯一。H 和 V 均未限有限维，未加入 R 正交性。一般代数接口保留较弱假设，构造入口负责提供其质量等式。
- `inner_G`、`G_symmetric/G_nonneg/G_positive`、`inner_QH`、`QH_symmetric/QH_nonneg`、`J_unique` 及组合等式由质量伴随推得。`G_positive` 单独使用 (N1) 的 R 单射；未假设 Q 投影、G 恒等，未加入有限维、完备或频率限制。
- `LoadInterface` 的 Γ、lift 和 right inverse 均为普通函数：TeX 392 仅称 load map，N2（TeX 437–443）只给出相容、右逆和范数界，未假定它们线性。本层不要求载荷类型具有代数结构；原文实范数载荷空间的假设留给分析层。`transferLoad` 是真实 H 值节点载荷 `L f + μ RH z`，μ 可逐节点变化。能量恒等式给出两种差分的非负配对，进而证明移位离散唯一性和选定载荷的 `∃! u_h, ...`，直接关闭 B2 的该用途。
- `extensionPlus/Minus` 用原有 Fin N 节点的整数转换及 ceil/floor 实现论文 `(t_{n-1},t_n]` / `[t_n,t_{n+1})`；单元取值与 0/T 端点已证明。
- `residualPlus/Minus_eq` 在 `D : Submodule ℝ H` 的域上取 `A : D →ₗ[ℝ] H`，对给定 H 值时间导数 `dU`，从冻结方程推出 `ε dU + A U = bar(L f) - bar(μ)(U-R bar(z))`。filter 版本保留几乎处处等式，未改成处处 PDE 假设。dU 与真实 Sobolev 弱导数的识别、连续解存在/正则性以及原文 μ=(Lq)^(2m) 的权族分析仍属 B1/B3/B4。当前 `U : ℝ→D(A)` 是代数用代表：B1 必须提供或转移几乎处处 D(A) 值代表，并保持真实 H 值 Sobolev 弱导数及端点迹；不能据此假设原 Sobolev 解每个时刻都属于 D(A)。

C002 是重构代数接口，C003 是上述载荷/残差消去及所选载荷的离散对应，二者均为 AUXILIARY。它们不等于完整 Section 5：T003 已完成并验收条件性 M2，B5 在该真实范数框架内关闭；B1/B3/B4 仍是原始定理的剩余义务，原文覆盖计数仍为 0/26。

## T003 的条件性接口与未清偿清单

`Carleman.conditional_transfer_uniform` 在 `TransferBridges` 前提下给出载荷与右逆残差两版。
先固定阶数/指数 `a` 和共同界 `K≥1`，再选
`C₀=2K+4K²+4K³`、`C=C₀(1+2(m+3)K⁴)`、`c_*=1/(2C)`；最终两版共用 `4CK`。
随后才量化任意 `TimeGrid`、时间权、重构/载荷/观测映射及所有状态。常数公式不含 T、δt、h、qmax、方向或状态。
这只证明条件性 Section 5，不给原始 Theorem 2.1 增加前提或标记原文完成。

### 真实对象与原文对应

- `TimeGrid.weightedSq p z = δt ∑ₙ(pₙ(zₙ))²`；`weightedNorm_sq` 证明平方根对应。
  `powerSq q b p z` 是同一有限和插入 `qₙ^b`，`powerSq_eq_weightedSq` 证明它恰为
  `qₙ^(b/2) • zₙ` 的加权平方范数，未引入替代能量标量。
- `timeSq` 是 `(0,T)` 上实际 Lebesgue/Bochner 积分 `∫q(t)^b p_t(u(t))²`。
  所有解释为 L² 范数的轨迹、误差、图范数项在桥接包中显式要求积分有限。
- `TransferGeometry` 的 state/load/control/space 是具有确定性的实半范数族，故逐时是真范数；
  observation/derivative/gradient 为允许核的半范数族。它们分别承载论文的离散加权范数、
  `‖θv‖_H`、`‖θv‖_{ω₀}`、`‖θ𝒟_jv‖`、`‖θD^kv‖`；`gradient_zero` 和
  `observation_le` 明确零阶/限制关系。T003 当时未构造 Ω 上的 Sobolev 空间、
  具体微分表达式或乘法算子 `exp(qρ)`；T004 已构造真实 L² 权乘法及区域观测，详见下节。
  Sobolev/微分表达式及整份桥接包的实例化仍是原始定理接入义务。此范数接口不以“名称”推断任何解析估计。
- `nodeEnergy` 正是 X 加权零阶项加上重构 R 后的各阶表达式；`loadSq`、`observationSq`
  使用实际 f、B* z。B* 为提供的线性观测映射，应用时取原文控制算子的伴随，不要求控制空间有限维。
- `frozenShift = (L qₙ)^(2m)`，连续延拓复用原来的 ceil/floor 两种半开单元。
  `error = domainValue(U) − R(z̄)` 取值 V；H 值代表与原始 U 几乎处处相等。

### 尚未证明的前提（完整有限包）

1. **B1 / `TransferBridges.solutions` 的存在部分**：每个方向、每个满足原状态方程的 (z,f)，
   对辅助载荷提供 `PeriodicWeakTrajectory` 和 frozen 方程。H 是完备实内积空间；value 和 derivative
   在 H 中属于 L²，value 在 `[0,T]` 连续，0/T 迹相等；对每个支撑紧含 `(0,T)` 的光滑实测试函数，
   `∫φ' U = −∫φ U'`，因此导数不是任意命名函数。仅要求 value 几乎处处属于 D(A)，
   并要求 A 作用于域代表后属于 H 值 L²。域代表在异常集填零；已证明其 H 值 a.e. 相等、L² 和弱导数转移。
   端点迹始终属于原连续 H 代表，**没有假设或声称其每个时刻在 D(A)**。
   `ComparisonBridge.frozen` 保持 a.e. 方程。存在与图估计待 Lemmas 3.1/3.4。
2. **B3 / `ComparisonBridge`**：节点 X 零阶范数到连续重构范数、逐 j 节点导数项到其实际分片延拓积分、
   延拓 lift 的载荷界、连续重构观测到 B* z 的界，以及这些项/连续解/误差/残差的加权积分有限性。
   `ErrorBridge.shift` 另列冻结 μ 的实际乘积误差到 `q^(2m)θe` 的界。
   T003 当时尚待从 N1/N2/N5 与 Lemma 3.2 导出共同 K；T004 已证明时间及移位部分并提供字段构造器，剩余空间实例详见下节；未把 `eq:transfer-comparison` 当作前提。
3. **B4-order / `ErrorBridge.order`**：对真实 e 和每个 j，`‖q^(c_j/2)θ𝒟_j e‖²`
   受相应完整 `graphSq` 控制。此处原文使用“阶数至多 j、系数有界”；实例化该微分表达式并由阶数证明此条仍待完成。
4. **B4 / `ErrorBridge.energy,l2,finite_energy,finite_l2`**：在已推导的辅助离散方程下，
   能量族取 `σ_j=q^(max(0,c_j−2(m−j))/2)θ`，L² 族逐一取
   `q^(c₀/2)θ`、`q^(o/2)θ`、`q^(2m)θ`，误差严格使用
   `ε_E=a_E+η_A+√δt` 与 `ε₀=a₀+a_E²+η_A+δt`。
   图范数为 k=0,…,m 的真实积分平方和。所有所用项要求有限。
   权覆盖定理已证明，并在这三个估计调用中传递覆盖证明；误差估计本身待 Theorem 4.2。

`ComparisonBridge.carleman` 是原文 (A4) 对所选真实弱解的实例；重构和 lift 的逐节点平方界、
右逆 ΓI=id 及其逐节点界来自原文 N1/N2，不是新的数学定理或未经证明的公理。
共同 K 必须在整个允许参数族上固定；目前未从 A1–A4/N1–N5 和 δ_x/δ_time/η_* 条件构造上述包，
也未证明这些阈值存在。这一构造是 M3/M4→原始 Theorem 2.1 的明确剩余义务。

### 已消去的桥接条款

- **B2**：`Orientation.state_solves_shifted` 直接重用已合并的双方向载荷等式，
  在 ErrorBridge 两种误差证明中实际供给辅助离散方程，不重复假设唯一性/状态对应。
- **B5**：`ComparisonBridge.comparison` 推出真实范数比较；`ErrorBridge.total_bound` 汇总准确权族；
  `LoadInterface.transferLoad_powerSq_le` 由 N1/N2、真实 μ 和同一 q 的节点值推导载荷与状态损失。
  `conditional_transfer_defect/load` 推出原文 Λ_f/Λ_z 及吸收，`TransferBridges.residual_estimate`
  使用普通函数右逆得到全状态残差版，`conditional_transfer_uniform` 证明常数先于所有时间网格选择。
  d_* 的最大值、b_*、负指数的 max{1,·}、Γ 的普通函数类型及两方向符号均未改变。

## T004：原文 Lemma 3.2 与具体 L² 单元比较

原稿未修改（`paper/main.tex` SHA256 仍为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`）。
C020 对应 Lemma 3.2 的完整候选声明；C021 是具体范数及 transfer 接口的辅助成果。原文计数仅在独立验收后更新。

### 权类、量词和全部单元结论

`TimeWeightRegularity w g β` 记录闭区间 `[0,T]` 内真实 `HasDerivWithinAt q q'`、
`|q'|≤βq²` 和 `q(0)=q(T)`。`ofContDiffOn` 从原文 `C²([0,T])` 的一阶导数界构造它；
原文 q_c≥1、q'' 界、首二阶导数端点匹配和 δt≤1 对本引理不是必需，未增加全实轴 C¹ 条件。
给定原文的周期延拓时，`CellEstimates.global_cell_bounds` 使用 `Function.Periodic q T`
将结论搬到所有实数时间。此周期性来自原文的延拓约定，不能从只有端点相等的任意 TimeWeight 擅自推断。
`Orientation.extension_periodic` 已证明任意节点序列的 ceil/floor 延拓在整条实轴上周期。

固定 m≥1、β>0、τ_*≥0 和空间界 R≥0，先选
`δ=1/(1+2β+4β(τ_*+R))`，再选
`C=max 3 (max (2β) (max (8β(τ_*+R)) (max (32β(τ_*+R)) (2(2m)2^(2m−1)β))))`。
`cell_estimates_uniform` 随后才量化任意 q、T=Nδt、N>0、δt 和相应正则性数据。
`CellEstimates` 包含：

1. 任意两个相距至多 δt 的闭区间时间点之间 q 和 σ 的双向比较，因而覆盖每个单元的两个端点；
2. 两种实际冻结延拓的 q 相对误差 `Cδt q_n` 和 σ 相对误差 `Cδt q_n²`；
3. 对所有 L≥1，实际 `bar μ` 与 `(Lq(t))^(2m)` 的差为 `CL^(2m)δt q(t)^(2m+1)`；
4. 原方向 `H_n=(σ_n/σ_(n−1)−1)/δt` 的点态界及 `weight_quotient_essSup` 的真正 essential-supremum 界；
5. 所有循环节点（包括末节点到 0）的 `|μ_(n+1)−μ_n|≤CL^(2m)δt q_n^(2m+1)`。

`allowedWeight τ r t=q(t)^τ exp(r q(t))`；取 r=ρ(x) 和 r=−ρ(x) 分别覆盖 θ 与 θ⁻¹。
`SpatialProfile.neg` 使用相同 R，`multiplier_neg_value` 明确给出 θ⁻¹，而不是默认 σ 只有一种符号。
C 和 δ 不依赖 T、L、qmax、网格、方向或状态；空间依赖仅通过固定的 R，指数依赖是固定结构数据。

### 实际空间、时间和节点范数

- `BoundedMultiplier.map` 作用于 mathlib 的 a.e. 等价类 `Lp E 2 ν`，证明乘法后 MemLp、线性和范数界；
  从不宣称任意代表的逐点等式。`seminorm_sq_integral` 是实际 `∫|σ|²‖u‖²`；密度可积已证明。
  ρ 有界可测构造 `SpatialProfile.multiplier`；空间正权 a.e. 非零给出确定性。
  原文光滑有界空间 profile 可使用其有界可测数据；Sobolev 微分算子本身没有因此自动构造。
- `observation_sq_integral` 在同一 L² 空间中用区域 indicator 实现 `∫_ω |σ|²‖u‖²`，
  并证明观测半范数 ≤ 全空间范数。它不把观测换成不相关的标量。
- `integral_extensionPlus/Minus` 对现有 ceil/floor 延拓证明精确 `∫_0^T bar f=δt∑f_n`，
  正向末单元使用周期重编号；`integrable_frozen_density` 和 `timeSq_frozen_eq_powerSq` 同时证明有限性及冻结平方范数恒等式。
- `powerSq_timeSq_comparison` 在实际时间积分与节点有限和之间给出双向平方常数 9，并从可测性、
  单元比较和冻结密度有限性推出连续侧有限性；不再把这项可积性当作假设。
  只要求空间测度 SFinite（覆盖原文 Lebesgue 限制测度），不要求状态低频或控制空间有限维。

### 指数对应与接回 B3

平方密度 `q^a ‖q^τ θ u‖²` 精确等于 `‖q^(τ+a/2)θu‖²`。
原文能量使用 a=c₀,c_j，观测使用 a=o，lift 使用 a=0；冻结移位损失 a=4m。
图范数中的 a=`2(m−k)+b`（b 为已有能量族指数）也沿同一公式。
原文 `eq:weightcoverage` 用于 B4 的权族仍保持 T003 的 d_*/2、c₀/2、o/2、2m，未改动。

**这里不要求原文 τ_* 额外覆盖 c_j/2 或全部图范数指数。**
`powerSq_timeSq_uniform_bounded_exponents` 对固定 |τ|≤τ_*、|a|≤A 先取单元分析阈值
`cellThreshold β (τ_*+A/2) R`，随后量化全部 T/q/网格/方向/状态。
A 可在有限的上述指数集合上先取共同上界。扩大的是本单元计算的固定指数界，
不是 (N1)–(N5) 或局部化假设必须成立的权族；不暗中强化原文 `eq:weightcoverage`。

`Transfer/ConcreteNorms.lean` 直接给出原 `ComparisonBridge` 四种字段的构造：

| 声明 | 仍需提供的真实空间数据 | 推出的字段 |
| --- | --- | --- |
| `node_derivative_of_L2` | 具体线性场 J 与 p.derivative 的 L² 等式 | `node_derivative`（9）及 `finite_reconstructionD` |
| `node_state_of_L2` | 空间范数实例、N1 型逐节点重构下界 C | `node_state`（9C） |
| `lifted_load_of_L2` | 空间范数实例、N2 型逐节点 lift 界 C | `lifted_load`（9C），lift 仍为普通函数 |
| `observed_reconstruction_of_L2` | 观测场（可取区域截断）、N5 型逐节点观测界 C | `observed_reconstruction`（9C） |

`powerSq_timeSq_comparison_comp` 同时提供这些线性场的时间有限性；普通载荷先取真实序列 `lift(f_n)` 即可。
`frozenShift_timeSq_le` 对实际 `frozenShift=(Lq_n)^(2m)` 证明
`‖bar μ u‖²_(time,σ) ≤ (2L)^(4m) ‖q^(2m)σu‖²_(time)`，并从右侧有限性推出左侧有限性。
该常数只含先固定的 m,L，供共同 K 吸收；从而该实例的 `ErrorBridge.shift` 无须重复假设。

### 阶段后的未清偿边界

- B1：周期连续辅助解的存在、真实 H 值弱导数/图估计仍待 Lemmas 3.1/3.4；本阶段未把 a.e. D(A) 正规性加强为每时刻 D(A)。
- B2：保持已合并证明与实际调用；不重复假设。
- B3：时间单元、空间权乘法、真实观测截断和冻结移位上述部分已证明。对于任意抽象 TransferGeometry，
  仍必须给出实际空间/Sobolev 场、p.space/p.derivative/p.observation 的等式以及原文数值空间比较。
  未自动给所有抽象半范数族填充 ComparisonBridge，也未构造整份 TransferBridges。
- B4：连续/离散正则性、时间与空间误差估计及微分表达式的阶数界仍未证明；连续解/误差的所需加权有限性仍随这些估计处理。
- B5：保持已验收的条件性组合和吸收。本轮没有声称原始 Theorem 2.1 完成，原文计数等待独立逐项验收。
