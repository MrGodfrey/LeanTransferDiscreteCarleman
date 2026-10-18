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

C002 是重构代数接口，C003 是上述载荷/残差消去及所选载荷的离散对应，二者均为 AUXILIARY。它们不等于完整 Section 5：T003 已完成并验收条件性 M2，B5 在该真实范数框架内关闭；B1/B3/B4 仍是原始定理的剩余义务；T004 后原文覆盖计数为 1/26（Lemma 3.2）。

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
   受相应完整 `graphSq` 控制。此处原文使用“阶数至多 j、系数有界”；T003 当时尚待实例化；T005 已在真实弱 Sobolev 实例中证明该阶数条款，详见后节。
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
C020/P005 的 Lemma 3.2 全七项已由父监督者独立验收；C021 为已核对的辅助成果。PR7 合并 main `3dff0be3a1eaecbbfeb153e55219b9019bd1549b`，同 SHA main CI39033650091 实际通过，原文计数 1/26。

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

### T004 阶段后的未清偿边界（后续更新见 T005）

- B1：周期连续辅助解的存在、真实 H 值弱导数/图估计仍待 Lemmas 3.1/3.4；本阶段未把 a.e. D(A) 正规性加强为每时刻 D(A)。
- B2：保持已合并证明与实际调用；不重复假设。
- B3：时间单元、空间权乘法、真实观测截断和冻结移位上述部分已证明。对于任意抽象 TransferGeometry，
  仍必须给出实际空间/Sobolev 场、p.space/p.derivative/p.observation 的等式以及原文数值空间比较。
  未自动给所有抽象半范数族填充 ComparisonBridge，也未构造整份 TransferBridges。
- B4：连续/离散正则性、时间与空间误差估计及微分表达式的阶数界仍未证明；连续解/误差的所需加权有限性仍随这些估计处理。
- B5：保持已验收的条件性组合和吸收。本轮没有声称原始 Theorem 2.1 完成，原文 Lemma 3.2 已独立验收，计数 1/26。

## T005：权导数、真实弱 Sobolev 场与规范 transfer 几何

本阶段 C022 为 AUXILIARY，72 个新定理、110 个显式声明；原文完成数保持 1/26。
原文依据为 TeX 294–320、374、681–746、1348–1373，另核对 TeX 2675 的 `𝒟₁=∇`。
逐声明及全部边界见 `governance/reviews/T005.md`。

### 权导数与真实空间乘法

- `allowedWeight_spatial_derivatives_uniform` 使用实际 `iteratedFDerivWithin`：对固定紧集 S、
  `ContDiffOn n rho S` 及 `UniqueDiffOn ℝ S`，先取 C>0，再对所有 q≥1、任意实 tau、
  |eta|=1、j≤n、x∈S，证明 `‖D^j(q^tau exp(q eta rho))‖ ≤ C q^j q^tau exp(q eta rho)`。
  这里 D^j 为 Fréchet 多线性算子的算子范数。固定 rho 的有限阶界由紧性推导，
  不直接假设权导数结论。正反权及其倒数均覆盖，常数独立 T/qmax/tau/网格。
- `SpatialProfile.ofContinuousOn` 从固定紧域上的连续 rho 和 ν a.e. 支持于该域构造
  真正的 L² 权乘法；乘法函数与上式精确相同，不要求 rho 域外有界。
- `hasDerivWithinAt_logWeight/allowedWeight` 及 `derivWithin_logWeight_bound` 使用闭时间区间的
  实际导数。`SpatialProfile.logDerivative` 是 `∂t log sigma` 的真正 L² 乘法算子，
  `logDerivative_shift_le` 给出 `‖(∂t log sigma)v‖ ≤ β(|tau|+R)/L^(2m) ‖mu v‖`。
- `shift_derivative_ratio` 对实际 `mu=(Lq)^(2m)` 证明
  `|mu'|/mu² ≤ 2m beta / (L^(2m) qc^(2m−1))`，保留原 qc 依赖。
  原文 C²/q'' 假设对这些一阶时间结论不必使用，未增加时间每点 D(A) 假设。

这些是 Lemma 3.1 的依赖。原文 Lipschitz 域及 `C∞(closure Ω)` 的具体表示与上述 within
导数输入、Fréchet 张量与坐标高阶导数集合的表示、空间弱乘积法则/共轭图范数、
参数椭圆图估计、周期能量恒等式和存在论尚未全部建立，不能将 Lemma 3.1 标完成。

### 真正的弱 Sobolev 实现

`SpatialTest S` 包括所有全空间 C∞、紧支撑且支撑包含于 S 的实测试函数。
其本身及真实 Fréchet 方向导数均已证明属于 L²。
`IsWeakSpatialDerivative` 的 L² 内积式与实际积分式
`∫ (∂e phi)u = −∫ phi v` 等价。对开域及 a.e. 域内支持的测度证明弱导数唯一性；
`ν=volume.restrict Ω` 已实际复用构建，无新增的测试函数成员性前提。

`DerivativeFiber d k = EuclideanSpace ℝ (Sym (Fin d) k)`，每个多重指标出现一次。
`WeakSobolevJet` 由 0..m 阶真实 L² 集合和相邻阶弱导数关系构成线性空间；
零阶映射的单射性来自逐阶弱导数唯一性。
`sobolevSubspace` 是它在 H=L² 中的线性像；`sobolevJetEquiv` 和 `sobolevDerivative`
恢复唯一导数集合。零阶类及加权范数与原 H 类精确相等，无额外范数等价常数。
这不声称该子空间在 H 拓扑中闭或完备，也不把其 H 诱导范数冒充 H^m 能量拓扑。

`OperatorMultiplier` 用实际有界可测点态线性系数作用于向量值 L² 场。
标量 `ofCoefficients` 与向量 `ofVectorCoefficients` 从普通有界系数构造它，
后者的作用精确为 `sum_i v_i • a_i(x)`。`DifferentialExpression` 只求和 k≤j 的系数项，
其阶数由定义保证。`VectorCoefficient/vectorExpression` 保留梯度等向量值表达式。
最终 `sobolevGeometry` 允许每个 j 有不同实内积输出空间 Z_j；未限制所有 𝒟_j 为标量。

### B4-order 与 B3 的实际构造

`weighted_density_le` 由真实 L² 三角不等式、Cauchy–Schwarz 和 q≥1 推出有限阶表达式界。
`CarlemanExponents.order_exponent_le` 对所有 k≤j 证明
`c_j ≤ 2(m−k)+max(0,c_j−2(m−j))`（Lean j 编号为 j−1），保留原 clipped 能量权。
`sobolevGeometry_order` 直接得到原 `ErrorBridge.order` 的界，取
`K=1+sum_j sum_k coefficientBound(j,k)^2`；K 只依赖固定空间系数和阶数，
与 T/h/dt/q/qmax/方向/状态无关。右侧图项的可积性保持为 B4 `finite_energy` 的既有义务。
本积分比较不单凭非负积分不等式声称左侧可积；真实解/误差的时间加权有限性仍待解析正则性。

`sobolevGeometry` 在任意 conforming V≤sobolevSubspace 上构造 H、观测、每阶规范弱导数和
各 𝒟_j 的真实范数，离散 state/load/control 仍取原数值范数数据。
`conformingDerivative_weak/conformingExpression_ae` 明确真实弱导数和点态表达式，
无需再假设这些字段仅凭名称代表微分。
`sobolevGeometry_comparisons` 在单一
`dt*qmax² ≤ cellThreshold(beta, c0/2+o/2+sum_j c_j/2, rho.bound)` 下，同时给出
节点重构导数比较及其有限性、状态比较、普通 lift 的载荷比较和实际区域观测比较。
相应常数为 9、9C_N1、9C_N2、9C_N5，单元分析阈值先于 T/网格/权/状态，
且不扩大原 N1–N5 的允许权假设。所有周期离散状态和两种 Orientation 均保留。

### 阶段后尚未清偿

- B1：连续周期 shifted/frozen 解存在、真实 H 值 Sobolev 弱导数及图估计仍待；原 a.e. D(A)
  代表和 H 端点迹完全沿用 T003，未强化为每时刻 D(A)。
- B2、B5：已证明并复用，不重新假设。
- B3：T005 的规范 Sobolev 实例已导出各比较字段。实际数值空间必须满足原 N1/N2/N5
  的统一节点界；连续解/误差/残差的可积性、所有允许参数下的整份 ComparisonBridge/
  TransferBridges 尚待构造。任意自由给出的抽象 TransferGeometry 不自动满足这些识别。
- B4-order：在上述真实 Sobolev 实例中由有界系数阶数定理导出，不再是独立估计前提。
  通用条件性定理的 ErrorBridge.order 字段仍保留以兼容其它实现；调用该实例时由本定理填充。
- B4：Euler 适定与正则性、连续/离散时间空间误差、energy/l2/finite_energy/finite_l2、
  权族所需有限性及原阈值的统一选择仍待 Lemmas 3.1/3.3/3.4、Theorem 3.5、Section 4。
  不从本阶段辅助结果推断这些存在或误差估计。

## T006：真正图空间、时空加权有限性及桥接包实例

C023 为 AUXILIARY；12 个模块、73 个定理、92 个显式声明。原稿未修改，原文覆盖仍为 1/26。
完整逐声明边界见 `governance/reviews/T006.md`。本节更新 T005 中的未清偿项。

### 图空间与时间可测性

`weakJetSubmodule_isClosed` 将所有弱导数测试恒等式写成连续 L² 配对的闭等式，
证明有限乘积图范数中的 `WeakSobolevJet` 完备；同时证明此范数与各阶 L² 范数和等价。
不把其 H 线性像的 H 诱导范数当成 Sobolev 能量范数。
`truncate` 精确保留低阶场和零阶 H 类；`elliptic_bound_lower_order` 从原 A1 的 2m 阶界
推出 transfer 所需 m 阶界，无需另加低阶椭圆假设。原文通常 Sobolev 范数控制此有限乘积范数。

`memLp_domainSobolevJet_of_operator` 在 range(A) 上构造至真实图空间的有界逆，利用嵌入传递
强可测性，再用 A1 控制积分。因此 B1 已有的 `A U ∈ L²` 推出规范 jet 属于 Bochner L²。
不假设 A 满射、闭性或每时刻 D(A) 正规性。`PeriodicWeakTrajectory` 的 a.e. 域代表、H 弱导数和周期迹不变。
任意有限节点 jet 的两方向分片延拓属于 L²；相减得到实际 `U−R bar(z)` 的图空间 L²。

`continuous_expCLM` 证明 r→exp(rρ) 空间乘法在算子范数中连续，从而真实时变 L² 轨迹
乘 σ 后强可测。`memLp_map`、`timeSquareIntegrable_of_memLp` 及表达式/导数场定理先证明
平方可积性，再使用积分；`timeSq_eq_norm_toLp_sq`、`timeNorm_eq_norm_toLp` 识别为真正
L²(0,T;L²(Ω)) 类的范数。没有从 totalized 积分比较倒推可积性。
qmax 和任意冻结序列幅值只用于有限性，不用作统一估计常数。

### 实际 ComparisonBridge / ErrorBridge

`sobolevGeometry_comparisonBridge` 现在构造整份真实 B3 桥接包，包括全部 12 项有限性字段。
输入为原 A1(2m)、真实 B1 frozen 解、原 A4 以及 N1/N2/N5 的逐节点界；
单一时间阈值沿用 T005，K 统一控制 9、9C_N1、9C_N2、9C_N5。
观测仍为同一空间的区域截断，微分表达式仍有依赖 j 的向量输出，lift/Γ 仍为普通函数。
所有方向、所有离散状态都包括，未把最终离散 Carleman 估计作为输入。

`sobolevGeometry_errorBridge` 构造 ErrorBridge 的 order、shift、finite_l2、finite_energy。
它从原 A1(2m) 和 B1 正则性推出所有实际误差的加权有限性，继而调用已证明的有界系数阶数界
和冻结 μ 比较。只留下能量、L² 两项实质误差估计；使用原真实误差、原 ε_E/ε₀、
能量指数 max(0,c_j−2(m−j))，以及 c₀/o/4m 三个 L² 指数。
误差估计仍以实际辅助离散方程为条件，后续 ErrorBridge.total_bound 用已证明 B2 供给该条件。
K 同时支配 `differentialFamilyBound` 与 `(2L)^(4m)`；这些常数只依赖先固定的结构数据。
应用原 `conditional_transfer_uniform` 时共同 K 仍须在所有 T/网格/权/方向/状态之前选择。

### Lemma 3.1 的新增依赖

`coordinateDerivative_cons` 将 Fréchet 张量坐标评估识别为真正重复坐标导数；
`coordinateVector_represents` 保证每个多重指标一次。
`allowedWeight_coordinate_derivatives_uniform` 将既有张量界转为真实 Euclidean 坐标集合界，
仅增加固定维数/阶数因子，C 先于 q/τ/正反符号/阶数选择。
原 Lipschitz 域与 C∞(closure Ω) 到 compact/UniqueDiffOn 输入的接入尚未证明。

`IsWeakSpatialDerivative.mul` 通过真正紧支撑光滑测试函数证明弱空间乘积法则。
权只需在开域内光滑；测试支撑在域内保证乘积全局光滑。
`weak_derivative_weighted` 专用于原指数乘法，得到 d(σu)=σdu+q(dρ)σu，
固定 profile 的方向导数界明确作为输入；负 profile/负指数适用于逆权。
本阶段只完成一阶空间弱公式，未声称完成所有高阶弱 Leibniz 或时间弱共轭公式。

`logDerivative_spacetime_le` 证明实际 Bochner L² 扰动界
`‖(∂t log σ)u‖ ≤ β(|τ|+R)/L^(2m) ‖μu‖`，m≥1、L>0。
导数先在 (0,T) a.e. 识别为真正 deriv q，再证明强可测、平方可积后比较范数。
常数独立 T/qmax/mesh；这已超出固定时刻界，但不声称产品测度 L² 的等距同构已构造。

### 本阶段后的精确剩余义务

- B1：原 Lemmas 3.1/3.4 的连续周期 shifted/frozen 解存在、参数椭圆图估计、周期能量恒等式；
  高阶弱乘积/共轭与时间弱乘积、算子域闭性及稠密核/逼近识别仍待。
- B2/B5：已证明且继续复用，不重新假设。
- B3：在规范 Sobolev 实例、原 A1/A4 与 N1/N2/N5 和已存在 B1 解下整份构造完成；
  不再单独假设有限性。具体数值方案仍须满足原统一节点界，原抽象自由 TransferGeometry 不自动拥有这些识别。
- B4：order、shift、finite_energy、finite_l2 在此实例中均已消去；剩下真实能量与 L² 误差估计，
  包括 Euler 适定/时间与空间误差、原权族覆盖与统一阈值的完整应用。
- 完整 `TransferBridges` 仍需 B1 每个载荷的存在量词和 B4 两项估计，不能从本构造推断原始 Theorem 2.1。

## T007：原 form 的关联算子与周期 Euler 适定

C024 为 AUXILIARY：12 模块、66 定理、104 显式声明，完整逐项清单见 `reviews/T007.md`。
本阶段改变证明路线，直接在有限个原无限维能量空间的 Hilbert 直积上用 Lax–Milgram；
不需要先构造无界谱分解或预设周期解。原稿及最终结论未改，原文计数仍 1/26。

`SobolevHilbert` 的范数平方恰为每阶实际弱导数 L² 范数平方和，且与既有弱 jet 图拓扑
连续线性等价。`conformingHilbert` 的零阶嵌入范围严格等于原 V；原 V 在 Sobolev 拓扑闭
给出能量空间完备，原 H 稠密性给出稠密嵌入。没有将 V 的 H 诱导范数冒充能量范数。
`conformingCoerciveForm` 接入原连续有界对称 coercive form；`IsAssociated` 是原 A 的完整
变分域/作用定义。`domain_eq` 和 `operator_eq` 证明既有 D/A 与构造完全一致。

由 A1 推出每个 r≥0 的 (A+r) 逆、真正 H×H 图闭性及 D 在 H 稠密。
`existsUnique_periodicEuler` / `conformingEuler_existsUnique` 对任意非负节点 μ、任意实际 H
节点载荷、所有网格和两个方向证明整个周期 Euler 存在唯一；无空间有限维或低频限制。

`euler_energy_identity` 证明原周期能量恒等式的 form 写法：A 半阶能量项写为
Σa(Δu,Δu)=dt²Σa(Du,Du)，按原 A1 等于对应 A^(1/2) 能量，不额外构造分数幂算子。
移位缺陷为 −Σ(μ(τ⁻¹i)−μ(i))‖uᵢ‖²，τ 分别为 prev/next。
直接反向使用已证单元分析得两方向同常数的 μ=(Lq)²ᵐ 增量界，并消去半吸收前提。
令 S=2·(2m)·2^(2m−1)·β，L≥max(1,2S)，dt·qmax²≤cellThreshold(β,0,0)，
`euler_unweighted_graph` 得到真实 dt 加权离散范数
‖D±u‖+‖Au‖+‖μu‖≤3‖D±u+Au+μu‖。
`periodicEuler_wellposed` 同时给出实际唯一解与 prescribed 载荷范数界。
这些阈值/常数先于 T、网格、权、方向、载荷、状态；qmax 没有进入图估计常数。
原 A1 椭圆界进一步给出实际每阶未缩放弱导数序列的 L² 范数和界。

### 更新后的未清偿义务

- B1：连续周期 shifted/frozen 解存在、真正 H 时间弱导数与周期迹构造、连续周期能量、
  参数 Sobolev 图估计仍待。关联算子的图闭性和定义域稠密已证明，光滑稠密核未证明。
  `PeriodicWeakTrajectory` 的 a.e. 域代表没有改成每时刻域正规性。
- Lemma 3.1 / 3.3：原 Lipschitz 域上的参数插值与 smooth-closure 接入、高阶弱乘积/共轭、
  时间弱乘积及允许权族统一加权估计仍待。上述未缩放导数界不含 (Lq)^(2m−j)，
  不声称完成 eq:euler-unweighted-graph 或完整加权 Lemma 3.3。
- B2/B5 已证明；B3 在规范 Sobolev 实例和已存在 B1 下沿用 T006 完整构造。
- B4：Euler 存在和未加权算子估计已导出；原实际能量/L²时间及空间误差、允许权族的
  加权正则性和统一阈值组合仍待。order/shift/finite_energy/finite_l2 沿用 T006。
- 完整 TransferBridges 的 B1 存在量词和 B4 两项误差没有被本阶段结果替代；原 Theorem 2.1
  仍未完成，无新增最终离散估计假设。

## T008：真实周期弱图空间与构造性时间频率依赖

C025 为 AUXILIARY：13 模块、70 定理、114 显式声明，逐项核对见 `reviews/T008.md`。
原稿、所有原文目标和原文计数 1/26 不变。

`PeriodicGraph` 是 C([0,T],H)×L²(0,T;H)×L²(0,T;H) 中的闭子空间；三个条件分别是
真正 H 分布弱导数、a.e. 原算子图、端点迹相等。`IsWeakTimeClass.iff_weakDerivative`
证明所有 L² 测试与原 Bochner 恒等式等价，向量分布测试给出导数唯一性。
实际已证 resolvent R=(A+1)⁻¹ 将 a.e. 图条件识别为 R(Au+u)=u 的 L² 闭等式。
`toTrajectory` 和 `toPeriodicGraph` 双向连接原 B1 接口，保持 [0,T] 全部 H 值及 a.e. du/Au；
没有额外假设每时刻 D(A) 正则性。完整图空间在 C×L²×L² 范数完备。
`evolution_eq_iff` 对任意有界可测 μ 及两方向精确识别 ±du+Au+μu，含原半开单元冻结乘法。
强图极限保持方程；本结论不包含极限存在或演化映射满射。

任意 r≥0、ω∈ℝ、f/k∈H，原 coercive form 在 V×V 的真实 Hilbert 范数上经
Lax–Milgram 给出唯一 x/y∈D，满足 Ax+r x+ω y=f、Ay+r y−ω x=k。
由原 A 对称性证明精确频率能量及
‖Ax‖²+‖Ay‖²+(r²+ω²)(‖x‖²+‖y‖²)≤‖f‖²+‖k‖²，常数独立 T/r/ω。
`frequencyTrajectory` 以 ω=2πn/T、耦合频率 s.sign·ω 构造原弱轨道并验证实际时间方程。
`exists_finite_harmonic` 对任意有限整数频率集和 H 系数构造连续周期弱解；原 D/A 经完整 A1
变分定义接入。有限时间频率是此辅助结论的明确范围，不替代原任意 L² 载荷目标。

`EulerTimeEmbedding` 真实复用已构造 Euler 解；原双向分片常数延拓属于 Bochner L²，
其范数平方严格等于 dt·Σ‖uᵢ‖²。状态与 Au 延拓位于真实时间算子图，
μ=(Lq)²ᵐ 的延拓差分/Au/μu 范数和≤3·载荷延拓范数，使用 T007 原统一阈值。
延拓差分尚未识别成某个分片仿射重构的真实弱导数，更不是分片常数状态的弱导数。

### 继续未清偿的义务

1. 原 B1 任意载荷连续存在：向量值有限谐波密度、时间积分图界及 C([0,T],H) 解收敛；
   或 Euler 单元平均/仿射重构、真实弱导数、紧性/极限。已给出闭性不等于这些极限存在。
2. 原 μ(t)/冻结 μ 的连续周期能量与 T 统一图估计、参数 Sobolev 插值、时间弱乘积、
   高阶弱共轭和完整允许权族估计仍待。连续乘法范数依赖系数大小不能用来冒领这些统一界。
3. B2/B5 已证明；规范 B3 和 B4 的 order/shift/finite 条款继续复用。B4 实际 energy/l2
   时空误差及原统一阈值组合仍待，完整 Lemma3.3 和原 Theorem2.1 未完成。

## T009：任意真实 L² 载荷连续周期存在与一般弱解唯一性

C026 为 AUXILIARY：18 模块、81 定理、94 显式声明，逐项核对见 `reviews/T009.md`。
原文目标及原稿不改，完成数仍 1/26。采用原 form 的频率求解加闭值域证明路线，
没有新增密度、图界、H¹→C 连续性或目标连续解存在假设。

原 Bochner 弱时间导数先推出闭周期所有迹点的 FTC、绝对连续、a.e. 强 H 导数及能量恒等式。
其中 H¹→C 估计为 ‖u‖C≤T^(−1/2)‖u‖L²+T^(1/2)‖du‖L²；该 T 依赖只用于图拓扑构造。
真实 H 值有限谐波在原未归一化时间 Bochner L² 中稠密，未假设 H 可分。
C¹ 原算子图近似核的时间积分估计为 ‖du‖²+‖Au‖²+r²‖u‖²≤‖F‖² (r≥0)，
并有原 form 给出的 α>0、(α+r)‖u‖≤‖F‖。由完整 C×L²×L² 范数控制得闭值域，再由
实际谐波密度得每个任意 L² 载荷的连续周期解。一般弱能量先证明全部弱解唯一性，
因此近似核在整个周期图空间稠密，du/Au 交叉项为零及上述图界传递给所有弱轨道。
不把“极限保留方程”当成“极限存在”。

对任意有界可测非负 μ，令 R 为其有限界，实际常数求解器的状态算子给出收缩
R/(α+R)<1，从而 `existsUnique_variable_periodic` 构造任意 L² 载荷唯一解。
`IsAssociated` 完整变分域/作用等价将存在和一般弱唯一性转回原 D/A。
最终轨迹仍只要求 a.e. D(A) 值代表、真实 H 弱导数及周期 H 迹；每时刻图值 C¹ 仅是稠密核的性质。
原 Section5 的 `transferLoad g μ f z` 经真实半开单元延拓直接接入
`LoadInterface.exists_frozen_transfer_trajectory`，全离散状态、普通函数 Γ/lift、F 无结构限制。

原 μ=(Lq)^(2m) 的 AC 性由原权类证明，其导数比精确为
δμ=2mβ/(L^(2m)qc^(2m−1))。实际变系数周期能量给出
‖du‖²+‖Au‖²+(1−δμ)‖μu‖²≤‖F‖²，δμ≤1/2时三项和≤2‖F‖²。
冻结系数仅可测，使用已证 Lemma3.2 单元比较及真实乘法扰动，不对其使用经典导数。
β dt qmax²≤1/2、2(2m)2^(2m−1)β dt qmax²≤1/4 时，冻结三项平方和≤16‖F‖²。
`frozen_periodic_uniform` 实际构造 L₀=max(1,4mβ) 和
δ=1/(1+2β+4·[2(2m)2^(2m−1)β])，在原 q≥1 下先于 T、网格、q、两种独立方向及载荷取定，
L≥L₀、dt qmax²≤δ 即给出唯一解和该常数16图界。

### 更新后的未清偿义务

1. B1 的任意载荷连续存在、一般弱解唯一性、真实弱正规性和周期迹已清偿；
   原 A1 接入使用已证明的完整关联等价。A4 连续 Carleman 估计仍是原假设。
2. Lemma3.1 的空间参数 Sobolev 插值 `eq:parametergraph`、高阶弱乘积与共轭、
   完整 σ 与 (Lq)^(2m−j) 图估计、formbound/coercive 任意 margin 仍待。
   本阶段 Au/μu/du 图范数不能冒充这些空间导数和允许权族范数。完整 Lemmas3.1/3.3/3.4 未完成。
3. B2/B5 继续复用；规范 B3 的所有比较和有限性继续复用，现可输入本阶段构造的真实 B1 解。
   B4 的 order/shift/finite 条款已证；实际 energy/l2 时间与空间误差、统一阈值组合仍待。
   `TransferBridges` 的剩余实质误差未消去，原 Theorem2.1 仍未完成。

## T010：全阶弱空间乘积、双向加权共轭与原移位 form

C027 为 AUXILIARY，14模块/67定理/85显式声明；逐项核对和表示边界见 `reviews/T010.md`。
完整 Lemmas3.1/3.3/3.4 未完成；原稿/原目标不改，原文计数仍1/26。

`WeakSobolevJet.weightedNorm` 是原 N 的真实有限平方和平方根，`parameterNorm` 是原 R 的
真实各阶L²范数之和。阶数分别取m和2m，字段沿用原Sym多重指标与Euclidean范数。
通过有序word递推证明真实分布Leibniz公式，再由分量范数平方恒等式还原全字段；没有重新假设高阶弱乘积。
`conforming_conjugation_uniform` 在A2的实际域保持性下，先选一个C，再对所有TimeWeight、
时间、tau和正/负profile、原子空间全部状态给R与N的双向空间比较。逆向实际使用逆权导数展开。
空间C不依赖T/L/qmax/网格/tau/符号/状态；n!/有限profile导数界和固定card(Sym)损失均可见。
入口明确使用rho在包含紧集K的开邻域U上C∞，而非擅自将任意闭集ContDiffOn识别为光滑延拓；
若原rho采用另一种C∞(闭包)约定，表示等价仍需接入。form和A2扰动不需要此入口。

`allowed_shiftedForm_bound` 与 `allowed_shiftedForm_coercive_uniform` 完成原A3推出的
两个空间form结论：C(L)=C+L^(2m)；给定B≥0先选L₀=max(1,C+B)，保留cN²+B‖qσv‖²。
σ²v使用同一允许权作用两次，未扩大原允许指数族。配对是实际L²，原V的能量拓扑未换为H诱导范数。
`conjugatedCommutator_parameter_le` 使用原A2的实际[A,σ]σ⁻¹v，给C/L倍R_(Lq)的空间扰动界。
没有将目标图估计或最终离散估计作为这些结论的前提。

### 继续未清偿的义务

1. 原bounded Lipschitz域上的参数Sobolev插值/扩张：固定mathlib现有全空间紧支撑GNS及
   Bessel-potential分布不能直接覆盖一般原状态。零延拓会添加边界条件；只用A1粗界会产生
   错误q幂；均未采用。需实际Lipschitz扩张+缩放插值或等价局部差商证明，保持原域一般性。
2. 真正时间弱乘积、允许权的完整时空图估计及Euler加权最大正规性尚缺；本阶段空间R比较
   不等于各阶Bochner L²范数之和的原时空R结论。未声称已完成eq:primitivegraph。
3. B1存在/一般弱唯一性/真实弱正规性/周期迹已由T009清偿；B2/B5、规范B3及B4-order/shift/finite继续复用。
   B4实际energy/l2时间与空间误差及统一阈值组合仍待，`TransferBridges.solutions`未整体清偿。

## T011：真实弱时间乘积、Bochner 时空共轭与图正规性

C028 为 AUXILIARY；14 模块/47 定理/56 显式声明，逐项边界见 `reviews/T011.md`。
这是完整的弱共轭正规性阶段，不是完整 Lemma3.1/3.3；原文计数仍 1/26。

`hasDerivAt_expCLM` 用真实 L² 乘子的二阶算子范数余项求导；
`hasWeakTimeDerivative_map` 从原 H 值弱导数、连续代表及导数 L²，推出
(σu)'=σu'+(∂t logσ)σu 的真实 Bochner 分布恒等式。系数 AC、a.e. 真导数和产品 L²均已证明，
不再把一般乘积辅助引理的这些前提留给实际权调用方。闭区间连续和周期 H 端点迹也保留。

`operator_aestronglyMeasurable` 从原 A1 关联算子的闭图可测逆推导 A 路径可测性，
`WeakSobolevJet.aestronglyMeasurable_of_value` 对完整弱 jet 做同样提升；不是假设 A 在 H 中连续。
实际空间 L² 的第二可数性由有限维空间及有限紧集测度条件证明，无新增空间可分假设。

`spacetimeParameterNorm` 是原 sum_j ‖q^(n−j)σD^j u‖_(L²_t L²_x)，n=2m 对应 R。
`conforming_spacetime_conjugation_uniform` 使用已证空间 Leibniz/共轭，先推得加权 jet 的 Bochner L²，
再用 Minkowski 得实际时空 R 双向比较；C 在 T/q/qmax/tau/正负profile/路径之前固定。
点态空间 R 的 L² 与各阶 L² 范数和仅使用不等式比较，固定损失 n+1；不将它们写成等式。
定义的 eLpNorm.toReal 总化不被用于隐藏无穷范数：每条实质比较均要求或证明所有字段 MemLp。

`allowedCommutator_spacetime_le` 将原 A2 的 [A,σ]σ⁻¹v 和 j=0…n−1 全字段直接接入，
证明换位子强可测、L²及 C/L 倍 R_(Lq) 的原时空界。`weightedOperator_L2` 进一步由此推得 A(σu)∈L²。
`exists_weighted_trajectory` 用原 A1 椭圆界、关联定义及 A2，构造原 PeriodicWeakTrajectory 的加权版本；
仅要求 a.e. D(A) 值，实际 H 弱导数、A 项 L²、连续性和周期迹全部给出。
`weighted_conjugation_identity` 证明原 9.26-eq2，两个 Orientation 均适用，μ任意；原 μ=(Lq)^(2m) 是其特例。
T005 原时间扰动 C/L^(2m) 估计现在可应用于这条真实加权轨迹。

### 尚未清偿且未改作结论前提的义务

1. 原 bounded Lipschitz Ω 的参数 Sobolev 插值/扩张 eq:parametergraph：需要把测度专化到
   volume.restrict Ω，建立原 Lipschitz 几何的弱 H^n 扩张及缩放插值，或等价局部差商证明。
   固定库的全空间紧支撑 GNS/Bessel 分布及标量 Lipschitz 扩张不能直接填补此桥。
   零延拓的额外边界条件与 A1 粗界的错误 q 幂均未采用。完整 eq:parameterparabolic、
   eq:primitivegraph、Euler 加权最大正规性仍待，不能由本阶段正规性和共轭恒等式推称已证。
2. 高阶空间共轭沿用明确的开邻域 C∞ 表示。未把任意闭集 ContDiffOn 当作该表示，
   原 C∞(闭包) 的另一约定仍需表示接入；没有修改原目标或擅自增加边界/域限制。
3. B1 存在及弱唯一性已由 T009 清偿；B2/B5、规范 B3、B4-order/shift/finite 继续复用。
   B4 实际时间/空间 energy 与 L² 误差、统一阈值组合及 TransferBridges.solutions 尚未清偿。

## T012：原域障碍核对与实质时间误差

原稿 `paper/main.tex:291` 只写 `ρ∈C∞(Ω̄)`，没有定义为某个开邻域上的光滑函数限制；另一处闭包光滑系数也没有补充定义。因此 T010/T011 的 `U` 开、`K⊆U` 邻域表示仍是明确未接通的入口，不能自动计入原 Lemma3.1。未改写原稿，未将 `ContDiffOn ℝ ∞ ρ (closure Ω)` 与内侧导数连续或邻域表示混同。若采用内侧各阶导数连续到闭包的标准含义，可尝试直接从紧性取得内侧导数界，再将弱 Leibniz 限于 Ω 内的测试函数；这一调整可能绕过完整 Whitney 延拓，但本阶段没有把这种可能性计为证明。

原 `eq:parametergraph` 的具体缺口是：对 `ν=volume.restrict Ω` 的完整弱 H^(2m)(Ω)，建立 `Σ_j r^(2m-j)‖D^jv‖ ≤ C(‖v‖H^(2m)+r^(2m)‖v‖L²)`，常数在 r≥1 前选定。固定 mathlib 的 `Analysis/FunctionalSpaces/SobolevInequality.lean` 是全空间紧支撑 C¹ 的 GNS；BesselPotential/Distribution Sobolev 库不提供原 Lipschitz 域的全阶弱扩张。零延拓会强加 V⊂H₀^m 或更高阶边界条件；把各阶范数都粗略压到 ‖Av‖ 会产生 r^(2m)‖Av‖，破坏所需统一性。一般 Lipschitz 图表的直接高阶反射也没有 H^(2m) 链式正规性，不能作为已证扩张使用。可行后续路线需要原域有限锥形覆盖、弱平移 FTC/密度及差商/Taylor 平均，或完整高阶扩张；这些尚未建立。

按监督者允许的路线切换，本阶段完成独立的实际时间误差分析，而非再增加最终误差前提：

- `affineReconstruction u := u₀ + ∫₀ᵗ extensionMinus(forwardSlope u)` 是真实 H-valued Bochner 原函数。证明所有节点值、闭周期连续性/端点迹、H 弱导数及 a.e. 单元公式。两方向均有 `∂t û = ε extension(D_ε u)`，并得到 `‖û−bar u‖L² ≤ δt‖D_εu‖ℓ²`。
- 任意 H¹ 弱轨迹之间的周期分部积分由 AC 和实际导数得到。闭算子时间图的自伴配对、真实冻结乘子的自伴配对、连续反向 evolution 和实际 Euler 解给出 `⟨U−bar u, P_{−ε}Y⟩ = −ε⟨û−bar u,Y_t⟩`。此处没有假设重构误差方程或目标离散估计。
- `temporal_l2_error_uniform` 直接调用 T009 构造的任意载荷冻结连续解/反向对偶解及 T007 全状态 Euler 解，得到 `‖U−bar u‖L² ≤ 12 δt‖f‖ℓ²`。L₀、δ 在 g/T/q/L/方向/f 之前选定；没有谱 CFL 限制，μ 始终是原 `(L q_i)^(2m)` 的对应方向冻结。
- `timeEnergy(e,Ae)` 用原 form 的 `(A+1)⁻¹:H→V` 构造真实 L²(0,T;V) 类，嵌入恰为 e；其 form 密度为 `(e,Ae)_H`。原 A1 强制性、已证 L² 误差及两个真实图界给出 `‖e‖L²(V)^2 ≤ (84/c) δt‖f‖ℓ²²`。这不是含 q 权的参数 N 范数，也没有假设参数插值。
- `IsAssociated.temporal_weak_error_uniform` 将 L² 结论转回原 D/A 和 Bochner 函数范数，明确证明误差 MemLp。连续解保留 a.e. D(A)、H 弱导数和周期 H 迹，不引入每时刻 D(A) 正规性。

**范围仍是 AUXILIARY**：本阶段证明未加权时间 L² 和 form-energy 误差；它们不是原允许指数权族的 Theorem3.5，不能清偿 B4 的加权 energy/l2 字段。完整 Lemma3.1/3.3、加权冻结正规性、原参数插值及光滑表示、空间误差和统一 B4 权族组合继续保留。原文完成仍 1/26；原始 Theorem2.1 未完成。B2/B5 和规范 B3、B4 finite/order/shift 沿用既有证明，Γ仍是普通函数。

## T013：内在闭包光滑、真实时空 N 与 A3 加权算子能量

C030为AUXILIARY：12模块/35定理/44显式声明，逐项核对见`reviews/T013.md`。原文仍1/26，原稿/最终结论不改。

`SmoothOnClosure ρ Ω` 精确表示ρ在闭包连续、在Ω内C∞、每阶实际Fréchet导数有连续闭包延拓；`smoothOnClosure_iff_coordinate`证明它与全部实际坐标词导数的连续延拓描述等价。有限张量坐标恢复CLM由基的多线性外延、代数左逆及有限维连续性构造。已证明邻域C∞表示蕴含此内在条件、任意域外代表改变不影响条件、各阶连续延拓在闭包唯一及负profile保持条件。没有宣称Whitney邻域扩张，也没有把任意闭集ContDiffOn当成上述条件。

有界Ω的闭包紧性给全部实际内侧导数统一界；实际允许权q^τexp(±qρ)及其逆权全阶相对导数界的C先于q、τ和符号。原`ν=volume.restrict Ω`的profile直接构造且value等于ρ。全部弱Leibniz、空间R/N四方向比较、真实Bochner时空R及原PeriodicWeakTrajectory加权正规性通过新`intrinsic_*`/`closure_*`入口接通，调用方不再提供开邻域光滑前提。旧入口保持兼容。轨迹只要求a.e.D(A)、真实H弱导数和周期H迹；已有弱共轭恒等式直接用于新构造轨迹。

`spacetimeWeightedNorm`定义原各阶q^(m−j)σD^j的Bochner L²范数平方和的平方根，已证明N²恰为空间N²的时间积分。所有比较有明确MemLp，空间N比较提升时保持同一个C。`closure_spacetime_energy_conjugation_uniform`给真正时空N双向比较，常数在T、q、τ、符号和轨迹之前选定。

本阶段另实际证明保留原误差结论的能量路线：对原D(A)⊂V状态，由A1测试恒等式和A3，L^(2m)≥C时
`c Nσ(u)² ≤ ‖σ(A+(Lq)^(2m))u‖L² ‖σu‖L²`。
`allowed_spacetime_operator_energy_uniform`证明时空版本，并在g/T、q、profile、τ、状态前选L₀；所有加权字段和算子L²有限性由无权图正规性推导，适用profile及其负号、τ及−τ。没有输入目标误差或图估计。这可替换原时间误差证明对D(A)误差使用的单独能量插值步骤；不冒称对任意H²ᵐ状态的原`eq:weighted-interpolation`已经完成。

### 精确的剩余依赖

1. 原`eq:parametergraph`仍未证明。所需同一个弱Hⁿ扩张须同时L²有界、Hⁿ有界且真实弱字段限制回原域；Hⁿ有界本身不够。全空间弱jet与Fourier/Bessel描述也未建立等价。内锥差商替代路线仍缺原Lipschitz有限锥覆盖和弱平移FTC/全阶密度。具体声明、库源检查和失败替代路线保存在`analysis/T013-interpolation.md`，没有把缺口改写成论文假设。
2. 原连续/Euler/frozen的统一允许权R图界、加权仿射缺陷/对偶导数界和时间加权L²仍待。新A3能量估计右端的这两个加权界未清偿，因此T012的12δt、84/c无权估计仍不能填写B4加权energy/l2。
3. B1存在/弱唯一性/周期迹、B2/B5、规范B3及B4 finite/order/shift继续复用；N1–N5空间误差、完整权族阈值组合及`TransferBridges.solutions`实质误差仍待。原Theorem2.1没有宣称完成。

## T014：实际冻结误差能量与完整全空间弱参数插值

C031为AUXILIARY：13模块/45定理/51显式声明，逐项核对见`reviews/T014.md`。原稿和最终目标不改，原文仍1/26。

`shiftedForm_coercive_of_lower`把原A3能量推广到任意实μ≥(C+B)q^(2m)，保留B≥0的margin；空间及真实Bochner时空版本不要求μ连续或可微。已证单元q(t)≤2q_anchor给实际两方向`frozenMultiplier`的下界。取L₀=2max(1,C)、δ=cellThreshold β 0 0，阈值在T/grid/s/q/L/state之前，得到Cq(t)^(2m)≤barμ(t)。

`FrozenEulerPair`由原A1完整关联等价及既有求解器构造任意同载荷的连续/Euler解对。连续轨迹仍只要求a.e.D(A)、真实H弱导数与周期H迹。实际域代表误差e=U.domainValue−bar u与U−bar u几乎处处一致，真实图L²及H^m有限性由原A1单向椭圆界/截断推出。逐项相减证明
`(A+barμ)e = extension(Dεu) − εU_t`。
`frozen_error_energy_uniform`直接得到
`c Nσ(e)^2 ≤ (‖σ extension(Dεu)‖L² + ‖σU_t‖L²) ‖σ(U−bar u)‖L²`。
没有μ−barμ扰动、反向A1界或L^(2m)载荷损失；两个加权导数和误差L²的统一载荷估计仍待，不宣称完整Theorem3.5。

全空间路线不再需要未证Fourier识别：用真实反射测试κ(x−y)证明分布弱导数的卷积交换；sqrtκ加权Cauchy–Schwarz和真实卷积积分证明非负单位质量核的L²收缩。原L²状态无需紧支撑。光滑卷积的完整可积性及全空间IBP给弱链估计，具体半径1/(n+1)、2/(n+1)的归一bump通过Lebesgue微分定理a.e.收敛，再用Fatou得到同一任意方向弱链u→v→z的`‖v‖²≤‖u‖‖z‖`。未假设交换、收缩、稠密性或目标插值。

真实Sym多重指标相邻阶分量满足上述弱链；有限分量最大值的log-convex递推及已证有限离散最大值原理控制缩放r^(n−k)序列，再由完整Euclidean分量平方和还原字段。`fullSpace_parameter_interpolation_uniform`给∃C≥1（仅依赖d,n），随后∀r≥0及所有全空间弱Hⁿ jet：
`Σ_k r^(n−k)‖D^ku‖L² ≤ C(‖u‖jet+r^n‖value u‖L²)`。
最大值仅是内部证明工具，最终结论仍是真实全部导数字段，含n=0/d=0。

### 精确剩余依赖

1. 原bounded Lipschitz Ω上的同一个高阶弱扩张须同时L²有界、Hⁿ有界，并使每个实际弱导数字段限制回Ω等于原字段；本阶段没有构造该扩张。因此原`eq:parametergraph`尚未完成，全空间结论不能计为原Lemma3.1。已试路线及下一接口见`analysis/T014-interpolation.md`。
2. 原允许权连续/Euler/frozen的统一R图界、加权仿射缺陷及对偶导数界、加权时间L²误差仍待。新冻结能量可以直接用于实际误差，但右端的加权载荷界仍需证明。
3. B1存在/弱正规性/周期迹、B2/B5、规范B3及B4 finite/order/shift继续复用；N1–N5空间误差、完整权族阈值和B4实际energy/l2尚未清偿。原Theorem2.1未完成，未增加最终离散估计假设。

## T015：真实加权时间L²、仿射缺陷与冻结图余项

本阶段 C032 为 AUXILIARY。`TimeL2Multiplier` 以实际 σ=q^τ exp(qρ) 作用于 Bochner 时间 L² 类；空间/时间代表只 a.e. 比较，逆权取同一ρ的负与−τ，σ²载荷取两次映射。`weighted_affine_defect_uniform` 在 δ 先于 g/w/T/τ/sign/全节点状态的次序下给真实范数 `3 dt · gridNorm(σ_nodes Dεu)`；`weighted_temporal_duality_uniform` 构造原连续、Euler及反向伴随解，并保留真实逆权伴随导数因子。对应原文 eq:timedelta 第一段、eq:temporal-dual-equation、eq:timecancellation，不宣称 eq:temporal-l2-error。

`logDerivative_frozen_small_uniform` 对任意预先给定 η>0，选择统一 L₀/δ 后，将实际 log 时间导数作用控制为 η 倍真实冻结移位范数。`exists_weighted_frozen_graph_remainder_uniform` 由原 A1 单向椭圆界、A2 及已有弱乘积/图转换构造加权轨迹，吸收时间项后得到常数30的加权时间导数/A/冻结移位界，右端为实际加权残差与实际 `A(σU)−σAU`。`weighted_graph_commutator_ae` 将该余项与原 A2 的 `[A,σ]σ⁻¹` 完全匹配。`weighted_adjoint_remainder_uniform` 构造 W²e 的反向伴随，M=W⁻¹，得到 `‖MY_t‖≤30(‖We‖+‖AZ−MAY‖)`，Z=MY为构造出的弱图，不作为存在/估计假设。

原 B1 的 a.e. 域/H弱导数/周期迹不加强为每时刻 D(A)；时间方程方向与冻结延拓方向可独立选择。一般关联 A 与 form 算子的域/算子等价已证；本阶段具体图定理以 form 算子陈述。三个图构造/伴随包装定理直接使用 T013 的 `exists_closure_weighted_trajectory`：`IsOpen S`、`Bornology.IsBounded S`、`SmoothOnClosure ρ.value S` 与原 A1/A2 即给所需轨迹，不要求存在更大的光滑开邻域。`SmoothOnClosure.of_neighborhood` 只证明邻域光滑 → 内禀闭包光滑；没有逆向桥，也没有使用 Whitney 延拓。先前本段所称“内在闭包到邻域接口”方向错误，已按 PR #18 独立审核纠正。

B4 未清偿边界没有扩大或隐藏：原 Lipschitz 域同一高阶弱扩张的同时 L²/Hⁿ 界（或等价原域插值）、允许权空间交换子吸收、允许权 Euler 图界、闭合的加权时间 O(dt)/O(sqrt(dt)) 及空间误差仍待。全空间插值不能替代原域；带交换子余项的图界不能替代原文完整 R 图界。精确依赖与已试路线见 `governance/analysis/T015-weighted-time.md` 和 T014 检查点。原文完成仍为 1/26。


## T016：一般阶 Euler 权余项、A3 低阶吸收与二阶闭合时间率

完整接口与剩余依赖见 [T016 数学阶段](analysis/T016-weighted-graph-closure.md) 和 [逐声明核对](reviews/T016.md)。新增14模块、31定理、37显式声明，范围 AUXILIARY，不增加原文整项完成数。

`weighted_euler_graph_remainder_uniform` 对任意 m>0 证明真实允许权 Euler 图常数6，保留且仅保留实际空间交换子；时间交换子已经统一吸收。`weighted_lowOrder_absorption` 对任意 m>0 证明 q^m N_m 与 q^m R_m 的任意小量吸收，明确只覆盖0至m阶。

`secondOrder_commutator_small_shift` 在 m=1 用原A2/A3及内禀闭包共轭消去全部空间交换子；得到常数12的离散算子图、常数60的冻结连续算子图。`secondOrder_parameter_graph_uniform` 用正向A1控制最高阶，构造完整R₂；`secondOrder_weighted_euler_sobolev_uniform` 对全部周期D(A)序列证明真实导数字段L²范数之和的Euler图。阈值与常数先于T/网格/权/方向/τ/状态选定，profile只要求原域上的SmoothOnClosure，不要求邻域表示。

`secondOrder_weighted_temporal_error_uniform` 构造实际Euler/连续/伴随解，在原周期弱图的a.e.域误差代表上证明 2160 dt 的真实加权L²率和 sqrt(466560/c) sqrt(dt) 的真实N₁率；声明包含弱jet的MemLp。Γ普通函数、已证B2和真实B3原接口不变。

B4仅在m=1的**时间部分**获得闭合。一般阶m+1至2m−1导数的原域参数插值、空间比较及所有权族的最终组合实例仍待；不把二阶辅助结果登记为一般Theorem3.5完成。此路线绕过任意Sobolev扩张的需要只限当前二阶推导，不假设一般域扩张存在。


## T017：一般阶时间条件链与原域内锥几何

详细陈述、常数和B1–B5余额见 [T017数学阶段](analysis/T017-higher-order-analysis.md)，逐声明核对见 [T017核对](reviews/T017.md)。新增10模块、11定理、17显式声明。C034为CONDITIONAL，C035为AUXILIARY，原文仍1/26。

唯一新增分析前提是实际D(A)上的 `DomainParameterInterpolation`：同一Cinterp对所有r≥1、u∈D(A)，控制Σ r^(n−j)‖D^ju‖为Cinterp(‖jet_n u‖+rⁿ‖u‖)。原A1只正向将jet控制为Au；没有反向A1或导数域保持。全空间实例已由既有弱插值证明，原bounded Lipschitz域实例尚待，所有一般阶调用均显式保留hI。

在该前提下，真实A2交换子已统一吸收；一般m的Euler算子图12、完整离散R₂ₘ图、冻结连续算子图60已证。真实Euler/连续/逆权伴随构造给2160dt的L²率及sqrt(466560/c)sqrt(dt)的N_m率，同时证明误差弱jet的MemLp。阈值先于T/网格/两方向/权/τ/所有状态和载荷，ρ保持内禀SmoothOnClosure；连续值只要求a.e.属于D(A)，不加强为每时刻正规性。冻结连续完整R₂ₘ图尚未另行包装。

原域几何新证明从明确Lipschitz图表构造实际内移闭球，再用开有界域闭包紧性得到有限覆盖和统一正高度。它不是Sobolev扩张，也没有证明hI；局部图函数到全局Lipschitz图表的定义等价亦不冒称已证。原域弱Taylor/平均估计仍缺。空间B4误差两系数、最终权族实例仍待；已证B2及普通Γ、原文全离散/两方向/T统一目标均不变。

## T018：原bounded Lipschitz域hI消去与完整一般阶时间范数

本段更新此前T012–T017的“原域插值未证”余额；历史阶段记录保留。详见[数学阶段](analysis/T018-domain-interpolation.md)及[逐声明核对](reviews/T018.md)。C036仍为AUXILIARY，原文完整结果计数1/26不变。

已证明通常局部柱形Lipschitz图表与T017可用global graph接口的双向桥；从实际有限内锥覆盖、原域内弱卷积交换、真实L²平均、内缩穷尽/Fatou、方向组合及有限最大值，得到任意n、所有原域弱Hⁿ jet、全部r≥1的统一参数插值。零延拓仅是L²等距，测试仍在Ω内，不要求零迹、光滑边界、高阶反射或假设扩张存在。`boundedLipschitz_domain_parameter_interpolation`真正清偿hI；`boundedLipschitz_operator_parameter_graph`仅再用正向A1，给原eq:parametergraph的Au版本。

一般m的原域入口现已不要求hI：完整允许权Euler R₂ₘ、完整冻结连续Bochner R₂ₘ、实际时间误差2160δt的L²率和sqrt(466560/c)sqrt(δt)的N_m率。每阶字段先取真实ℓ²/Bochner L²范数再求和；连续jet及误差jet的MemLp均证明。两方向、全状态/任意载荷、T/网格/允许权/τ之前的统一阈值、内禀SmoothOnClosure、a.e.D(A)/H弱导数/周期迹均保留。AllowedWeightData没有插值或目标估计字段。

剩余重点转到Section4：N1–N5下真实空间误差a_E+η_A和a_0+a_E²+η_A、与时间误差的统一权族组合及最终TransferBridges实例。原连续非冻结图及shifted-form完整论文声明仍需整体验收。B2/B3/B5不重复假设，Γ仍是普通函数；原Theorem2.1不宣称完成。


## T019：完整原Section3结论及原假设转移

本段更新T018仍将一般阶时间结果列为组成部分的边界。详见[数学阶段](analysis/T019-section3-closure.md)和[逐声明核对](reviews/T019.md)。新增真正非冻结μ(t)=(Lq(t))²ᵐ的完整加权连续R₂ₘ估计，无网格条件；原域hI由既有几何证明内部给出。实际时间权导数和A2空间交换子分别吸收，无目标估计假设。

原V闭Hilbert实现、原有界双线性形式、完整原D(A)/A识别、原区间q代表和C²正则性、原内禀光滑ρ的有界可测profile均有显式桥。`section3_original_operator`从原D/A及完整变分定义输入，经`domain_eq/operator_eq`转移所有状态；`graph_equation_iff`对任意a.e.D(A)弱代表识别实际方程。不增加逐时刻D(A)、零迹、导数域保持、反向椭圆界或核限制。

`Conclusions`同时包括Lemma3.1任意B的连续适定性、完整R、形式上界与B‖qσv‖²下界，以及Lemma3.3/3.4全解空间适定性和完整R，Theorem3.5任意实际解的δt L²率、sqrt(δt) Nm率和弱误差jet MemLp。两profile及指数范围、两时间方向统一选max阈值/min正δ；冻结方向与演化方向独立，误差使用同向真实延拓与bar g。K在B/L/T/网格/权/状态/载荷之前选择；共同L₀(B)已扩大使L₀(1)支配冻结阈值，可取L₁=L₀(1)、δ_time(L)=δ。`primitive_on_interval`显式以任意T>0陈述，不需要网格限制。

P004/P006/P007/P008在完整同SHA实际构建与审计后登记BUILT/PAPER，等待父监督者独立验收；不会仅因执行者组装而记REVIEWED。B1、B2/B5、规范B3及B4 finite/order/shift继续复用，Γ为普通函数；B4时间部分已按原权族闭合。Section4/N1–N5的空间误差和两误差系数、最终统一transfer实例及原Theorem2.1仍待；原最终全离散/两方向/T统一结论不变。

## T020：Section4空间误差的精确恒等式与全离散适定性

见 [T020 数学阶段](analysis/T020-spatial-identities.md)。C038 为 AUXILIARY：
节点相关自伴测试算子的周期能量恒等式、由真实 Euler 方程相减得到的
`eq:thetaEuler`、保留全部三项的 `eq:completeidentity` 及实际加权 L² 左端，
还有有限维全状态上任意载荷的辅助离散存在唯一性。两时间方向共用同一证明；
不要求 Q²=Q、G=Id、不同节点测试算子交换或正交重构。

N4 时间导数到真实算子差分的估计、superapproximation/coercivity 吸收、
N3 的真实 N/R 范数接入及两种空间误差率仍待。现有对偶恒等式接收满足原方程的
任意对偶解，下一阶段从已证 Section 3 供应它；不把恒等式当作空间误差估计。
原文覆盖不提升，T019 的独立语义验收状态不因合并或 CI 成功而自动改变。
