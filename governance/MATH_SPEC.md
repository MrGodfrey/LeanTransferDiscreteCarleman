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
