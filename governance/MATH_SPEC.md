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

### T020 本机 main 接续：真实空间 Céa 估计

[能量阶段](analysis/T020-spatial-energy.md)更新上一段的待办边界。C039 为 AUXILIARY：原 N4 的实际 qσ 重构质量导数界已给两方向时间负项 18C；真实弱 Sobolev Nm 上的 σ²/逆权乘法统一界、精确误差方程的 Céa 测试及缺陷吸收、N3 逐节点界到实际序列 R 范数的 Minkowski 提升已形式化。

最终空间误差率、状态稳定性、参数统一阈值和完整逆权对偶实例仍待组装。`Section4.spatial_cea` 的 hform/hcoer/hmul 均有此前供应定理，必须在最终原假设入口调用；hsmall 必须由原 hqmax、ηA 阈值证明。此阶段不增加或放宽原假设，也不提升 Lemma4.1/Theorem4.2/Theorem2.1 的覆盖状态。

### T020 完整空间误差：更新上述待组装边界

[完整阶段](analysis/T020-spatial-complete.md)与[逐声明核对](reviews/T020-spatial-complete.md)对应八模块、36 显式声明。`OriginalForm.spatial_uniform` 已实际调用原 Section3 供应形式、任意质量余量与正/逆 Euler 图，并由原 hqmax/ηA 范围构造统一吸收阈值。原 N3/N4、实际两 Euler 方程给能量误差 `aE+ηA`、重构状态稳定性和完整逆权对偶 L² 误差 `a0+aE²+ηA`。所有常数先于 T/网格/qmax/离散空间/方向/符号/全状态及载荷；Q/G 和刚度缺陷均保留，无目标估计新增前提。

C008/P009 是完整 Lemma4.1 候选，精确 main CI 核实后登记 BUILT/PAPER；执行者核对不增加独立 REVIEWED 计数。Theorem4.2 的真实时间延拓/空间误差组合、最终 B4 接口及原 Theorem2.1 仍待，原稿和最终目标没有修改。

## T021：完整原 Theorem4.2 空间—时间误差

[阶段和逐声明映射](analysis/T021-combined-error.md)记录四模块、13 显式声明。`OriginalForm.combined_uniform` 从原解析及数值假设内部构造中间 Euler 解、调用 Section3 时间估计与 Lemma4.1 空间估计，再用真实两方向单元延拓和时空 Nm/Bochner L² 三角，得到原 `sqrt(dt)+aE+ηA` 能量率与 `dt+a0+aE²+ηA` L² 率。完整 V 误差代表与原 U−Rbar z 几乎处处相等，并实际证明全部弱 jet 的 MemLp。

固定公共时间阈值包含 `cellThreshold β (τStar+m) ρ.bound`，较大的解析指数只比较 q 幂密度，不扩大原数值允许权族。所有常数先于 T/网格/qmax/离散化/方向/符号/全状态/载荷。C009/P010 在真实同 SHA main CI 后登记 BUILT，独立本机 Agent 验收后才记 REVIEWED。最终 TransferBridges 的原假设实例与原 Theorem2.1 仍待完成；没有提前清空其额外桥接前提。

## T022 原 Theorem2.1：全部实际桥接清偿

`OriginalForm.transfer_uniform` / `Section5.TransferUniform` 是完整原 Theorem2.1 候选：原 A1 从 OriginalForm 及正向域正则界供应；A2/A3 是原 AllowedFamily；A4 是同一真实弱周期轨迹上的连续 Carleman 估计；N1–N5 是原 NumericalData、质量伴随、普通载荷兼容与稳定右逆。所有原数值类型、T/网格/q/qmax、全状态和两方向后置于共同阈值和常数。

五模块18显式声明完成真实 timeSq/powerSq/graphSq 与 Theorem4.2 范数的精确识别，并从已证原权族 combined 估计构造 ErrorBridge、从真实非负冻结连续解构造全部 TransferBridges。最终入口内部调用 Section4 全部结论，不再输入任何 B1–B5 桥接、误差、插值或有限性假设；原 Λf/Λz、εE/ε0 和载荷/残差两版结论不变。详见 `analysis/T022-original-transfer.md`。C010/P001 仍需同 SHA CI 与独立本机 Agent 验收后才计入原文完成；历史条件性接口 C004 继续保留其范围作可复用定理，不冒称其单独证明原 Theorem2.1。

## T023：原尺度推论入口（等待固定版本独立验收）

`OriginalForm.scale_uniform` 和 `OriginalForm.heat_scale_uniform` 返回原两版完整估计，内部从原近似阶与 qmax 尺度推出全部小量和缺陷条件，并调用原 Theorem 2.1。零分母用省略规则；正指数由 κ、零指数由 h0/Δ0 控制。热方程最终尺度是 h^(−4/5)、dt^(−2/5)。参数和原文逐项映射见 `analysis/T023-original-scales.md`；未引入新的误差或桥接前提。

## T024：原物理时间基础引理（等待固定版本独立验收）

`Physical.physical_duality_lemma` 对原N+1物理节点和N控制步，从Section7的有限维非负自伴刚度、范数≤M的自伴势、范数≤1的控制算子给出完整初末值唯一解、精确反向指数界、统一C(T,M)控制L2能量界及原p^(n−1)对偶。最终方程保留真实Hilbert伴随；不存在周期回绕或状态限制。具体有限元/差分实例仍须各自验收。映射见 `analysis/T024-physical-duality.md`。

## T025：原滤波反向界（等待固定版本独立验收）

`Physical.filter_reverse` 从真实物理伴随方程和原非负刚度/有界势，证明原Lemma7.4的 `exp(TΛ_F+MT+M²T²/2)` 反向范数界。Λ_F为原非零子空间向量Rayleigh商的真实上确界；不要求A或势保持F。Rayleigh单步增长和正算子逆界均在内部证明。详细原文映射见 `analysis/T025-filter-reverse.md`。
## T026：真实物理 HUM 条件桥

范围保持 CONDITIONAL，不计原 Theorem 7.3 完成；仍缺原 Theorem 7.2 的统一观测估计及其具体实现依赖。

`PhysicalFlow` 用原有限维步映射的真实逆构造全部 N+1 个伴随节点，定义终值到初值的连续线性映射 R，以及到 `PiLp 2 (Fin N → U)` 的观测映射 O。O 的第 i 项为 `sqrt(dt) • B.adjoint p^i`，其范数平方严格等于原观测离散积分；R 单射及原能量上界均由已验收 Lemma 7.1 推出。

`PenalizedHUM` 从真实正算子 `O.adjoint.comp O + ε² id` 的有限维双射直接得到唯一最优性方程，无需把极小点或目标控制当作输入。显式松弛观测 `‖Rz‖² ≤ C(‖Oz‖²+ε²‖z‖²)` 推出控制范数 `≤sqrt(C)‖y0‖` 和真实对偶终值余量 `≤ε sqrt(C)‖y0‖`。

`PhysicalHUM` 对真实控制序列使用 sqrt(dt) 加权嵌入及逆缩放，精确证明物理终值等于 `R.adjoint y0 + O.adjoint controlVector(u)`，并由真实初值问题存在性产生整个前向解。`RelaxedControl.relaxed_control_of_observation`（完整名称 `Carleman.Physical.relaxed_control_of_observation`）在原非负自伴刚度、有界自伴势和真实 Hilbert 伴随方程下，取 ε=exp(-dS)，输出原前向方程及两条控制结论。C、d、S 为显式参数；没有证明它们满足原网格与权函数构造要求。

独立验收应覆盖全部显式声明、dt 权重、p^(n−1) 的时刻、真实伴随与终值识别，以及最后入口仍保留的观测假设。不得将该条件桥提升为 PAPER，也不得认为其提供原观测定理。
## T027：原物理观测的周期权与具体截断基础

范围为 AUXILIARY；原 Theorem 7.2 的空间加权范数、势载荷与具体 P1/FD 及连续热 Carleman 供应仍未完成，不能将本阶段计为完整观测定理。

八个 `Control/Physical*` 模块完成原 `q(t)=qb/sqrt(sin²(πt/T)+δ²)` 的实际光滑函数：正分母、全时上下界、周期性、真实一二阶导数及准确比界 `π/(qb T)`、`4π²/(qb² T²)`。`physicalTimeWeight` 与 `physicalTimeWeightRegularity` 接到既有允许权接口；二阶公式通过 `HasDerivAt` 和实际 `deriv (deriv q)` 识别，首阶导数周期且端点为零。

证明路线采用显式 Lipschitz 截断 `clipUnit((min(t,T−t)−a)/a)`，a=δT。原证明仅用其节点取值、边界消失、中央等于一及差商界，故无需截断本身光滑。该替换不改原论文，也不改变最终陈述。形式化证明其值在[0,1]、在距端点≤a处为零、距端点≥2a处为一、差商≤1/a。N+1个物理节点截断后准确连接周期 N 节点，保留 `D_- z + A z = -Vz-r` 的原符号与真实 r。没有将伴随轨迹本身周期化。

对实际节点作整数计数，左右窗口测度各≤b+dt；dt≤T/12时中央三分之一测度≥T/6。过渡区域采用安全的 `5a` 上界（原稿更精细为3a），仅放大可选择的绝对常数，不改变 S 指数或统一性。真实伴随能量给出 `dt Σ‖r‖² ≤ (5/a)exp(4MT)‖pN‖²` 和中部初值恢复 `(T/6)exp(−4MT)‖p0‖² ≤ dt Σ_middle ‖pi‖²`；这些仍是未加空间权的中间界。

`physical_delta_conditions` 直接从 qb≥2、16qb≤S≤qb T/(4dt) 给出δ>0、δ≤1/16、qmax=S、截断宽度和dt≤a/4。`physical_transition_weight` 对真实差商非零节点证明原 `q_i≥S/sqrt(1+9π²)`，`physical_weight_endpoint_decay` 对任意ρ≤−ρstar证明原端点指数 `exp(−(2ρstar/sqrt(1+9π²))S)`。中央 q≤2qb 也已从真实正弦函数推出。

后续须把这些点态和未加权结果接到实际空间加权 seminorm、具体势载荷与 Theorem 2.1，选择统一 Cb 并完成潜势吸收、观测上界及指数余项吸收。不能把这些尚待条件隐藏在一个命名为原观测定理的接口中。

## T028：完整原权条件和实际空间加权预算

本阶段仍为 AUXILIARY，不计原 Theorem 7.2 完成。`physicalBaseAmplitude` 严格采用原 `Cb(qc+T⁻¹+M^(2/3))`，证明 qb≥Cb qc、qb T≥Cb、qb³≥Cb³M²；M=0 也包含。`physical_qclass_uniform` 对任意固定 Cmin 选择 Cb=max(2,max(2π/β,Cmin))，量词先于 T/M/网格/S。实际返回原正弦权、qmax=S 和完整 `PhysicalQClass`：全局光滑代表、qc 下界、实际 deriv/deriv² 的 β/β² 界、0/1/2 阶端点匹配，另接既有一阶 TimeWeightRegularity。可把 Cmin 留作后续潜势吸收预算，不需要改变 q 的选择。

`PhysicalSpatialWeights` 对真实 Lp 乘法 seminorm 给出 exp(-ρstar q) 上包络和 exp(-ρ.bound q) 下包络；原过渡节点得到 exp(-c_end S) 平方界，中央节点得到 exp(-4ρ.bound qb) 平方下界。`PhysicalExponentialBudgets` 证明 q³ exp(-2ρstar q)≤6/ρstar³ 及 S exp(-cS)≤(2/c)exp(-cS/2)，并作用到真实空间观测范数。

`PhysicalWeightedEnergy` 对真实 N+1 伴随轨迹及具体 χ/r，显式保留重构 R 的原始未加权质量比较。上界输入 ‖Rx‖²≤Cmass‖x‖²，输出真实加权余项积分，随后吸收 S 得 `(10 Cmass/(c_end qb T))exp(4MT)exp(-c_end S/2)‖pN‖²`；下界输入 ‖x‖²≤Cmass‖Rx‖²，输出中央初值控制整个真实周期加权 q³ 能量。χ=1 的中央节点、过渡外 r=0、原伴随能量和离散窗口测度均在内部调用。没有把目标观测不等式、空间指数包络或余项指数界作为输入。

尚待具体重构质量界实例、势载荷与右逆的加权界、原 Carleman 供应、潜势吸收和统一最终组装；连续热 CE、具体 P1/FD 也未被本阶段证明。独立验收应核对全部22项声明及上述范围，不提升 P014。

## T029：实际周期载荷 CE 到物理观测的条件桥

范围为 CONDITIONAL，不能提升 P014 / 原 Theorem 7.2。五模块20声明直接构造 `-b_i.map(R z_i)-I r_i`，在 Lp 等价类上用实际有界乘法证明势载荷的加权界，实际 Γ 兼容给原负号方程。载荷平方界为 `2M²‖θRz‖²+2CI²‖θRr‖²`；M=0 保留。

`PhysicalLoadCarleman` 明确是整个周期状态/载荷空间上的实际 q³ Lp 重构能量估计，输入真实 `D_-z+Az=Γf`，右侧为实际载荷与 Bstar 观测能量。本阶段仍没有从具体 P1/FD 或连续热 CE 供应它。`cutoff_carleman_absorb` 对实际截断轨迹和构造出的载荷应用此 CE；`physical_potential_budget` 从原 qb 公式及 `Cb≥max(1,32CCE)` 推出半能量吸收，所有网格/轨迹后的目标预算均内部清偿。实际 χ∈[0,1] 与真 Bstar 线性、空间指数包络给 `cutoff_observation_budget`。

`physical_observation_of_load_carleman` 将真实加权端点余项、中部初值恢复、势吸收与观测去权合成。常数显式定义为 `Cmass/K * (4CCE CI² Kremainder + 2CCE (6/rstar³)+1)`，其中 K 是正的中部恢复因子，Kremainder 不含S/网格。`physical_observation_uniform_of_load_carleman` 先选择 Cb≥max(2,32CCE,2π/β) 和 d0=c_end/4，再对 T>0、M≥0 选择正 C(T,M)，最后量化所有X、网格、S、算子、数据和全伴随轨迹。原正弦q、完整qclass、半能量预算和原势二次型下界均在内部产生；不把目标观测作为输入。输出指数严格为 exp(-2d0 S)，观察时刻为 p^i（原 p^(n−1)）。

显式待供应项：统一周期实际Lp载荷CE、重构双向质量界、Γ/I与乘法势的兼容、允许权下I的稳定性，以及 Bstar 实际数值观测到这里Lp观测的等距/有界接口。尤其 Bstar 当前是显式线性观察映射；不能仅凭名称认定它已是原控制算子的Hilbert伴随。原A/V自伴、A非负及势算子范数界在最终入口保留，真实物理 Hilbert 伴随方程不变。本阶段既不声称原具体数值条件已实例化，也不声称原连续热CE已证明。独立Agent应按该精确条件范围验收。

## T030：真实 L2 子空间及 L2(ω) 控制接口

五模块32显式声明。范围为 CONDITIONAL；本阶段清偿真实正交L2子空间的质量/势/载荷/控制伴随接口，仍需原具体 P1/FD 网格实现和统一周期载荷CE，不能提升P014/P015或Prop6.1/6.2。

X为真实完备（最终控制入口为有限维）L2子空间，R=I为包含映射，Γ为正交投影；双向质量界和加权I界均以常数1实际证明。`conformingPotential X b=Γ b R` 采用真实有界乘法算子，证明其自伴、算子范数≤b.bound、准确双线性积分形式和Γ载荷兼容。任意非负自伴刚度A仍是显式输入，没有假称已构造具体热刚度矩阵。

`restrictRegionLp/Linear/CLM` 实际把Lp(ν)限制到Lp(ν.restrict ω)，在a.e.商空间上证明线性和收缩。已有真实零延拓的等距性与新的积分恒等式共同证明限制算子的Hilbert伴随就是该零延拓；限制后再零延拓等于真实indicator乘法。`conformingRegionControl` 定义为Γ复合零延拓，控制空间真正是L2(ω)。其实际Hilbert伴随是限制复合R，范数≤1，双线性配对恰为区域积分；与中间环境Lp观察算子的范数严格一致。空/零测度ω也包含，未添加正测度条件。

`conforming_observation_control_uniform` 从显式统一周期 `PhysicalLoadCarleman` 输入出发，内部构造全部物理接口并调用已验收观测桥和HUM，输出真实B.adjoint的全轨迹观测以及L2(ω)中的实际控制、原前向方程、控制预算和指数终值余项。Cb/d0先于T/M，C(T,M)先于有限维X/网格/S/A/b/轨迹/初始数据，原qb与尺度双边条件不变。代价写sqrt(C)，与原可重新命名的正C(T,M)等价。

周期CE输入暂采用与区域加权观察等价的环境L2 indicator形式。具体有限元数值几何、原完整离散能量到这条载荷CE的供应、连续热CE及原网格阈值仍待，不因这里的真实控制算子构造被视为完成。

## T031：原热尺度推论到真实物理观测/控制

四模块15声明，范围CONDITIONAL，不提升P014/P015。`PhysicalTransferGeometry`把完整热能量的c0=o=3与实际q³和dt有限和精确识别，只舍弃非负导数能量；minus方向与真实Γ载荷方程不变。`conformingReconstruction/conformingLoad`对X≤V的实际L2子空间内部构造包含、正交质量伴随、Γ和恒等普通lift；真实乘法状态seminorm的正定性内部证明。

`ConformingHeatData`显式打包原AllowedFamily、NumericalData和实际弱周期轨迹上的连续A4；不含离散CE、误差桥或物理观测。`conforming_heat_load_uniform`内部调用已验收原`heat_scale_uniform`，从原误差阶aE≤Cap*h、a0+ηA≤Cap*h²与原4/5、2/5尺度供应实际周期载荷CE。κ/h0/Δ0/CCE先于所有数值空间、T/网格、权和状态。

`conforming_heat_observation_control_uniform`进一步内部供应此前显式的周期CE，输出真实L2(ω)控制伴随观测和HUM控制/完整前向解。κ/h0/Δ0/Cb/d0先于T/M，Cphys(T,M)先于X/网格/刚度/误差/势/轨迹/初值；Smax严格等于κ min(h^(-4/5),dt^(-2/5))，原物理尺度条件全部保留。调用者仍须对完整PhysicalQClass权族提供原数据；具体P1网格、连续热CE和Dirichlet实现尚未构造，FD的不同质量/重构另需实现。详见`analysis/T031-original-physical-transfer.md`。

## T032：实际Galerkin刚度与原数值接口

四模块16声明，CONDITIONAL；不提升Prop6.1或P014/P015。对真实有限维L2子空间X≤a.V，以原形式拉回到X再用实际L2 Riesz逆构造`galerkinStiffness`，其精确配对、自伴、非负、唯一及零刚度缺陷全部是结论。有限维能量提升的连续性只用于定义算子，没有把其随网格变化的范数混入统一常数。

重构单射、G=Id、Q=正交投影、实际加权观察识别已证明；`galerkinNumericalData`内部供应原N1/N2/N5相关全部字段，质量/载荷/观察常数均为1。仅N3加权近似和N4测试仍由调用者提供，实际零刚度缺陷允许ηA=0。`GalerkinHeatData`显式保留原A2/A3、N3/N4和连续A4，不含离散CE或物理观察。

`galerkin_heat_observation_control_uniform`内部选取真实刚度及其自伴非负证明，不再输入任意A/defect或相关算子假设；原κ/h0/Δ0/Cb/d0先于T/M，Cphys先于全部数值数据。原尺度、全物理轨迹、真实区域控制伴随和前向方程不变。仍未构造具体P1网格及其N3/N4、连续Dirichlet热CE；不能以此提升具体实现覆盖。详见`analysis/T032-galerkin-physical.md`。

## T033：原投影加权测试及统一时间界

五模块20声明，CONDITIONAL，不提升P011/P014/P015。对真实L2子空间X，F(t)=σ(t)R，`galerkinWeightedTest=F.adjoint F`精确等于原Π_X(σ²z)；加权配对、二次型能量恒等、对称非负与周期端点均证明。时间导数候选为F'.adjoint F+F.adjoint F'；使用已证明的实际算子范数乘法导数，证明原N4所需整个闭区间的真实二次型HasDerivWithinAt。

对真实加权状态使用对数导数乘子界，推出`|<z,T'z>|≤2β(|τ|+ρ.bound)(q‖σz‖)²`，再得统一`Ctime=2β(τStar+ρ.bound)`；该常数不含T、X、维数、h、dt或qmax，不需要加权投影稳定性。两符号空间权具有同一bound。

`GalerkinSuperapprox`只保留原特定Π_X(σ²z)的空间超逼近，原V中双乘法保持条件、逆权范数和Csuper*h*qmax不变；`galerkinWeightedTestData`内部构造N4其余全部字段。`ProjectedHeatData`保留原Allowed、N3、空间超逼近和连续A4；最终`projected_heat_observation_control_uniform`内部指定上述时间常数与真实测试，原物理结论和先置常数不变。具体网格的近似/超逼近及连续Dirichlet热实例仍待供应。详见`analysis/T033-projected-weighted-test.md`。

## T034：插值误差到原投影近似和超逼近

六模块25声明，CONDITIONAL，不提升P011/P014/P015。实际正交投影误差分解将插值的L2/能量误差和加权投影稳定性、逆估计转换为原N3；特定Pi(sigma²z)的空间N4从实际双乘法插值误差推出。热m=1采用实际唯一弱梯度场，逐点q|σ|≤|ζ|将原梯度加辅助L2预算转为真实Nσ；未假称ζ已是具体ell⁻¹σ。

精确误差aE=(CE+(1+CI)Cp CE)h、a0=(1+Cp)C0h²、ηA=0，统一Cap取两个系数的max；超逼近Csuper=CS+(1+CI)CpCS，均不从T/X/mesh/qmax选择。最终`interpolatedHeatNumericalData`对全部两符号和允许τ内部供应原N1–N5，实际时间测试由T033构造。具体网格/加权投影稳定性/插值/逆估计仍为显式未供应局部输入，连续Dirichlet热实例也未完成。详见`analysis/T034-projection-errors.md`。

## T035：实际分片仿射L2空间与Galerkin刚度

三模块24声明，AUXILIARY，不提升P011/P012。有限可测有界单元的实际indicator乘常数/坐标函数生成真实Lp类，有限系数线性像给分片仿射空间并证明有限维性；构造用界R不改变该空间。在a.e.分区（可含零测度共享边界）上，range与逐单元仿射多项式的a.e.刻画完全等价。

与原V取交给实际一致空间，包含V及有限维性均内部证明；在该空间上构造真实Galerkin刚度并给准确形式配对、对称、非负。没有假定任意X的有限维性，也没有把Lp代表点值当节点值。实际网格、V=H01及Dirichlet热实现、稳定性/局部插值仍待。详见`analysis/T035-piecewise-affine.md`。

## T036：实际单纯形分区与局部节点插值

三模块30声明，AUXILIARY，不提升P011/P012。实际有限顶点凸包的凸/紧/可测/边界零测及显式顶点和半径内部证明；真正非退化d单纯形内部非空。覆盖加内部不交推出受限Lebesgue测度的a.e.分区。`SimplicialPartition`用真实Simplex并记录inside/cover/disjoint，供应实际一致分片仿射空间及有限维/成员刻画，但不声称面匹配、形状正则和分级已证。

真实AffineBasis重心坐标给局部节点插值：顶点值精确保持、全空间再现仿射多项式、单元内L∞稳定常数1。仅输入实际点值数组/仿射函数，未在Lp类上赋予节点值。全局连续/H01插值、Sobolev点值、局部误差及具体网格均待。详见`analysis/T036-simplicial-nodal.md`。

## T037：面匹配全局连续节点插值

三模块30声明，AUXILIARY，不提升P011。真实FaceMatching几何条件经共同顶点仿射包一致性给局部插值共享面一致；有限闭覆盖给closure S上连续，全局节点保持、仿射再现、唯一性、幂等与常数1节点稳定已证。实际toLp属于分片仿射空间，并构造点态函数到L2的真实LinearMap；从未在Lp等价类上取节点值。见`analysis/T037-global-nodal.md`。

## T038：节点插值的实际弱导数与H1

八模块39声明，AUXILIARY，不提升P011。实际局部AffineMap的CLM导数经内部邻域等值给全局a.e.经典导数；零测骨架与有限indicator和给真实L2导数字段。BoundaryFitted要求边界单元交由边界顶点生成，边界节点零推出全局连续零延拓。有限个同常数Lipschitz函数的连续选择仍为同常数Lipschitz，经局部排除与直线段liminf斜率论证证明；实例化实际局部仿射函数及零函数，得原零延拓全局Lipschitz。

实际差商积分分部推出对全部SpatialTest及任意方向的原弱导数身份；坐标导数组装真实WeakSobolevJet，value准确等于nodalLp，故进入原sobolevSubspace H1。所用Lipschitz常数可依赖网格/节点值，仅为成员证明，不是统一逆界。H01闭包身份、H2连续代表、局部误差、具体网格和连续Dirichlet热实例仍待。见`analysis/T038-nodal-h1.md`。

## T039：全空间零延拓H1与Dirichlet闭包空间

五模块27声明，AUXILIARY，不提升P011。实际节点函数及其逐片CLM导数在全空间volume下的Lp类、a.e.导数和完整弱H1身份均内部证明，有限体积由真实紧单元供应。原全部SpatialTest也构造真实fderivLp与H1 jet，value精确恢复测试函数Lp类。

Dirichlet空间定义为这些紧支光滑jet的线性张成在真实H1图范数下的闭包，再经value实现为标量L2子空间；证明包含于H1、包含全部测试、开集上在H1中闭合且在L2中稠密。未把连续零边界直接等同于H01闭包；节点插值的H01成员、Poincare/实际梯度形式和数值估计仍待。见`analysis/T039-dirichlet-closure.md`。

## T040：实际H01上的Poincare与Dirichlet梯度形式

四模块27声明，AUXILIARY，不提升P011。原完整光滑测试的线性运算和真实jet身份使span每个元素仍为单个测试。以L(x)φ(x)作测试，准确乘法导数及弱积分分部推出slab Poincare；真实value/gradient的连续性把估计传到H1闭包，未预设目标估计。

实际全梯度L2内积给连续对称Dirichlet形式，积分准确包含全部一阶分量。能量范数精确为零阶加梯度平方，Poincare给强制常数((2R)²+1)⁻¹；有界开集内部供应坐标slab，实际构造Lean OriginalForm的全部字段，仅对应原A1的空间与形式部分。原A1另要求的H2椭圆正则性尚未清偿。没有添加零阶质量项。节点H01成员、H2算子域/正则性、数值估计及连续热CE仍待。见`analysis/T040-poincare-dirichlet-form.md`。

## T041：Dirichlet算子的实际负Laplacian与完整分布图

四模块20声明，AUXILIARY，不提升原文覆盖。真实梯度Lp内积精确展开全部坐标一次，负Laplacian是实际H2 jet的纯二阶和之负值。完整弱导数身份给光滑测试Green恒等式，经H1闭包传至全部H01测试；由准确一阶截断构造能量元素，证明H2∩H01进入原实际形式算子域且operator=-Δ。

完整变分算子图双向等价于真实H01 jet满足对全部SpatialTest的分布-divgrad=f，未引入H2/谱截断等额外域限制。反向H2正则性和原域等式仍未证明；节点H01、H2点值、网格数值估计及连续CE仍待。见`analysis/T041-dirichlet-laplacian.md`。

## T042：凸域内缩、正支撑缓冲与实际H1构造

三模块24声明，AUXILIARY，不提升原文覆盖。真实centeredDilation及其逆映射构造原函数的内缩；开凸域中心与closure S的严格凸组合进入S，紧支集正向像给精确tsupport及正卷积缓冲。实际Fréchet链式导数与Lipschitz常数均证明。

全空间紧支Lipschitz函数的真实fderiv由紧支indicator控制进入L2，Rademacher和已证完整积分分部给真实WeakSobolevJet。零边界实际节点函数据此构造内缩H1 jet，value准确恢复同一内缩函数。尚未证明r→1的H1收敛或光滑卷积的H1收敛，故节点H01成员仍待；缓冲可依赖函数/中心/r，不是统一网格常数。见`analysis/T042-contracted-nodal.md`。

## T043：实际节点内缩的强H1收敛

四模块18声明，AUXILIARY，不提升原文覆盖。实际Lp平方范数积分和支配收敛给任意normed目标的强L2极限，共同紧支及统一函数/Lipschitz界给实际紧支Lipschitz jet的完整H1图拓扑收敛。

具体r_n=(n+1)/(n+2)内缩，逆像点趋于x；在实际单元内部导数为固定CLM，closure S外局部为零，有限零测骨架外真实fderiv收敛。支撑共同位于紧closure S，Lipschitz常数≤2C，故内部供应全部条件，实际nodalContractedSobolevJet趋于原nodalGlobalSobolevJet。C可依赖网格/节点值，仅用于极限。光滑卷积H1极限和最终H01成员仍待。见`analysis/T043-nodal-contraction-limit.md`。

## T044：真实光滑逼近与节点H01成员

五模块30声明，AUXILIARY，不提升原文覆盖。实际非负单位质量核卷积保持全局界/Lipschitz常数且有准确厚化支撑；完整弱积分分部证明实际fderiv(κ⋆f)=κ⋆fderiv f。Lebesgue微分和共同紧支界给真实光滑卷积的完整H1强极限。

真实Lp字段逐项限制保留全部弱导数身份及H1图拓扑收敛。紧含于开S的Lipschitz函数以实际SpatialTest逼近而进入原Dirichlet闭包，再由节点内缩H1极限和闭性，证明实际nodalLp属于H01及实际一致P1空间；最终单独处理空域，不预设零边界等于H01。公开几何为开凸域、FaceMatching/BoundaryFitted及边界顶点值零。H2点值/正则性、统一加权误差/投影和连续热CE仍待。见`analysis/T044-nodal-dirichlet.md`。

## T045：真实单纯形L2系数与参考逆估计

两模块15声明，AUXILIARY，不提升原文覆盖。真实单纯形上节点多项式的Lp类线性；连续多项式a.e.身份、开集正测度及单元内部稠密性恢复实际全部节点系数，故该映射单射。有限维反Lipschitz界内部供应正常数B(T)先于全部系数。

真实重心仿射坐标的CLM导数给实际节点多项式Fréchet导数，全坐标一阶fiber的真实L2类线性。该实际映射算子范数与系数反界给固定单纯形逆估计，正常数C(T)先于全部节点系数。尚未证明仿射缩放及形状正则族的统一h_K逆界，也未供应原加权逆估计；原文12/26。见`analysis/T045-reference-inverse.md`。

## T046：真实仿射换元与形状控制局部逆估计

六模块28声明，AUXILIARY，不提升原文覆盖。真实F(x)=Ax+b与J=|det A|>0给限制Lebesgue测度和积分换元；实际单元像、节点多项式复合身份及Fréchet链式法则给精确函数/梯度缩放。全坐标fiber范数比较与真实L2平方积分消去同一Jacobian，得到固定T的全部仿射像统一C(T)‖A⁻¹‖逆界。

真实内球ball(a,r)包含于物理单元时，以其两点逆像和参考单元界R内部推出‖A⁻¹‖≤4R/r。h≤κr给最终C(T,κ)/h，常数先于全部A/b/a/r/h/c。尚待把任意物理单纯形实际参数化为固定T的像，并完成原全网格加权逆估计；其他P1误差/投影/连续CE义务未清偿，原文12/26。见`analysis/T046-affine-inverse.md`。

## T047：所有单纯形的统一局部加权逆估计

两模块11声明，AUXILIARY，不提升原文覆盖。任意T/U的顶点差线性基给真实连续线性等价，准确平移使全部顶点映射，从而清偿所有物理单纯形的共同参考参数化。参考单元只依赖维数，形状常数C(n,κ)先于所有单元/尺度/系数。

实际单元乘子满足|w|≤Ws及s≤W|w|时，真实L2范数比较使归一化s精确消去，得到C(n,κ,W)/h的局部加权逆界，常数先于权/单元/多项式。另给任意实际AffineMap及其真实L2/梯度代表形式与完整积分形式。完整Vh的局部弱梯度识别、全网格求和、allowed权族比较和其余P1义务仍待；原文12/26。见`analysis/T047-weighted-simplex.md`。

## T048：完整一致P1状态的真实局部弱梯度

四模块20声明，AUXILIARY，不提升原文覆盖。任意子域的实际L2字段限制保留全部SpatialTest弱身份与任意阶完整jet。真实仿射函数的CLM导数和Lipschitz积分分部构造方向弱导数，完整测试唯一性识别任何实际H1 jet的全部一阶fiber。

开凸S中cell⊆closure S给interior cell⊆S，空域单独处理；真实零测边界使闭单元和内部受限测度相同。局部限制和仿射唯一性证明任意H1状态在闭单元上的实际梯度身份。原完整conformingSpace成员刻画给真正AffineMap p及其value/梯度a.e.公式，不需节点表示、FaceMatching或额外状态限制。全网格求和、allowed权比较及其余原P1依赖仍待，原文12/26。见`analysis/T048-local-gradient.md`。

## T049：完整一致P1空间的全域加权逆估计

三模块9声明，AUXILIARY，不提升原文覆盖。真实有限a.e.唯一分区与闭单元零测边界给全域积分精确求和；实际分片逆尺度乘子有单元a.e.公式，实际加权L2平方准确等于单元逆尺度平方积分之和。

完整H1一致P1状态的实际局部多项式／梯度身份与统一局部逆界给真实全域加权逆估计。正常数C(d,κ,W)先于全部域、网格、尺度、权及状态；不假设节点表示。仍显式要求内球形状控制和单元权比较，原allowed权族比较与原ℓ尺度对应及其余P1义务仍待；原文12/26。见`analysis/T049-global-inverse.md`。

## T050：原允许权族的完整一致P1逆估计

四模块20声明，AUXILIARY，不提升原文覆盖。固定C1 profile在紧凸闭域上的真实导数界供应统一空间Lipschitz常数；实际q^τ exp(±qρ)比值精确消去q^τ，得到两符号／所有τ的空间比较。定义真实单元直径及最大直径，hq≤1给统一单元常数exp L；hqmax条件推出全时刻条件。

原ℓ_K≤B diam(K)与真实内球形状比diam(K)≤κr_K供应ℓ_K≤Bκr_K。把以上内部证明的条件接入全域逆界，得到原eq:p1-weighted-inverse，C先于全部网格、权、时刻、τ、符号及完整H1一致P1状态。加权投影稳定性、H2插值／超逼近及其余P1与连续分析义务仍待，原文12/26。见`analysis/T050-allowed-inverse.md`。

## T051：原四类权的统一邻接分级

四模块16声明，AUXILIARY，不提升原文覆盖。实际共享顶点给邻接点距离≤2h；原正ℓ双侧比值控制给逆尺度因子的邻接比较。真实σ反演准确改变τ及符号，实际分片逆尺度在单元a.e.的身份给四类权的γ exp(2Lhq)分级。

定义并核对实际Γ_d及d=2、3数值，构造正常数δ≤1，使γ exp(2Lδ)≤(γ+Γ_d)/2<Γ_d。固定光滑profile内部供应L；hqmax≤δ给四类实际权全时刻统一分级，δ先于全部网格、尺度、权、τ、时刻及符号。由此到实际L2投影稳定性的DST证明仍待，原文12/26。见`analysis/T051-neighbor-grading.md`。

## T052：P1加权系数二次型的强制性

单模块9声明，AUXILIARY，不提升原文覆盖。有限系数型Σc_i e_i+(Σc_i)(Σe_i)在e_i=ω_i²c_i时，由真实偏差界与有限Cauchy–Schwarz得到下界μ(d,γ)Σ(ω_i c_i)²。原1≤γ<Γ_d严格推出μ=1−(d+1)(γ−1)²/(4γ)>0；任意局部正归一化a≤ω_i≤γa具有同一μ。

这里只证明完整代数引理，尚未识别该型与真实单元积分，也未证明实际L2投影稳定性。真实重心坐标矩、完整Vh节点对应和节点测试构造仍待；原文12/26。见`analysis/T052-coefficient-coercivity.md`。

## T053：真实重心坐标分布及一阶矩

单模块7声明，AUXILIARY，不提升原文覆盖。实际重心坐标与homothety作用公式给K∩{λ_i≥t}在0≤t<1时是顶点中心、比例1−t的真实缩放像。真实Lebesgue缩放定理给分布体积(1−t)^d volume(K)，并正确换成单元受限测度的real值。

非负坐标和为1给λ_i≤1；紧单元连续函数可积及实际layer-cake／区间幂积分给∫Kλ_i=volume.real(K)/(d+1)，端点1只按零测排除，含d=0。二阶矩、真实一致质量积分身份及完整投影稳定性仍待，原文12/26。见`analysis/T053-barycentric-distribution.md`。

## T054：真实二阶矩与一致 P1 质量积分

四模块19声明，AUXILIARY。真实layer-cake、顶点置换的实际Jacobian换元和非空内部给完整二阶矩：对角2 vol(K)/((d+1)(d+2))、非对角vol(K)/((d+1)(d+2))。真实有限双和积分得到∫K p_c p_e等于该体积因子乘p1CoefficientForm c e；真实平方积分有系数平方和的上下界，比例d+2。

T052强制性因此提升为真实单元积分估计，原阈值内非零c给∫K p_c p_(ω²c)>0；体积、局部权归一化和任意正负系数均准确保留。节点权与原实际四类权对应、完整Vh节点表示/测试及全域投影稳定性仍待，原文12/26。见`analysis/T054-simplex-mass-integral.md`。

## T055：原四类权的节点权构造与全域节点测试

四模块16声明，AUXILIARY。每个几何顶点的共享节点权取实际相邻单元正样本最小值，单元范围a_i/θ≤ω节点≤a_i保持局部分级θ。原四类权的样本使用实际指数权顶点值与明确单元因子；实际分片权只按单元a.e.身份比较，避免共享边界求和值混用。

固定profile和原γ<Γ_d内部供应统一δ与θ=(γ+Γ_d)/2<Γ_d，适用于全部网格、尺度、时刻、τ、符号及两类分片因子。节点平方加权零边界数据供应真正H¹₀一致P1测试，真实单元强制性可求和为全域节点状态的L²内积估计。完整Vh节点表示及最终加权投影仍待，原文12/26。见`analysis/T055-uniform-nodal-weights.md`。

## T056：真实加权范数与保留节点表示前提的统一投影界

六模块18声明，AUXILIARY。真实单元质量上界和实际分片积分给状态／节点平方权测试的全域加权范数界θ⁴(d+2)E及θ²(d+2)E。真实互逆有界乘子的L² Cauchy–Schwarz、正交投影测试与μE强制性推出投影范数常数θ³(d+2)/μ。E=0独立处理，正能量消去合法。

对原四类实际权内部构造有界倒数乘子，按单元／全域a.e.证明互逆，统一δ及θ=(γ+Γ_d)/2<Γ_d供应全部权比较。δ、C先于全部网格、权、时刻和输入。最终使用真实完整空间的正交投影，但显式保留该输出等于nodalLp f和边界节点f=0；完整Vh表示尚未证明，因此原投影结论仍不升级，原文12/26。见`analysis/T056-nodal-projection-estimate.md`。

## T057：完整 H¹₀ jet 的真实全空间零延拓

两模块8声明，AUXILIARY。域内紧支撑光滑状态与全空间测试的真实积分分部，通过H¹ jet拓扑闭包传递到完整H¹₀状态；由此实际L²零延拓在全空间的弱导数恰为原弱导数的零延拓，没有额外边界项。分量提取与零延拓交换，逐字段构造完整全空间H¹ jet，其标量值、各阶L²范数与限制回原域身份均已证明。

仅需开域和真实H¹₀闭包成员条件，不预设连续代表、节点表示或网格条件。完整一致P1空间的全局节点表示及零边界数据仍待；原文12/26。见`analysis/T057-dirichlet-zero-extension.md`。

## T058：完整一致 P1 空间的节点表示与原四类权投影界

四模块10声明，AUXILIARY。真实有界全空间弱梯度经光滑卷积、统一Lipschitz界及实际a.e.极限供应连续代表。完整H¹₀分片仿射状态的局部真实常梯度及零延拓满足该条件；连续代表在所有闭单元等于其仿射多项式，在域补集及边界为零。因此任意完整conformingSpace成员都有真实nodalLp表示及零边界节点数据，清偿T056显式前提。

allowed_weight_full_projection对原完整空间的实际L²正交投影成立，覆盖全部四类真实权和任意输入；δ/C先于网格、尺度、时间权、幂、时刻与输入，代表构造的网格/状态相关Lipschitz常数不进入统一估计。原eq:p1-weighted-projection已证明；完整prop:p1仍需H²插值及超逼近等义务，原文12/26。见`analysis/T058-full-weighted-projection.md`。

## T059：经典导数控制下的真实节点插值误差

三模块13声明，AUXILIARY。实际仿射内球导数界和节点插值仿射再现给误差2R及G+4R/r。真实一阶Taylor仿射多项式与凸集均值定理，在Df为L-Lipschitz时给单元节点函数误差2Lh²、梯度误差(1+4κ)Lh；真实内球与h≤κr显式保留。积分通过实际连续性/可积性得到带真实单元体积的平方误差界，并使用项目真实Euclidean一阶fiber。

真实二阶Fréchet导数的点态界可供应Df的Lipschitz性。此阶段只对经典导数满足这些条件的函数成立，未以此代替一般H²弱状态的原插值结论。允许权平方乘P1状态的导数控制及加权超逼近仍待；原文12/26。见`analysis/T059-classical-nodal-errors.md`。

## T060：闭单元内在导数与真实权乘仿射插值误差

两模块13声明，AUXILIARY。真实HasFDerivWithinAt连接函数与导数字段，在闭凸单元内部完成Taylor及节点误差2Lh²/(1+4κ)Lh，不附加边界外可微假设。实际乘积w·p的域内导数为wDp+pW，由真实导数字段界及Lipschitz性给P L₂+2||Dp||L₁，进而得到乘积节点值与梯度误差；单元内部明确等于真正fderiv。

真实域内二阶字段界可供应W的Lipschitz常数。允许权σ²的统一实例、P到实际L²量转换与全域加权超逼近仍待；一般H²插值也未冒充完成，原文12/26。见`analysis/T060-within-affine-product.md`。

## T061：实际允许权平方的域内导数与乘积节点误差

三模块10声明，AUXILIARY。真实平方权等于2ρ/2τ指数权，给实际闭域一、二阶fderivWithin及其HasFDerivWithinAt身份；固定C先于q、τ、符号及空间点，导数界Cqσ²/Cq²σ²。在原开凸紧闭包设定和hq≤1下，profile Lipschitz及真实均值定理供应锚定顶点的Cqσ²(a)一阶界和Cq²σ²(a)导数字段Lipschitz界。

代入真实仿射状态p，得节点值误差2Cσ²(a)(q²P+2q||Dp||)h²及形状控制下导数字段误差(1+4κ)Cσ²(a)(q²P+2q||Dp||)h，实际TimeWeight乘子平方身份已证明。P到L²、倒数权及全域超逼近仍待；原文12/26。见`analysis/T061-squared-weight-errors.md`。

## T062：真实加权单元残差及实际导数积分界

四模块10声明，AUXILIARY。真实节点平方和构造P并由精确质量下界给P²|K|≤(d+1)(d+2)∫p²；真实CLM/fiber范数比较将q²P+2q||Dp||转成单元L²状态/梯度能量。正连续权的真实积分比较把点态节点误差转成σ倒数加权积分，未保留P额外前提。

原允许σ²p实际残差满足值平方误差≤C h_K⁴(q⁴∫σ²p²+q²∫σ²|∇p|²)，梯度平方误差≤C h_K²同能量；C先于网格、q、τ、符号及状态。真实内球/形状与hq≤1保留；零测边界将域内字段识别为实际fderiv的a.e.积分。完整状态全域识别、弱梯度和网格求和仍待，原文12/26。见`analysis/T062-weighted-local-errors.md`。

## T063：完整状态的全域节点残差及实际积分求和

六模块13声明，AUXILIARY。真实全域节点残差在闭单元及内部邻域等于局部残差，零测骨架给实际fderiv身份；所有实际加权被积函数可积，精确网格求和得值h⁴/梯度h²乘q⁴状态与q²梯度能量，统一C无单元个数依赖。

完整V_h状态内部供应零边界节点代表及真实弱梯度身份，最终右端使用原H¹ jet的实际Lp状态/弱梯度，真实加权节点测试属于完整H¹₀一致空间。左端仍为实际残差fderiv积分；残差H¹/弱梯度、ℓ⁻¹项与投影组合尚待，原文12/26。见`analysis/T063-global-nodal-errors.md`。

## T064：真实弱残差与原允许乘子范数

六模块9声明，AUXILIARY。只在实际支持集要求系数有界/Lipschitz的乘积论证，给零边界节点残差真实紧支撑全局Lipschitz性；真实弱导数及限制构造完整H¹ jet，字段a.e.等于实际残差及Euclidean梯度。成员资格常数不进入统一误差常数。

真实Lp乘子差值与原允许σ/倒数ξ平方seminorm身份，使完整V_h任意状态内部得到I∈V_h和真实弱残差e，值/梯度加权范数平方分别≤C h⁴/Ch²乘(q⁴||σu||²+q²||σ∇u||²)。C先于网格、时间权、τ、时刻、符号与状态；ℓ⁻¹项、投影组合及残差H¹₀身份仍待，原文12/26。见`analysis/T064-weak-nodal-norms.md`。

## T065：原尺度残差与节点超逼近

见 [T065规格](analysis/T065-scaled-nodal-norms.md)。五模块7声明：真实ℓ⁻¹残差和同一I/e三平方范数界，准确原弱N范数及原9.26-eq10/11；统一常数先于网格/权/状态。投影测试eq:testsuper、H¹₀残差资格及一般H²插值未宣称完成；AUXILIARY，原文12/26。

## T066：原完整P1投影测试超逼近

见 [T066规格](analysis/T066-projected-superapproximation.md)。三模块6声明完成真实Π_h(σ²u)−σ²u弱H¹误差及原eq:testsuper，原γ<Γ_d阈值、尺度比较、统一δ/C和完整V_h保持；接入既有GalerkinSuperapprox并以弱导数唯一性识别canonical jet。未将该接口原有hw蕴含误记为A2已清偿。一般H² N3等仍待；AUXILIARY，原文12/26。

## T067：原H¹₀允许权保持性

见 [T067规格](analysis/T067-dirichlet-weights.md)。四模块15声明从真实一阶弱乘积与连续H¹算子、光滑测试乘积及闭包不变性证明全部H¹₀状态的允许权保持；原SmoothOnClosure无需域外延拓。平方权残差的实际H¹ jet由其值身份获得H¹₀资格。仅完成m=1能量空间保持部分，未宣称算子域/交换子或完整A2；一般H²逼近仍待，原文12/26。

## T068：原Dirichlet算子乘积与允许权域保持

见 [T068规格](analysis/T068-dirichlet-operator.md)。三模块10声明在完整弱测试上得到真实负Laplacian乘积公式；内部真实一阶、二阶导数乘子及H¹₀闭包保持，经原form-operator图刻画推出全部实际算子域的允许权保持。无H²正则前提，不缩小原域；统一交换子及A1正则仍待，AUXILIARY，原文12/26。

## T069：原Dirichlet允许权统一交换子

见 [T069规格](analysis/T069-dirichlet-commutator.md)。三模块12声明将真实修正项的相对导数界、实际原算子交换子身份及内在H¹权共轭组合，得到全部原域状态的C(q²||z||+q||∇z||)界。常数先于所有权参数；σ及倒数的实际域资格均内部清偿，无H²正则前提。结合T067/T068完成该模型m=1 A2；A3、A1正则及完整Appendix A仍待，AUXILIARY，原文12/26。

## T070：原Dirichlet形式的A3加权估计

见 [T070规格](analysis/T070-dirichlet-form.md)。三模块10声明从真实平方权弱梯度恒等式、Cauchy–Schwarz及Young得到原N范数上下界；原scalarForm经同一H¹₀能量实现准确识别。原SmoothOnClosure内部给统一导数系数，全部原状态的权保持资格已清偿；c=1/2，上界常数1，下界C先于全部权参数。A1的H²正则及完整Appendix A仍待，AUXILIARY，原文12/26。

## T071：原Dirichlet允许权接口组装

见 [T071规格](analysis/T071-dirichlet-data.md)。两模块3声明准确识别H² jet低阶字段与原H¹域jet，内部供应原AllowedWeightData及双符号AllowedFamily所有A2/A3字段。统一常数先于全部权参数；原A1的H²域嵌入明确保留为前提，未新增闭包公理或宣称正则性已证。AUXILIARY，原文12/26。

## T072：凸单元光滑函数的均值 Poincaré

见 [T072规格](analysis/T072-convex-poincare.md)。四模块11声明以真实均值平方恒等式、线段FTC、L² Cauchy–Schwarz和仿射体积雅可比，证明任意正体积紧凸K上真实C¹函数的均值误差≤(2^d/2)D²乘实际导数平方积分。半线段、两点差及全部Fubini可积性均证明；未将其冒充一般弱H¹/H²结果，后续仍需局部卷积穷竭和真正逼近。AUXILIARY，原文12/26。

## T073：原凸域的真实弱 H¹ 均值 Poincaré

见 [T073规格](analysis/T073-convex-weak.md)。五模块21声明以真实局部卷积、原弱导数坐标能量、L²双差Fatou与显式内部紧凸穷竭，证明原有界开凸域全部H¹ jet的均值误差≤(2^d/2)D²||field 1||²。零延拓仅作L²卷积，全部弱测试留在原域；无边界迹、光滑状态或全空间H¹延拓前提。一般H²仿射逼近及原B1/B2仍待，AUXILIARY，原文12/26。

## T074：原凸域全部弱 H² 状态的齐次仿射逼近

见 [T074规格](analysis/T074-h2-affine.md)。五模块34声明从真实平均弱梯度构造实际仿射 p 与零均值弱 H¹ 残差 r，两次原凸域弱 Poincaré 给 `||r||+D||∇r||≤d(2^d+1)D²||field₂u||`。真实 Hessian 坐标和使用明确 d² 上界；无光滑代表、全空间延拓或零迹前提。物理面迹校正、原完整 B1/B2/P1 尚待，AUXILIARY，原文12/26。

## T075：全部弱区间 H¹ 类的实际迹与乘积端点积分

见 [T075规格](analysis/T075-weak-trace.md)。五模块25声明从原全部弱 Hilbert H¹ 图证明连续代表存在唯一，构造实际有界线性迹算子及端点 FTC；标量积分分部给两端点显式公式。乘积端点积分有实际 L² 资格、代表不变性及 `(2/L)||f||²+2L||v||²` 上界，并在真实弱切片上等于其连续代表的端点。原多维弱身份到切片的证明、坐标拆分及物理面校正仍待；AUXILIARY，原文12/26。

## T076：原乘积域完整弱导数与实际 L² 面迹

见 [T076规格](analysis/T076-weak-slices.md)。五模块16声明以真实张量测试、全部可积 Fubini 和横向基本引理给逐测试切片身份，再用实际 L² 测试对空间的可分性取得对所有测试共同的满测集。原乘积域任意弱 L² 数据因此拥有真正弱切片及连续代表的双端点；实际面 L² 类满足正确 2/L、2L 估计。长方体坐标拆分及物理面仿射校正仍待；AUXILIARY，原文12/26。

## T077：原欧氏长方体的真实弱面迹

见 [T077规格](analysis/T077-box-face.md)。五模块42声明证明实际坐标拆分、平移及限制体积乘积身份，将原全部弱坐标导数传输到已验收的全弱切片定理。原长方体真实双面 L² 迹保留 2/L、2L 尺度；对全部真实 H¹ jet 给全梯度界，并证明连续代表的迹就是实际面限制。任意物理面集合的仿射核校正及统一 B1/B2 尚待；AUXILIARY，原文12/26。

## T078：真实面迹线性结构与闭面仿射核校正

见 [T078规格](analysis/T078-affine-face.md)。七模块41声明证明实际乘积端点迹与原长方体迹的线性性，实际仿射类及全弱导数、闭面核的精确识别和有限面集合统一的核校正。单位立方体上用原面迹平方和控制真正 L² 与全梯度误差，常数仅依赖维数；一般固定盒子的中间常数不宣称网格统一。与原全部 H² 逼近、物理零迹及侧长统一缩放的组合尚待，AUXILIARY，原文12/26。

## T079：参考立方体全部弱 H² 的边界仿射逼近

见 [T079规格](analysis/T079-unit-boundary.md)。四模块15声明将真实全弱 H² 逼近、实际面迹线性身份及闭面核校正组成参考单位立方体上的完整零迹仿射逼近：任意全部弱 H² 状态和任意所选闭面集合，常数仅依赖维数，残差实际 L² 与全梯度由原 Hessian 半范数控制。直接输出实际仿射多项式与真实 H¹ 残差。原物理尺度 h² 的统一缩放与 B2 尚待，AUXILIARY，原文12/26。

## T080：物理盒仿射多项式与真实面迹缩放

见 [T080规格](analysis/T080-box-scaling.md)。四模块35声明构造实际正对角同构与平移盒图，证明真正行列式、开闭盒及闭面的精确对应、Lebesgue 换元。全部仿射多项式的真实 L² 值、完整梯度与实际面迹满足正确体积／横向雅可比缩放，并给 h/κ≤边长时的统一 H¹ 缩放上界。等价路线将全部弱 H² 逼近留在物理域，仅缩放有限维仿射校正；不增加原状态假设。最终物理统一 h² 组合及 B2 仍待，AUXILIARY，原文12/26。

## T081：原 Lemma B.1 的统一物理 h² 边界仿射逼近

见 [T081规格](analysis/T081-physical-boundary.md)。六模块15声明组合物理原弱迹界、参考有限面核校正、真实仿射缩放及物理凸域全部弱H²逼近，给原 B.1：常数仅依赖维数和侧长可比界，先于全部盒子、h、面集合与原全部弱H²状态；输出整个所选闭面消失的实际仿射 p 和真实 H¹ 残差，实际误差≤Ch²乘原Hessian半范数。另证明两非平行面消去全部仿射核及原角点齐次界。原稿不变，仅调整等价证明路线。固定提交已获独立PAPER验收，P025完整完成，原文13/26；B2仍待。

## T082：全局 Dirichlet 状态的真实局部面零迹

见 [T082规格](analysis/T082-dirichlet-face.md)。四模块16声明证明实际 L² 与完整弱图空间限制连续、真正盒面迹连续，并以原紧支撑光滑测试在物理面零和闭核包含图闭包，推出全部原H¹₀状态的局部面零迹。限制/截断交换后，原全部H²∩H¹₀状态自动满足B1局部零迹，实际局部Hessian限制范数给统一h²边界仿射逼近，无新增迹或光滑假设。原FD矩重构及B2全局加权组合仍待；AUXILIARY。

## T083：原允许权族的真实局部边界仿射逼近

见 [T083规格](analysis/T083-weighted-local.md)。四模块9声明证明真实乘权与子域限制交换、双向锚点界及实际允许权的盒内统一比较，再对原全部H²∩H¹₀状态给实际加权局部仿射误差≤Ch²乘原加权Hessian局部范数。固定光滑轮廓内部供应Lipschitz界，hq≤1内部供应权比较；常数先于全部盒、h、时间权、周期、幂次、正负号及状态。真实FD矩重构和有限重叠全域组合仍待，AUXILIARY，原文13/26。

## T084：真实平方积分与笛卡尔有限重叠的全域组合

见 [T084规格](analysis/T084-patch-assembly.md)。三模块16声明证明真实有限覆盖／重叠的平方L²估计，实际各向异性整数格点扩张块的重数界`(2r+1)^d d!`，以及局部加权h²估计到全域估计的`sqrt(2M)`组合。常数不含网格总单元数；实际FD局部再现／稳定性及其索引、支撑进入笛卡尔块的实例仍待。AUXILIARY，原文13/26。

## T085：实际 Kuhn 单元与顶点星支撑

见 [T085规格](analysis/T085-kuhn-stars.md)。三模块24声明从真实上三角同构构造前缀顶点单纯形，经坐标排列、正对角缩放与平移得到原Kuhn单元，证明实际顶点与步进公式及闭网格盒包含。共同顶点内部推出整数格点相差至多1；完整无限格网星并集等于有限紧单元之并，紧且可测、位于固定扩张块，有限单元族的实际星重数≤`5^d d!`。全部网格覆盖／不交、帽函数、矩条件与Qh仍待；AUXILIARY，原文13/26。

## T086：真实有限 Kuhn 网格覆盖与几乎处处分割

见 [T086规格](analysis/T086-kuhn-partition.md)。四模块34声明以实际相邻坐标差重构参考凸包，证明有序坐标刻画；真实排序与floor选出有限格点／排列，证明整个开域点态覆盖。内点正向扰动给严格坐标界与严格排列次序，证明全部不同格点／排列单元内部不交；结合已证边界零测性得到真实有限网格几乎处处唯一分割。实际有限索引同时内部供应星重数≤`5^d d!`。帽函数、矩和Q_h仍待；AUXILIARY，原文13/26。

## T087：实际 Kuhn 公共面与连续 Dirichlet 节点帽函数

见 [T087规格](analysis/T087-kuhn-conforming.md)。六模块43声明用实际顶点坐标／坐标差的整数宽度证明公共面匹配，以正重心支撑的边界坐标等式证明物理边界贴合；内部构造真实SimplicialPartition。实际Kronecker节点数据拼接出连续内部帽函数及其L²类，属于原H¹₀图闭包；单元内精确为局部重心坐标，非相邻单元为零，拓扑支撑位于实际有限节点星及共享顶点星块。节点矩、载荷提升、Q_h与原FD/B.2仍待；AUXILIARY，原文13/26。

## T088：实际内部节点帽函数中心对称与零一阶矩

见 [T088规格](analysis/T088-kuhn-first-moment.md)。四模块16声明以真实逆序排列和原点`2a-z-1`证明网格单元中心反射公式，内部整数节点保证所有关联及反射单元均属于实际有限网格。重心坐标的真实仿射重标号给有限域零延拓帽函数全空间中心对称；明确证明向量一阶矩可积后，通过反射换元和物理域外零得到原`∫_Ω(x-x_i)φ_i=0`。零阶矩、载荷、Q_h及FD/B.2仍待；AUXILIARY，原文13/26。

## T089：实际内部节点质量与完整仿射矩再现

见 [T089规格](analysis/T089-kuhn-moments.md)。四模块15声明证明实际开盒体积、Kuhn单元平移体积身份及内部节点每个排列／顶点位置的唯一有限关联。真实单元积分及全网格分割得到原零阶矩`∫_Ωφ_i=∏δ_j`，与已验收零向量一阶矩组合，证明全部实际仿射p的归一化矩再现`(∏δ_j)⁻¹∫_Ωpφ_i=p(x_i)`，真正可积性内部供应。载荷右逆、稳定性与FD/B.2仍待；AUXILIARY，原文13/26。

## T090：原完整内部节点空间上的真实 L² 载荷右逆

见 [T090规格](analysis/T090-kuhn-loadlift.md)。五模块28声明从真实重心坐标二阶矩计算实际载荷多项式的双对偶积分，定义只使用内部顶点的真实有限网格分片载荷，证明原局部公式几乎处处成立及真正L²/积分成员。实际内部节点质量给归一化矩右逆，再以完整有限索引`∏Fin(N_j−1)`及实际物理点单射构造任意离散向量的L²载荷，证明整个原有限空间上的`J_h L_h=Id`和J_h满射。网格一致加权稳定性、刚度身份、完整FD/B.2仍待；AUXILIARY，原文13/26。

## T091：实际重构与载荷的网格一致无权 L² 界

见 [T091规格](analysis/T091-kuhn-norm.md)。五模块24声明构造原有限帽和重构及其真实L²类，计算实际局部载荷精确平方积分，并以内部点单射和真实帽质量把单元顶点质量精确组装成原`E(f)=(∏δ_j)∑f_a²`。同一有限分割给真实全域重构界`E/(d+2)≤‖R_hf‖²≤E`及同一右逆载荷界`‖L_hf‖²≤(d+2)E`，常数与网格大小/长宽比无关。全允许权族加权界、局部Q_h和FD/B.2仍待；AUXILIARY，原文13/26。

## T092：原允许权族的实际重构与载荷加权稳定性

见 [T092规格](analysis/T092-kuhn-allowed-stability.md)。八模块18声明由实际紧单元积分、真实重构/载荷公式和精确加权节点质量，得到原物理域上的三项加权L²平方界。固定原光滑轮廓和hq≤1内部供应包含边界顶点的实际权比较；最终统一C先于所有网格、h、时间权及周期T、幂次、符号和完整离散状态。严格使用已接受的同一R_h及L²右逆载荷，不增加节点数或长宽比因子。局部Q_h、刚度和完整FD/B2仍待；AUXILIARY，原文13/26。

## T093：实际 Q_h 的局部 L² 稳定性与裁剪矩形邻域

见 [T093规格](analysis/T093-kuhn-local-projection.md)。四模块22声明严格定义原Q_h=R_hJ_h；真实帽质量与Cauchy–Schwarz、实际P1质量及|K|≤prodδ给全部原L²状态的局部积分/范数界，常数1，并证明a.e.局部数据决定K上全部Q_h值。实际域裁剪radius-2邻域内部包含活动帽非零支撑，是真正开盒、各向宽度在δ_j到5δ_j之间、重数≤5^d d!。明确为一致加宽块，不冒充原最小块；一般局部定理保留任意支撑容纳块。局部仿射再现、梯度逆界和完整FD/B2仍待；AUXILIARY，原文13/26。

## T094：原完整 Dirichlet H² 状态的实际局部仿射再现

见 [T094规格](analysis/T094-kuhn-local-affine.md)。四模块14声明证明实际内部顶点完整枚举、原仿射L²类的J_h矩及Q_h闭单元再现、真实减法线性性，严格构造裁剪块物理闭面并覆盖中心单元的全部边界点。原全部弱H²∩H¹₀状态自动给局部边界相容仿射p、真正弱H¹残差及统一h²估计，并内部保证实际Q_hp=p；常数仅依赖维数和步长可比界，真实局部Hessian范数保留。梯度逆界及完整FD/B2仍待；AUXILIARY，原文13/26。

## T095：实际 Kuhn 重构的 Dirichlet 弱梯度与统一逆估计

见 [T095规格](analysis/T095-kuhn-weak-inverse.md)。四模块17声明以实际坐标置换等距、正对角缩放给真实Kuhn仿射逆映射界κ/h，清偿网格统一L²逆估计的几何前提。原同一R_h严格等于已证nodalLp，物理边界零数据给原H¹₀图闭包资格，并构造值完全相同的真实弱H¹ jet；原局部弱唯一性证明其完整梯度等于实际单元P1梯度。由真实局部范数身份得原R_h弱逆界，组合原J_h与实际局部Q_h界得全部原L²状态的Q_h局部梯度稳定性。常数仅依赖d、κ，完整FD/B2仍待；AUXILIARY，原文13/26。

## T096：实际 Q_h 的原全状态无权局部误差

详见 [T096 分析](analysis/T096-kuhn-local-error.md)。`cartesianKuhn_h2_local_error` 对所有原弱 H²∩H¹₀ 状态、实际有限 Kuhn 单元和正可比网格证明真实值及弱梯度的局部 h² 误差，右侧为同一原 Hessian 在实际加宽裁剪块的 L² 范数。C只依赖固定维数与κ，先于全部网格、h和状态选取。原仿射再现、真实限制 jet 唯一性、实际 Q_h 梯度逆界均内部使用已证结论；无额外状态假设。四模块13声明，AUXILIARY；允许权及全域求和仍待，B.2/FD不提升，原文13/26。

## T097：原 Lemma B.2 的全状态允许权逼近

详见 [T097 分析](analysis/T097-kuhn-weighted-error.md)。四模块7声明中最终 `allowed_weight_cartesianKuhn_approximation` 直接给原实际Q_h的全域加权值差及完整弱梯度差≤Ch²乘原加权Hessian范数，对全部原H²∩H¹₀和允许权、两种符号、任意幂/时间/周期统一。固定原轮廓C¹正则性给实际裁剪块统一权比较，真实局部误差与实际有限重叠内部组装；常数先于全部网格、h、权参数和状态选择。固定环境S允许Ω_g⊆S，原Ω_g=S矩形是原文实例，未增加原假设。保留统一加宽裁剪块的等价证明路线。固定提交a9ca6fccf19cc677a4a60b07f373eb533df9d502已获独立PAPER验收，P026完整完成且无额外前提，原文14/26。FD/P012及其余命题不自动提升。

## T098：实际 Kuhn 弱刚度的精确单元差分展开

详见 [T098 分析](analysis/T098-kuhn-stiffness-cells.md)。两模块9声明从实际物理顶点差和真实仿射导数证明坐标差商公式，完整弱梯度的局部积分及全域原Dirichlet scalarForm严格等于真实单元体积加权相邻节点差商配对之和。输入为全部原内部节点状态，真实H¹₀重构、完整DerivativeFiber、闭单元零测边界及有限积分分割保持不变。AUXILIARY；全局坐标边重排、差分分部求和和完整FD刚度仍待，FD/P012不提升。

## T099：原弱刚度的精确坐标边组装

详见 [T099 分析](analysis/T099-kuhn-stiffness-edges.md)。三模块13声明证明原零边界数据在有限格网掩码平移下的真实和不变，严格识别Kuhn相邻差商为坐标前向差商；固定排列的前缀平移与π换元去除排列依赖，真实体积平移不变及排列体积总和给原物理权∏δ_j。最终原Dirichlet scalarForm(R_hf,R_hg)精确等于完整坐标边差商配对，全部原独立状态及边界层保留。AUXILIARY；原2d+1点Laplacian分部求和和完整FD刚度仍待，FD/P012不提升，原文14/26。

## T100：原标准差分 Laplacian 的精确刚度恒等式

详见 [T100 分析](analysis/T100-fd-stiffness.md)。三模块14声明证明真实有限格网的零边界分部求和，并由内部节点到半开盒的实际单射去除且仅去除零项。原2d+1点Laplacian与原物理节点配对接入真实坐标边能量，最终精确等于同一原H¹₀重构上的Dirichlet scalarForm，即eq:fdstiffness。全部正步长、原独立状态及完整边界项保留，无额外可比性条件。AUXILIARY，完整FD/P012仍待实际测试、观察和接口组装，原文14/26。

## T101：原FD对角测试的精确结构与允许权质量等价

详见 [T101 分析](analysis/T101-fd-diagonal-test.md)。两模块15声明直接实现原全节点空间的σ²线性乘子，证明相对原物理内积的自伴性、正定性、精确加权能量和逆权能量身份。真实零延拓乘法与原节点插值严格相容，点函数及Lp版本均为实际R_h(Tσf)=I_h(σ²R_hf)，实际残差精确对应已验收nodalProductResidual。组合真实允许权质量界得原eq:test-norm，全权族、周期、网格和状态统一。时间导数、周期性及超逼近和观察仍待；AUXILIARY，完整FD/P012不提升，原文14/26。

## T102：原FD测试算子的真实时间导数和统一估计

详见 [T102 分析](analysis/T102-fd-test-time.md)。三模块12声明通过真实有限对角系数到连续算子的连续线性映射，证明原σ²测试的算子范数导数；同一q端点匹配和周期性精确传给原测试。原对数导数界、紧闭包轮廓实际点值界及真实质量比较给eq:testtime。固定β、τStar后，C先于全部网格、周期、时间权、时间、两符号和完整状态；原允许范围|τ|≤τStar保留。AUXILIARY14/26，超逼近和观察仍待，FD不提升。T101残差为论文残差的负值，后续弱jet接口显式处理方向。

## T103：原Kuhn测试的真实统一形状及节点代表唯一性

详见 [T103 分析](analysis/T103-kuhn-test-geometry.md)。三模块8声明通过参考单纯形真实内接球及实际仿射逆界，构造全部物理Kuhn单元的统一半径r₀h/κ内接球，真实cellDiameter/maxDiameter≤(d+1)h，形状常数先于全部网格。两个真实nodalLp相等经局部多项式连续性推出所有实际顶点值相等，因此节点乘法与代表选择无关。原R_h全状态的实际conformingSpace资格内部证明。为随后原超逼近清偿几何和代表前提，AUXILIARY14/26，FD仍待。

## T104：原FD对角测试的完整弱超逼近

详见 [T104 分析](analysis/T104-fd-test-super.md)。三模块5声明将真实全状态弱乘积残差落实到指定原节点数据，显式取论文残差方向，并组合零阶与梯度界为完整H¹权范数。实际Kuhn统一内球、直径和全状态conforming资格均内部供应。固定原物理域、ρ、κ后先选ε及C，再量化全部网格、权族、两符号、时间和完整状态，得到原eq:testsuper。T101/T102的真实对角算子不变；观察及完整FD接口组装仍待，AUXILIARY14/26。

## T105：原FD节点观察及真实重构区域界

详见 [T105 分析](analysis/T105-fd-observation.md)。三模块15声明由实际帽函数闭节点星和真实单元距离界、原观察域紧包含，证明原重构在ω₀上只依赖ω内节点。实际控制空间是ω内节点子类型，B为零延拓、B*为限制；原物理配对和真实控制加权平方和身份完整证明。将实际区域Lp身份与全允许权质量界组合得eq:observationinterface，常数/阈值先于全部网格权族状态。完整FD数值接口组装仍待，AUXILIARY14/26。

## T106：原FD物理Hilbert空间及真实控制伴随

详见 [T106 分析](analysis/T106-fd-physical-spaces.md)。三模块23声明从正物理质量内积构造真正有限维完备状态/控制Hilbert空间，范数平方严格等于原加权节点平方和。原零延拓/限制成为实际连续算子，Hilbert adjoint(B)=B*由原物理配对证明。原允许权观察界已改写为这一真实伴随的加权Hilbert范数，无网格依赖范数等价常数。重构质量伴随及完整数值接口装配仍待，AUXILIARY14/26。

## T107：原FD重构、质量伴随与载荷接口

详见 [T107 分析](analysis/T107-fd-mass-interface.md)。三模块19声明构造同一原物理Hilbert空间上的实际重构连续线性映射及单射性，证明真实Hilbert伴随逐节点严格等于原归一化帽函数积分。原Reconstruction接口的R/J/Q/G与已验收实际构造完全一致；原LoadInterface取F=X、Γ=Id和同一真实L²载荷，并证明兼容性及I=Id右逆。完整FD数值接口组装仍待，AUXILIARY14/26。

## T108：同一原物理Hilbert测试的完整WeightedTest接口

详见 [T108 分析](analysis/T108-fd-weighted-test.md)。三模块14声明构造真实物理Hilbert平方权测试及其算子范数导数，证明同一原节点公式、周期端点、二次配对导数、对称与非负。完整WeightedTest明确使用同一实际测试/导数，实际时间和超逼近界内部组合，弱jet值唯一性识别原残差及重构，常数先于全部网格、周期、允许权和两符号。完整FD其他数据装配仍待，AUXILIARY14/26。

## T109：原物理刚度、加权范数与统一稳定性

详见 [T109 分析](analysis/T109-fd-physical-numerics.md)。三模块19声明把原差分Laplacian构造为同一真实物理Hilbert连续算子，证明原精确刚度、自伴与非负。状态/控制实际权范数具有正定性和原权同质性，原测试严格正；同一RH、载荷与测试的无权/全允许权界接入同一接口，统一常数先于全部网格和权族。完整FD统一装配及N3接口仍待，AUXILIARY14/26。

## T110：原B.2逼近接口与真实FD数值数据组装

详见 [T110 分析](analysis/T110-fd-approximation-interface.md)。两模块4声明由原完整B.2和hq≤1严格推出完整H¹能量/值误差，保持a_E=Ch、a₀=Ch²；同一实际Q_h误差jet经弱值唯一性接入WeightedApproximation。原数值数据在同一真实A/R/J/载荷/B*及实际权范数上统一组装，η_A=0，阈值及全部常数先于网格、周期、权族与两符号。D(A)≤H²明确保留为原A1连续前提，不冒充已证具体H²正则性或完整FD/P012。AUXILIARY14/26。

## T111：原全P1空间的完整加权测试接口

详见 [T111 分析](analysis/T111-p1-weighted-test.md)。实际全P1超逼近与原Galerkin测试时间性质组合为完整WeightedTest，明确算子与导数均为同一实际Pi_h(σ²z)构造。阈值与正时间/空间常数先于全部原分级网格、周期、时间权和两符号；有限测度由紧闭包内部供应。原全H²逼近仍待，不提前提升P1/P011。AUXILIARY14/26。

## T112：低维光滑状态的真实L² Hessian节点值误差

详见 [T112 分析](analysis/T112-p1-h2-nodal.md)。二阶Taylor积分余项、真实收缩Jacobian及可积r^(−1/2)核给d≤3的平均Taylor余项；同一实际仿射多项式及节点插值给闭单纯形上∫|f−I_Kf|²≤16D⁴∫‖D²f‖²，保留真实L² Hessian，自动证明体积正性。两模块15声明；当前只在光滑类证明，弱H²闭包、梯度及全局权估计仍待。AUXILIARY14/26，P011不提升。

## T113：光滑状态的真实L² Hessian节点梯度误差

详见 [T113 分析](analysis/T113-p1-h2-gradient.md)。同一平均Taylor多项式的实际平均梯度、逐坐标原均值Poincare及真实内球仿射逆界，给d≤3的完整梯度平方误差≤(2^d d+128κ²‖derivativeOneFiber‖²)D²乘实际二阶张量L²积分。单模块5声明；与T112结合完成光滑类局部值/梯度界，常数只依赖维数与形状。弱jet Hessian识别、弱H²闭包和全局权逼近仍待，AUXILIARY14/26。

## T114：原弱 Hessian 的真实局部卷积与节点误差界

详见 [T114 分析](analysis/T114-weak-hessian.md)。真实局部弱链经两次分部积分识别实际卷积二阶张量，固定维数坐标重构和L²收缩给可积性及原field₂控制；全部原弱H² jet自动供应链，零延拓仅为L²数据。组合真实光滑节点值/梯度估计，常数对核及半径统一，保留实际支撑须在原域内的条件。四模块11声明，连续节点代表、边界极限及全局允许权逼近仍待；AUXILIARY14/26，P011不提升。

## T115：原弱 H² 的真实内部强光滑逼近

详见 [T115 分析](analysis/T115-strong-h2.md)。真实L² Fatou与平行四边形身份给强收敛准则，实际缩小核的收缩与a.e.收敛推出全部L²输入的强收敛；原局部弱链和内部支撑缓冲进一步给全部原弱H² jet的同一C∞卷积在内部紧集上值、全部一阶/二阶分量同时强收敛。四模块10声明，无光滑代表或全空间Sobolev延拓前提；连续节点代表、边界适配和全局权逼近仍待，AUXILIARY14/26。

## T116：低维原弱 H² 的真实内部连续代表

详见 [T116 分析](analysis/T116-h2-continuous.md)。实际低维 L² Hessian 点值估计、固定张量坐标重构和一致 Cauchy 准则，将同一原弱 H² 卷积序列转为内部紧凸集上的连续一致极限；局部闭球拼接给任意开域上原全部 d≤3 弱 H² 的单一连续代表、a.e. 身份、每个内部点的实际卷积极限及代表唯一性。五模块14声明，无预设点值或连续代表；闭包边界延拓、零边界节点和全局允许权插值仍待，AUXILIARY14/26，P011不提升。

## T117：真实向内收缩的全 L² 强连续性

详见 [T117 分析](analysis/T117-inward-l2.md)。实际仿射 Jacobian 给全 L² 拉回资格、精确平方范数和统一维数界；真实能量收敛/Fatou准则与实际光滑卷积密度推出任意 L² 代表的向内拉回强收敛。全部 k 阶实际导数缩放与同时变化近似序列的强极限均证明，不假定原任意代表点态收敛。五模块17声明；闭域弱 H² 光滑逼近和边界连续代表仍待，AUXILIARY14/26，P011不提升。

## T118：原弱 H² 的闭域强光滑逼近与连续代表

详见 [T118 分析](analysis/T118-h2-closure.md)。真实收缩闭包的紧支撑缓冲给状态无关核序列；同一实际向内卷积在整个闭包上对原全部弱 H² 的值、全部一/二阶分量强 L² 收敛，零延拓仅作为 L² 数据。低维一致 Cauchy 准则和真实 L² 极限唯一性构造有界开凸域 d≤3 的闭包连续代表与唯一性，覆盖空域。五模块12声明；H¹₀边界零值、全弱节点误差及全局允许权仍待，AUXILIARY14/26，P011不提升。

## T119：原全部弱 H² 的真实局部节点值误差

详见 [T119 分析](analysis/T119-weak-nodal-value.md)。真实闭域光滑逼近经节点插值连续性、强 L² 能量极限及 Fatou，给全部原弱 H² 的局部节点值平方误差≤16 D⁴ C(d,2)² d²乘同一单元的原弱 Hessian 平方积分；最终自动选取一个闭包连续代表用于所有单元。五模块12声明，没有预设光滑性或插值界，常数只依赖维数。梯度误差、H¹₀边界零值及全域允许权组装仍待，AUXILIARY14/26，P011不提升。

## T120：原全部弱 H² 的真实局部节点梯度误差

详见 [T120 分析](analysis/T120-weak-nodal-gradient.md)。真实节点导数连续性及全一阶强 L² 极限把光滑梯度估计传到原完整弱梯度，右端保留同单元弱 Hessian 积分，显式常数只依赖维数/形状并具有 D² 阶。最终自动选择一个闭包连续代表，对所有单元同时给真实值/梯度误差。四模块9声明；H¹₀边界零值、conforming 插值及全局权仍待，AUXILIARY14/26，P011不提升。

## T121：真实全空间弱导数的 C¹ 链式法则

详见 [T121 分析](analysis/T121-weak-chain.md)。真实支配收敛及变动有界乘子强 L² 极限、全部测试的弱身份闭合和实际卷积经典导数，证明任意全空间 L² 弱导数对的 C¹ Lipschitz 标量链式法则，η(0)=0保证真实全空间 L²。三模块9声明，未预设原状态点态可微。为H¹₀边界零值的截断论证提供工具，尚不声称边界结论或完整P1；AUXILIARY14/26。

## T122：原 H¹₀ 连续代表的真实边界零值

详见 [T122 分析](analysis/T122-dirichlet-continuous.md)。真实光滑截断、弱链式法则及凸域弱 Poincaré 排除原弱函数的值域正间隙，再由实际 H¹₀ 零延拓与开凸域边界两侧的正测度，证明任何原闭包连续代表在全部边界点为零。最终对原全部有界开凸域 d≤3 弱 H²∩H¹₀ 自动构造该代表。四模块5声明，无预设迹定理；全网格 conforming 误差及允许权仍待，AUXILIARY14/26，P011不提升。

## T123：全部弱 H²∩H¹₀ 的同一 conforming 节点误差

同一实际闭包连续且边界零代表供应真实节点插值，属于原全部 conforming P1 空间；实际误差 jet 是 truncate¹ u−I_hu，值及全部一阶弱导数均与真实局部多项式对应，属于原 H¹₀。全部原弱 H²∩H¹₀ 状态自动得到同一 f/e，之后对所有单元及原内球/形状/直径参数满足局部值与梯度界，右侧是同一单元原 Hessian 能量。三模块8声明，6727项递归公理通过；全域权与投影仍待组合，AUXILIARY14/26，P011不提升。见 `analysis/T123-weak-conforming.md`。

## T124：全部原弱状态的全域允许权节点插值

原弱 H²∩H¹₀ 的同一f/e先于全部允许权选定；实际局部W⁴权转移、精确单元求和和真实ℓ²/ℓ乘子给原两个节点插值估计。C仅依赖固定域/profile/d/形状/尺度比较，不依赖网格、状态、时间或实幂；全部TimeWeight、τ,t及两种符号均覆盖，h q(t)≤1。五模块10声明，6740项递归公理通过；投影和P1接口仍待组合，AUXILIARY14/26。见 `analysis/T124-weak-weighted.md`。

## T125：原全部弱状态的P1投影误差与N3

真实Π_h的固定误差E∈H¹₀先于全部允许权选定；原全域节点估计、四权投影稳定性、加权逆估计和上下尺度给值Ch²、能量Ch界。常数先于全部网格、原弱H²∩H¹₀状态、T/时间/实幂/符号。对任意原D⊆H²∩H¹₀，实际conforming重构与唯一弱jet对应，得到原Section4.WeightedApproximation，aE=Ch、a0=Ch²。三模块3声明6743审计通过；具体连续DirichletH²正则性不由本接口证明，AUXILIARY14/26。见 `analysis/T125-p1-approx.md`。

## T126：原 L²(ω) 控制与全 P1 NumericalData

`restrictRegion_weighted_sq` 给真实受限 L² 权范数的积分身份；`conforming_region_weighted_observation` 在 ω₀⊆ω 下证明实际 B_h* 限制的观测界，常数1。`galerkinRegionNumericalData` 使用真实 inclusion 重构、Galerkin 刚度、零缺陷、正交投影负载及原 L²(ω) 控制。

`full_p1_numericalData` 对原全 conforming P1 网格族、原 grading、真实允许时间权与两符号，把已证明的 N3/N4 内部供应给同一实际数据；统一 δ/Ctime/Csuper/Capp 先于全部网格及时间参数，aE=Capp h、a₀=Capp h²、ηA=0。具体 Dirichlet 算子域的 H² 包含 hD 仍是显式原 A1 前提；本阶段不替代连续 H² 正则性或连续 CE，AUXILIARY、14/26。

## T127：有界分布导数与实际 L² 极限

`exists_inner_of_bounded_test_functional` 由真实 Hahn–Banach 和 Riesz 构造同常数 Hilbert 代表。`exists_weakSpatialDerivative_of_test_bound` / `exists_weakSpatialDerivative_iff_test_bound` 对任意开域上的原全部光滑紧支测试，证明分布导数在原 L² 测试范数中 C 有界与存在范数≤C的真实弱导数等价。

`exists_weakSpatialDerivative_of_test_limits` 容许每个测试各自最终成立的分部积分身份，候选导数字段只要求最终L²范数≤C，不要求其收敛；从测试配对极限构造真实弱导数。`exists_weakSpatialDerivative_of_strong_limit_bounded` 给恒定域上强L²极限的直接推论。常数C原样保留，无有界域或边界光滑性限制，不预设待证弱导数存在。凸域Dirichlet H²的实际先验界和内域正则性仍未完成；AUXILIARY14/26。

## T128：真实对称 Hessian 组装与 H² 极限

`SpatialTest.derivativeTest` 保持原紧支光滑测试资格，真实两次方向导数在 L² 中交换；`IsWeakSpatialDerivative.mixed_commute` 由全部测试身份和密度证明原弱状态混合导数交换。`derivativeFieldAssembly` 将原无序多重指标的 L² 分量组装为真实 Euclidean 字段，精确恢复每个分量及平方范数和。

`secondOrderJet` 保留原 H¹ jet 的全部字段，接入真实二阶弱导数。`exists_weakH2_of_gradient_test_bounds` 从每个梯度分量的原测试范函 C 界内部构造二阶 L² 字段及对称性，得到相同一阶截断的原 H² jet，并有 ‖field₂U‖²≤card(Sym(Fin d),2) C²。`exists_weakH2_of_gradient_test_limits` 允许逐测试最终身份和只受最终统一界控制的候选 Hessian；`exists_weakH2_of_strong_H1_limit_bounded` 为强 H¹ 极限推论。任意维数/开域，C≥0，无 H² 零延拓或候选 Hessian 收敛前提。具体 Dirichlet 正则性先验界和光滑内域解仍待，AUXILIARY14/26。

## T129：H¹₀ 弱紧性与真实 Dirichlet H² 极限

`exists_hilbert_weak_subsequence` 及闭子空间版本由实际弱对偶紧性/Riesz选同一弱子列并保留原范数界。`exists_dirichlet_weak_subsequence` 在真实Sobolev Hilbert空间及原H¹₀测试闭包中提取子列，内部供应Lebesgue L²可分性，保留两阶真实字段的弱收敛和平方和界。

`IsWeakNegativeLaplacian.unique_rhs` 及 `of_weak_gradient_limit` 保持全部原Poisson测试身份。`exists_dirichlet_H2_of_bounded_approximants` 从原H¹₀逼近、统一H¹能量界、候选Hessian最终L²界与逐测试最终身份，内部构造实际H²∩H¹₀解且negativeLaplacian v=f，Hessian平方≤card(Sym(Fin d),2)C₂²。无需候选Hessian收敛/全域弱导数资格或H²零延拓。实际光滑内域解、Hessian先验界和穷竭仍待供应；AUXILIARY14/26，P023不提升。


## T130 / C146：真实子域 Dirichlet 零延拓

- 原对象：任意开域 T⊆S，原 H¹₀ 测试闭包中的 H¹ jet。
- 结论：真实全空间零延拓后限制到 S，仍属于原 H¹₀(S)；每阶 L² 字段范数不增，测试精确保持同一函数，延拓在原完整 H¹ 拓扑连续。
- 证明义务：测试支持和 a.e. 身份、限制伴随的零延拓连续性、真实测试闭包传极限，均内部证明；不要求 H² 零延拓。
- AUXILIARY，P023 不提升；分析见 `analysis/T130-dirichlet-extension.md`。


## T131 / C147：真实内域解与 Dirichlet 穷竭极限

- 原对象：有界开域 S、真实 L² 右端项 f、递增开域穷竭 Tₙ⊆S、原 H¹₀ 内域解。
- 内部构造：coercive form 给每个内域的实际弱解；外域 slab Poincare 给所有内域同一 H¹ 界。实际零延拓等距及限制伴随配对供应所有测试身份，紧支持最终落入 Tₙ。
- 穷竭极限：若这些内域有实际 H² 解且完整 Hessian 统一有界 C，则构造同一 f 的真实 H²∩H¹₀(S) 解，Hessian²≤card(Sym(Fin d),2)C²。H¹ 界、全域候选字段及逐测试最终身份均不再作为输入。
- 边界：不宣称 H² 零延拓；只延拓 H¹₀ 状态及单独 L² 二阶分量。不对支持未落入内域的测试声称内域方程成立。
- AUXILIARY，14/26。光滑内域 H² 正则性、统一二阶估计和凸域光滑穷竭仍未清偿，P023 不提升。分析见 `analysis/T131-dirichlet-exhaustion.md`。


## T132 / C148：内部 Hessian 能量与弱 Poisson 平滑化

- 原对象：实际紧支 C∞ 测试，以及任意原 H¹ 弱 Poisson 状态和 L² 右端项。
- 测试结论：真实有序二阶能量等于纯二阶导数和的 L² 范数平方；内部构造原 H² jet，保留同一 H¹ 截断与实际 Laplacian。
- 平滑化结论：反射核紧支持位于域内时，真实卷积函数满足 −Δ(u*κ)=f*κ；只用原一阶弱链和 Poisson 方程。
- 不将紧支测试恒等式冒充一般 Dirichlet 边界估计，不假设原状态 H² 或全空间 H² 零延拓。
- AUXILIARY，14/26。分析见 `analysis/T132-interior-energy.md`；P023 的剩余边界与凸域正则性义务不变。

## T133 / C149：真实 Poisson 截断与统一 H² 界

三模块12声明证明实际经典 Laplacian 的乘积法则、紧支测试局部化及真实 L² 代表身份。对原 H¹ 弱 Poisson 解和仅在截断支持内合法的反射核，内部证明全空间精确局部化 PDE。由固定截断的紧支光滑性内部选 M，再量化解、载荷与核；非负单位核的 L² 收缩与真实有界乘法给 ‖Δ(η(u*κ))‖₂≤M(‖f‖₂+2∑ᵢ‖Gᵢ‖₂+‖u‖₂)。构造同一局部化测试的真实 H² jet，保留完整一阶 jet、负 Laplacian 等式和 Sym 字段维数因子。AUXILIARY14/26；原解内部极限、边界正则性与凸域全局估计未提前认定。

## T134 / C150：原弱 Poisson 解的内部 H² 正则性

四模块6声明内部构造紧支光滑截断，证明 η=1 的开内域上实际截断卷积梯度强 L² 收敛到原梯度。真实二阶候选的完整测试身份和 T133 最终统一界恢复同一 u|T 的 H² jet。原弱方程经测试延拓/限制准确保留同一载荷；最终定理仅输入 S、T 开、closure T 紧包含于 S，常数先于全部原 H¹ 弱解及 L² 载荷，输出完整一阶 jet 等式、negativeLaplacian v=f|T 及显式 Sym 维数因子估计。无 H²、核、截断或极限前提；内部正则性已构造，边界正则性和凸域全局估计仍待。AUXILIARY14/26，P023不提升，详见 `analysis/T134-interior-regularity.md`。

## T135 / C151：原 P1 粗空间 Rayleigh 界（P019）

目标为 `prop:filter-p1` 的完整 Proposition7.7。三模块8声明从已证全 conforming P1 逆估计取真实常数权1，内部得到 κ/Q 形状准一致参数下的全粗状态梯度界；C 先于所有粗/细网格和域。细刚度严格为原 Dirichlet Galerkin 算子，一致质量为原 L² 子空间范数，F 为实际粗空间包含映射的像，Hc 为实际粗单元最大直径。内部证明零空间/非零空间的真实 Rayleigh supremum 界，最终 Λ_F≤C/Hc²。无预设逆界、H²正则性或连续CE，不要求细算子保持F。独立验收前不增加完成数；完整 PAPER 验收后只提升 P019，详见 `analysis/T135-filter-p1.md`。

### T136 / C152：原 Cartesian 粗网格命题的一维精确插值估计

原 `prop:filter-fd` / P020 中的一维部分使用真正粗节点线性插值，细区间数为 mK，m>0。`linearRefinementMass_eq` 精确给每粗单元细梯形质量 m(a²+ab+b²)/3+(a−b)²/(6m)，`linearRefinementEnergy_eq` 精确给边能量 (b−a)²/m，进而内部推出系数12的单元逆估计。`uniformLinearProlongation` 直接用商/余数从同一粗数据计算全部细节点；节点值、完整闭粗单元上的线性公式、质量与能量分块均精确证明。零端点使梯形质量总和严格等于实际对角节点平方和，最后恢复 h 加权物理质量与前向商，得到常数12/(mh)²，先于所有粗数据且对任意正整数m成立。K=0、m=1也保留。此批三模块18声明只申请AUXILIARY验收；多维张量插值及原实际差分算子/保留像连接尚待，P020不提前提升。

### T137 / C153：原 Proposition 7.8 的完整 Cartesian 粗网格 Rayleigh 界

`tensorLinearProlongation` 是全部真实粗内节点数据的一维线性节点基函数张量积；粗节点恢复、两侧零边界、任意坐标截面等于同一一维粗插值均内部证明。有限 Cartesian 和用实际 piSplitAt 双射逐坐标分解，应用T136精确一维估计并求和得到12∑Hr⁻²。`cartesianCoarseProlongation` 将全部粗数据送入原物理细状态空间，其真实对角质量和原2d+1点差分能量均与上述张量值严格相等，包括边界两端；未改质量、差分或保留空间。

`Physical.fd_coarse_filter_rayleigh` 对任意维数、每轴m>0和任意K，细分数N=mK，全部正细步长h，证明原filterRayleigh在实际插值range上的上界12∑((m_r h_r)⁻¹)²。`fd_dividing_filter_rayleigh`直接接受原N与m_r∣N_r，内部取K_r=N_r/m_r，输出真实线性插值映射及其每个细节点精确公式和同一Rayleigh界。域原点任意，盒长由N_rh_r确定；无网格尺寸比例、维数限制、算子不变性、H²正则或CE输入。系数12严格保留，零空间/空内节点也由原定义处理。六模块27声明申请完整P020/PAPER验收；固定SHA独立验收及实际CI完成前仍15/26。

### T138 / C154：真实零边界光滑函数的 H¹₀ 成员资格

在原有界凸开域S上，任意全空间紧支光滑测试φ只要在frontier S逐点为0，其限制的完整原H¹ jet属于由紧支域内测试闭包定义的dirichletJetSpace。最终定理不要求φ的支持严格位于S；边界零值经真实indicator零延拓、全空间Lipschitz资格、凸边界零测、内缩强H¹收敛和实际光滑卷积逼近推导闭包成员资格。半径序列依原域内点构造，统一函数/导数界供L²支配收敛；导数连续性只在边界外使用，未假定零延拓全局C¹。该完整测试引理将用于跨盒面奇反射的合法弱测试；全局H²/原P023仍未完成，范围AUXILIARY。

## T139 / C155：原弱 H¹ 的实际坐标反射

任意维数中的坐标 r 及任意 c，实际 R(x)_r=2c−x_r，其它坐标不变。真实保测仿射 L² 拉回及全部弱测试换元给原全空间 H¹ jet 的反射，梯度分量严格为 s_i R(G_i)，s_r=−1、其它1；值/梯度范数、双侧配对及自伴严格保持。完整构造不要求输入光滑，不假设变换后的弱身份。31声明与原始审计见 T139 分析；AUXILIARY，尚未完成跨面 Poisson 方程或全局 H²，原文覆盖保持16/26。

## T140 / C156：实际下侧盒面奇反射的弱 Dirichlet Poisson 延拓

原 S=∏(aᵢ,bᵢ) 的完整弱 H¹₀ 解 u 与 L² 右端 f，沿任意下侧面 xᵣ=aᵣ，真实 U=E₀u−R(E₀u)、F=E₀f−R(E₀f) 限制到实际扩大盒 T=∏(a'ᵢ,bᵢ)，a'ᵣ=2aᵣ−bᵣ。指定 U 满足原弱 Poisson 方程、属于 T 的原 H¹₀ 闭包，并在 S 上恢复整个原 jet；值/梯度/右端全空间范数各≤2倍原范数。测试边界条件由全部实际盒面几何内部证明，H¹₀ 由真实测试序列与完整强 H¹ 连续性证明。八模块40声明；AUXILIARY，不提升全局H²/P023；剩余全部上下盒面迭代与内部H²衔接。

## T141 / C157：实际盒域的完整弱 H² 正则、算子域及右端估计

固定任意正边长坐标盒。逐坐标上下真实奇延拓到端点2a−b、3b−2a的固定扩大盒，完整原H¹₀弱方程与同一jet恢复逐步保持，值/梯度/右端统一4^d界。原闭盒严格在扩大盒内部，已验收的真实内部H²正则给原完整弱解的全局H² jet；原负Laplacian恰为f，常数在所有u/f之前选定。对d>0，实际形式算子域严格等于H²∩H¹₀，且原完整H²图范数≤K‖f‖，由原弱方程和Poincaré内部证明。九模块34声明，固定原稿不变。AUXILIARY：完成P023所需盒上正则部分，未完成一般凸多面体正则、全部解析假设或CE，暂不提升P023/其它PAPER。

## T142 / C158：完整 Cartesian 数值实现（原 Proposition 6.2 / P012）

实际盒上域H²包含由T141内部提供，调用者不再供应正则性前提。原对角质量、Kuhn重构、2d+1点差分、真实载荷与控制伴随的完整数值数据保留aE=Ch、a0=Ch²、ηA=0。另以 `cartesian_full_weight_interface` 明确供应transfer较小接口未保存的原结论：指定节点平方权测试和导数等式、严格正定性、双向测试配对/重构范数、所有允许权的载荷和观测界。常数与阈值先于所有网格、时间、权及状态；全维数、全状态、双符号与全部允许指数。实际N1/N2恒等式和真实算子可微性由固定已有依赖共同构成完整命题，而非把接口较小的字段集合冒充全部N1–N5。两模块两定理申请PAPER验收；连续CE及一般凸多面体正则性不在本命题范围，P023/P024不提升。详见 `analysis/T142-cartesian-full-realization.md`。

## T143 / C159：实际盒域解析数据、真实边界图册与完整 Section 3 辅助估计

真实原盒算子的canonical H² jet受实际算子值控制，域包含与严格正图范数常数内部供应；全部原允许权族的A2/A3与同一原形式保持。任意光滑原空间函数内部构造同值profile。实际非零方向线性坐标、有限活跃面最大图函数及非活跃面邻域给有限严格半空间交的真实Lipschitz图册，真实中点和上下坐标不等式给任意正盒图册，包括全部棱角。最终 `box_section3` 联合提供同一真实算子的完整 Conclusions 和全部所需 AllowedFamily，常数先于网格/周期/权/状态，两种时间方向保留，无额外图册或正则性输入。五模块11声明；AUXILIARY，P023的一般凸多面体正则与P024连续Carleman估计仍待，不提前提升。详见 `analysis/T143-box-analytic-data.md`。

## T144 / C160：连续热算子的实际高斯权与空间矩阵

原 ψ=−‖x−c‖²、φ=exp(lψ)、ρ=φ−2 全空间光滑；真实 Fréchet 一/二阶导数与 Riesz 梯度，负权界及实际有界 SpatialProfile 全部内部证明。用真实 ℓ=qρ 的 Hessian/Laplacian 和 Ψ=−Δℓ−8qlφ 构造原矩阵，证明精确 c=4qlφId+2ql²φ∇ψ⊗∇ψ 及全空间一致强制性。从有界域及非空开观测子集内部选实际球、l、正下界和矩阵常数，先于 q/时间/状态；支持面上的真实法向导数给通量标量非正。三模块32声明。AUXILIARY，仅为 P024 的实际空间权步骤；完整点态热恒等式、面 Green 积分、端点、吸收、密度及时间反射仍待。详见 `analysis/T144-interior-heat-weight.md`。

## T145 / C161：真实时空热算子的完整点态恒等式

用真实Fréchet方向导数证明全部乘积、有限和、混合二阶交换和通量抵消；完整保留原M_t、divV、两个平方、原c二次型和B。实际A=|∇ℓ|²−Δℓ−Ψ、k=ℓ_t+A，B精确展开为原书全部项；真实exp共轭连接原热残差。在ℝ×Euclidean空间上明确识别原deriv与空间Laplacian，z=exp(ℓ)u内部定义，得到任意全空间C∞实函数的完整点态Carleman等式和不等式。五模块53声明；AUXILIARY。此批C∞准备步骤尚未恢复原C²时间权与完整Sobolev轨道，真实域Green积分、周期端点、heatcross系数估计/吸收、密度及时间反射仍待，P024不提升。详见 `analysis/T145-pointwise-heat-identity.md`。

## T146 / C162：周期时间通量积分与实际平面热通量

实际平移周期性经Fréchet微分保持，内部给原M的周期与光滑性；真实时间切片FTC证明每个x上∫₀ᵀM_t=0。局部平面零边值沿真实切向曲线推出切向导数零、法向梯度及时间导数零，继而T145同一热通量严格为V·n=2D_nℓ(D_nz)²。实际Gaussian权与支持半空间条件给非正符号。三模块15声明，AUXILIARY光滑阶段；原C²时间权、Sobolev轨道、原面几何和棱角零测、法向迹/Green积分、吸收及密度仍待，P024不提升。详见 `analysis/T146-heat-time-and-plane-flux.md`。

## T147 / C163：有限半空间交的实际闭面热通量

真实严格半空间交的闭包等于全部弱不等式，单活跃面的实际开邻域给局部边界平面；Riesz向量内部构造真实单位外法向和支持符号。从原u在frontier零值内部得到z=exp(L)u的局部平面零值，对同一V证明非正。给定一个真实相对内部面见证，实际凸插值与通量连续性将符号延伸到该闭面全部点，包括棱角。三模块12声明，AUXILIARY；冗余表示的面见证不自动提供，光滑闭面符号仍非Green积分或原弱轨道CE，P024不提升。详见 `analysis/T147-finite-halfspace-heat-faces.md`。

## T148 / C164：实际坐标盒的面通量与散度积分

真实上下坐标半空间、±基向量法向和中点面见证全部内部构造，从原frontier零值推同一V的全部闭面符号。实际Euclidean到函数坐标保测换元和真实Fréchet链式法则接mathlib散度定理；可积性内部由紧盒连续性供应，开闭盒a.e.相同得到原开域体积分。真实面参数化和上下符号最终给任意正盒上∫divV≤0。四模块15声明，AUXILIARY光滑步骤；原弱Green、一般多面体、C²时间权、完整时空积分与吸收仍待，P024不提升。详见 `analysis/T148-box-heat-divergence.md`。

## T149 / C165：真实光滑周期盒状态的积分热不等式

真实时空限制乘积测度上的可积性由紧柱连续性内部供应；Fubini与周期FTC给同一M_t的整个时空积分零，实际盒散度符号给∫divV≤0。原点态不等式经真实单调积分得到完整bulk（平方、矩阵、混合项和B全部保留）积分≤真实exp(L)(∂t−Δ)u残差平方积分。z及k内部构造，时间T与全光滑周期状态量词保留。三模块15声明，AUXILIARY；bulk尚待实际系数界/观测吸收，原C²权/弱轨道/一般多面体/密度/时间反射仍待，P024不提升。详见 `analysis/T149-integrated-smooth-heat.md`。

## T150 / C166：原高斯相位与热系数的实际微分展开

真实Gaussian的Laplacian、梯度能量及其导数，真实分离时空相位的时间/空间微分和配对，内部给原L=qρ、Ψ=−ΔL−8qlφ的光滑周期与完整系数公式。同一实际k=q′ρ+q²G+8qlφ，实际B经乘积微分消去Laplacian后精确为4q³l³φ³g(lg−6)加全部q²/q′/q″项；g为真实∇ψ范数平方。原Ψ梯度及平方和也精确计算。四模块32声明，AUXILIARY；未证明qclass余项界/混合项Young/吸收、原C²权或完整CE，P024不提升。详见 `analysis/T150-gaussian-heat-coefficients.md`。

## T151 / C167：真实高斯热权的统一余项、混合项与光滑盒 heatcross

实际矩阵二次型内部化为4qlφ能量加非负平方；同一B的全部余项由实际q′/q″界与紧空间系数界控制。实际Ψ梯度能量内部估计，有限方向真实平方求和证明Young混合项界。代入同一bulk并在真实柱体限制测度上单调积分，得到原形式heatcross，主项常数6、残差系数1/4，余项C(l)先于所有T/q/β/u选择。八模块15声明，AUXILIARY光滑周期盒结果；尚需观测吸收、返回u、原C²权与完整弱轨道、一般凸多面体和时间反射，P024不提升。详见 `analysis/T151-gaussian-heat-cross.md`。

## T152 / C168：光滑周期盒的正向热 Carleman 观测估计

任意非空开观测子集内实际选球/中心/λ，真实势球外正下界和全域紧集界给实际示性观测项；先于全部时间数据选择β与qc吸收同一heatcross余项。真实受限乘积测度上的观测积分/可积性和线性消项内部证明。实际exp乘积微分及空间相位能量界返回原u，并识别真实空间切片gradient。最终∫q³θ²u²+∫qθ²|∇u|²≤C(∫|θ(∂t−Δ)u|²+∫_Wq³θ²u²)，全部参数先于T/q/u，ρ负界同时给出。八模块18声明，AUXILIARY；仅C∞周期盒正向估计，原C²权/弱轨道/一般凸多面体/反向情形仍待，P024不提升。详见 `analysis/T152-smooth-heat-estimate.md`。

## T153 / C169：真实时间反射与同常数光滑盒双方向估计

实际R_T(t,x)=(T−t,x)的光滑、自反、周期拉回、时间限制测度和柱乘积测度保持，以及全部真实积分换元内部证明。实际q′反号、q″同号及反射区间保持恢复同一权界；反射u的正向热残差严格等于原−∂tu−Δu。最终同一ρ/λ/β/qc/C先于全部T/q/ε/u选择，原空间梯度与观察积分完整保留，覆盖ε=±1的光滑周期盒估计。两模块14声明，AUXILIARY；原C²权、完整弱轨道和一般凸多面体仍待，P024不提升。详见 `analysis/T153-smooth-heat-both-signs.md`。

## T154 / C170：全局 C² 周期时间权的实际光滑逼近（辅助）

`TemporalMollification`、`TemporalMollificationDerivative`、`TemporalMollificationBounds`、`PeriodicC2Mollification` 共十九声明。使用真实非负单位质量紧支光滑核卷积，保持周期和正下界，证明实际一二阶导数交换与逐点收敛。均值估计在足够小支持上给 q(t−s)≤3q_n(t)，从而导数阶数界为 9β q_n²、27β² q_n³；输入 β/9 的固定余量给目标 β 的同一 qclass。序列共享有限上界 B，实际逼近尺度可依赖 q/T，固定数值余量不依赖它们。

此阶段输入全局 C² 周期 q，尚未包括原闭区间 C² 的周期扩展、权积分极限、完整弱轨道或一般凸多面体。范围 AUXILIARY，原 P024 不提升，覆盖保持 17/26；不把逼近定理当作完整连续 Carleman 估计。详见 `analysis/T154-periodic-c2-mollification.md`。

## T155 / C171：C² 周期时间权下的盒双方向估计（辅助）

`BoxTimeIntegralLimit` 的两项实际有限柱支配收敛定理（含真实观察示性函数），及 `BoxC2HeatEstimate.box_C2_gaussian_heat_both_signs`。先固定光滑估计参数并取 β=β₀/9，再对所有 T>0、全局 C² 周期 q 和光滑周期零边界 u，应用真实逼近及四项实际积分极限，得原指数(3,1;3)、原 ε∂t−Δ 残差的同常数双方向估计。支配常数可依赖本次数据但只用于极限，不进入最终估计常数。

仍为坐标盒及光滑状态；原闭区间 C² 的匹配延拓、完整弱轨道与一般凸多面体待。AUXILIARY，P024 不提升，覆盖17/26。详见 `analysis/T155-c2-heat-estimate.md`。

## T156 / C172：原闭区间 C² 权的匹配周期延拓（辅助）

`PeriodicPrimitive`、`PeriodicC2Extension`、`BoxIntervalC2HeatEstimate` 共五声明。真实连续二阶导数经 AddCircle 延拓后积分两次，实际 FTC、端点匹配和周期积分给全局 C² 周期 Q，并在整个 Icc 上恢复 q、derivWithin q 和二次 derivWithin。最终 `box_interval_C2_gaussian_heat_both_signs` 内部供应延拓及 qclass，再以真实柱积分相等换回原 q。原 C²([0,T])、零至二阶端点条件已保留，无新延拓假设；同常数顺序及两个时间符号不变。

状态仍 C∞ 周期零边界，区域仍坐标盒；完整弱轨道及一般凸多面体未完成。仍 AUXILIARY，P024 不提升、覆盖17/26。详见 `analysis/T156-interval-c2-heat.md`。

## T157 / C173：逐坐标全偶空间核与真实 L² 逼近（辅助）

实际逐坐标反射平均构造 C∞ 紧支、非负、单位质量、支集收缩的全偶核；不假设通用 ContDiffBump 径向对称。真实反射换元给局部奇函数卷积在对应平面严格为零。实际反射 Lp 和卷积平均恒等式传递全部 L² 状态的 a.e. 收敛，再以 L² 收缩证明平方误差及 L² 强收敛。五模块29声明。

局部奇性尚为明确输入；本批不声称已完成盒奇延拓、保持零边界的 H² 逼近或完整弱轨道。范围 AUXILIARY，P024 不提升、覆盖17/26。详见 `analysis/T157-even-spatial-mollification.md`。

## T158 / C174：实际全盒局部奇延拓与零边界平滑（辅助）

真实反射Lp差、同面奇性及异面交换保留局部奇性；两次同坐标反射后下端局部带内上端反射项严格消失，保留两个原面。加强原Poisson扩展见证以保存零延拓的精确Lp公式，再有限坐标迭代，保留原弱方程、Dirichlet归属、原域恢复及4^card界。实际全偶卷积在足够小半径下同时对整个原frontier严格零值，且全局C∞。局部弱一、二阶实际导数L²强收敛亦内部证明。七模块25声明。

尚须把扩展H²正则性与原域字段恢复接到同一序列，以得原域H²图范数逼近，再完成弱周期轨道。仍 AUXILIARY、P024不提升、覆盖17/26。详见 `analysis/T158-odd-box-boundary.md`。

## T159 / C175：完整盒 H²∩H¹₀ 的严格零边界光滑密度（辅助）

任意原弱H² jet且H¹截断属于H¹₀，先以实际负Laplacian作右端构造奇Poisson扩展，再用扩大盒的已证H²正则性；实际值唯一性恢复原盒全部jet。全偶卷积对原盒闭包紧内强收敛，经真实测度限制与字段恢复，得到原域值和全部一二阶实际坐标导数的L²极限。该卷积值就是已证局部奇延拓的卷积；取尾序列后每项C∞且在整个frontier严格零值。三模块四声明。

完成空间H²密度，尚未接入全部周期时空图空间和弱CE，且区域仍坐标盒；仍AUXILIARY、P024不提升、覆盖17/26。详见 `analysis/T159-box-h2-density.md`。

## T160 / C176：真实盒 Dirichlet 算子图的光滑零边界密度（辅助）

固定紧支截断保持原盒上全部实际方向导数，将 T159 空间 H² 密度加强为真正 SpatialTest 序列。实际二阶导数与 Laplacian Lp 对齐，有限 Lp 求和给负 Laplacian 强收敛；原凸域 H¹₀ 归属及弱 Poisson 图等价内部供应每项的实际 Dirichlet 域和算子身份。最终对任意原盒 Dirichlet 算子图元素，构造严格零边界全局紧支光滑序列及同一实际算子图序列，值和算子分别为原 Lp 类并在完整空间图范数中收敛。四模块十声明。

周期时间图密度、完整弱 CE 及一般凸多面体仍待；AUXILIARY，P024 不提升、覆盖 17/26。详见 `analysis/T160-box-graph-density.md`。

## T161 / C177：实际完整盒弱周期图的光滑零边界密度（辅助）

原实际算子图上的谐波系数映射由闭图定理证连续；实际常系数周期解算子把载荷谐波稠密性转成完整弱周期图的有限谐波稠密性。显式空间光滑系数给真实全时空 C∞、严格周期、全时间全边界零值代表。任意空间图系数由 T160 逼近，经谐波连续性进入该真实子空间闭包。最终任意原弱周期图 p 都有 P_n→p（含连续迹一致范数、弱时间导数 L²、实际算子 L²），及逐项满足上述条件并在每个闭区间时刻与 P_n 迹 a.e. 相同的实际函数 F_n。四模块十六声明。

经典 ∂t/负 Laplacian 与图字段的显式识别及实际积分弱 CE 极限继续；一般凸多面体仍待。仍 AUXILIARY、P024 不提升、覆盖17/26。详见 `analysis/T161-box-periodic-density.md`。

## T162 / C178：经典时间导数与负 Laplacian 的完整图逼近（辅助）

真实方向微分及空间 Laplacian 线性性、原谐波 Bochner 字段身份内部证明。构造带同一实际光滑 F 的更强周期图子空间，逐项保留全时空 C∞、严格周期、全时间全边界零值、每个 Icc 时刻迹身份，以及时间 a.e./空间 a.e. 的实际经典 ∂t 和负 Laplacian 字段。真实谐波系数值/算子身份及 T160 空间图逼近给该子空间在完整弱周期图中稠密；最终对所有原弱周期轨道输出同一序列及精确经典字段身份。五模块十三声明。

空间梯度和实际加权柱积分的识别、完整弱 CE 极限及一般凸多面体继续；仍 AUXILIARY、P024 不提升、覆盖17/26。详见 `analysis/T162-classical-periodic-density.md`。

## T163 / C179：完整弱周期图的真实梯度和加权热能量连续性（辅助）

实际能量字段由原 resolventEnergy(1)(Au+u) 的 Bochner CLM 构造，并嵌回原值。弱 H¹ 值唯一性内部给同一光滑代表的真实弱梯度；将原 dirichletGradient 作用于该能量字段，得到完整图连续的真实空间梯度。复用原 timeMap 证明 timeSq 为加权 Bochner 范数平方，原 q³ 值、q 梯度、ε∂t+A 残差和观察 cutoff 四项均连续。五模块十八声明。

同一权和同一常数下的光滑 core CE 可由完整图密度延拓到全部弱轨道；此处明确保留光滑 core 不等式前提，实际柱积分与 Bochner 四项的对接仍待，未声称完整弱 CE。一般凸多面体仍待；AUXILIARY、P024 不提升、覆盖17/26。详见 `analysis/T163-weak-heat-continuity.md`。
