# T167 / C183 独立本机验收：完整 Cartesian 盒热差分 Carleman 估计

- checked_sha / source_sha: `d4b7f2d6d6894520fc5db06dc3a230be27518297`
- mathematical_base: `28789e8973368055acc0c17d5b395332e6ee7364`
- reviewed_at: `2026-10-19T13:07:48+00:00`
- reviewer: 独立本机 Agent `/root/accept_section3`
- result: **PASS**；axiom_check: **PASS**；scope: **AUXILIARY**。
- 三模块七项声明通过。C183 可升级为 REVIEWED，并保持 AUXILIARY；完整原文覆盖仍为 **17/26**，不据此提升一般 P024、P1 或其他一般几何结论。

## 原文与固定审查范围

已独立读取固定源码中的三模块全部证明、七项完整展开类型、关键依赖及实际原文。对照 `paper/main.tex:579–585` 的 `eq:rawCE`、`617–623` 的 `cor:scales`、`1634–1676` 的原物理 Cartesian 空间/差分/载荷/测试，以及 `1684–1706` 的精确刚度与 Section 6 末尾实例结论。本批确实将实际盒 Dirichlet 连续 CE、空间解析数据和已证明的原数值对象组合到原热尺度下的全状态差分估计；没有把抽象 transfer 前提改写名称后视为已清偿。

遵循固定 AGENTS、PROJECT_OPERATIONS、state/README，核对 MATH_SPEC 的 T167 段、`analysis/T167-box-cartesian.md`、C183/T167 和固定声明清单。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，未修改。动态 `.ci/axioms.txt`、未来 PhysicalFiniteLp、PhysicalFiniteWeights、PhysicalIntervalQClass 等草稿完全排除。

范围是任意固定正边长坐标盒、非空开观察集 W⊆Ω、开控制区域 ω 且 closure W⊆ω，以及固定步长可比界 ratio≥1。W 的闭包紧性由 W⊆有界盒内部推出。网格可有任意原点 o、正各向步长 δ 和整数 N，只要求其实际开盒等于固定 Ω，并满足 h/ratio≤δⱼ≤h；原文 h=max δⱼ、Nⱼ≥2 的网格全部包含。结论不要求原点为零、各向步长相等、状态滤波或给定离散 PDE 解。

## 七项声明逐项验收

位置均指 checked_sha，Lean 路径相对于 `Carleman/`；raw 行是固定完整类型的起始行。顺序与 `/tmp/carleman-t167-box-cartesian-declarations.json`、C183 和 T167 一致。三模块均导入固定根目标，七项均有实际 `#check` 与 `#print axioms`。

| # | 声明 | 固定源码位置；raw 行 | 独立结论 |
|---|---|---|---|
| 1 | `Carleman.cartesianLoadInterfaceOn` | `Transfer/CartesianHeatGeometry.lean:14`；32521 | PASS。沿真实域等式运输原 Reconstruction 与其实际 LoadInterface；`subst S` 后就是原对象，无新载荷或兼容性假设。 |
| 2 | `Carleman.cartesianLoadInterfaceOn_Γ` | `Transfer/CartesianHeatGeometry.lean:20`；32530 | PASS。运输后 Γ 仍对每个原物理状态精确为恒等，非仅满射或范数等价。 |
| 3 | `Carleman.cartesianHeatState_definite` | `Transfer/CartesianHeatGeometry.lean:26`；32534 | PASS。实际节点权 exp(qρ) 严格非零，真实物理加权范数为零推出完整节点状态为零。 |
| 4 | `Carleman.cartesianHeatControl_definite` | `Transfer/CartesianHeatGeometry.lean:35`；32539 | PASS。同样对实际 ω 内节点子类型的物理控制空间证明确定性；空控制索引也合法。 |
| 5 | `Carleman.cartesianHeatGeometry` | `Transfer/CartesianHeatGeometry.lean:45`；32545 | PASS。状态与载荷使用同一个实际物理范数，控制使用真实限制空间范数；空间一阶项是原 Sobolev 弱梯度。 |
| 6 | `Carleman.cartesian_numericalData_on` | `Transfer/CartesianTransportedData.lean:12`；32559 | PASS。原统一数值数据仅作依赖域运输，所有阈值/常数、误差阶、真实测试与算子保留；此辅助项仍显式接收 hD 和小量条件，最终第 7 项内部供应。 |
| 7 | `Carleman.box_cartesian_heat_estimate` | `Transfer/BoxCartesianHeatEstimate.lean:18`；32614 | PASS。盒 H²/允许权族/N1–N5/原弱轨道 CE 全部内部清偿，原 4/5、2/5 尺度给两方向全部周期离散状态的实际 rawCE。 |

## 原物理空间、算子、载荷与梯度

实际读取 `PhysicalFiniteSpace`、`CartesianPhysicalSpaces`、`CartesianPhysicalNorms`。状态空间与全部内部节点函数线性等价，但范数从正内积 `mass·Σ fᵢgᵢ` 直接构造，mass=∏δⱼ；其有限维和完备性由此内部证明。没有将函数 sup 范数作为原物理范数，也没有使用依赖节点数的范数等价。真实乘子逐节点为 σ(xᵢ)，故状态范数平方精确为 `(∏δⱼ)Σσ(xᵢ)²zᵢ²`。载荷空间 F=X，载荷范数就是同一个状态范数。控制空间是 xᵢ∈ω 的实际内部节点子类型，质量仍为同一个 ∏δⱼ。

`cartesianPhysicalControlExtension` 是实际节点零延拓的 CLM，其 Hilbert adjoint 由原物理配对恒等式证明精确等于节点限制。最终观察项直接使用该 `.adjoint`，没有拿任意线性映射命名为 B*。节点权的正性来自真实 exp 严格正，即使 ρ 在一般辅助声明中只可测有界，也足以证明第 3、4 项的确定性。

实际读取 `CartesianReconstructionInterface`、`CartesianPhysicalStiffness`、`CartesianFiniteDifference`。R 是原 Kuhn 帽函数重构的真实 L² 类，且属于原 H¹₀；J 是真实 Hilbert 伴随，并具有 `mass⁻¹(u,φᵢ)` 的原矩表达式，Q=RJ、G=JR。载荷 lift 是已构造的实际 L² 载荷，其真实 J 右逆身份供应 LoadInterface.compatible。新域运输 `hdom ▸ r` 只识别相同空间域，Γ=id 的定理对任意 hdom 证明成立；未增加几何同构的尺度因子或更换 R/J/lift。

实际 Laplacian 在每个内部节点精确为 `Σⱼ(2zᵢ−zᵢ₊ₑⱼ−zᵢ₋ₑⱼ)/δⱼ²`，邻接边界由原节点零延拓处理。对独立 z、v，其物理配对等于原 Dirichlet scalarForm(Rz,Rv)，原形式为全弱梯度 L² 内积，没有零阶质量项，刚度缺陷 b=0。算子的自伴和非负性质在固定依赖中已证明。

`heatGradientExpression` 的零阶系数为零，一阶系数为真实恒等 CLM，作用恰为原一阶 DerivativeFiber；`conforming_heat_expression` 对真实 Rz 给原完整弱梯度。它不是数值差商的随意代用品，也不是 ∇(θRz)。记 qₙ=q(tₙ)、θₙ=exp(qₙρ)、mδ=∏δⱼ，最终左侧准确为

`δt Σₙ [qₙ³ mδ Σᵢ θₙ(xᵢ)² zₙ,ᵢ² + qₙ ‖θₙ D¹(Rzₙ)‖²L²(Ω)]`。

右侧准确为原物理范数中的 `δt Σₙ ‖θₙ(Dₛz+Aₕz)ₙ‖²X` 加 `δt Σₙ qₙ³ ‖θₙ B* zₙ‖²U`。`weightedSq` 与 `powerSq` 是实际带 δt 的有限和，指数分别为 3、1、0、3，时间节点一致。原 TimeGrid 用循环索引、T=steps·δt，Sequence 为全部索引函数；两种 Orientation 对应原 D₊、D₋，包括首尾循环项，不是只在内部时刻的差分。

## 解析、数值与连续 CE 前提的实际清偿

`box_analytic_data_uniform` 对原完整 associated operator 域内部调用已证明的盒 H² 正则性。真实 canonical H² jet 通过 value 唯一性与正则性输出识别，得到 `‖jet(z)‖≤Creg‖Az‖`；hD 不是新增前提。盒的有界 Lipschitz 几何也由实际 `openCoordinateBox_bounded_lipschitz` 构造。全允许权族由 `dirichlet_allowed_family_uniform` 供应，包括 σ 与 σ⁻¹ 的真实域资格、原形式上下界及实际共轭交换子；常数在全部 w、τStar 前选择，不假定任意原状态额外光滑。

`cartesian_numericalData_on` 直接来自已证明的同一 `cartesian_numericalData`。已读取它的全部组装及关键实现：实际精确刚度；原全部 H²∩H¹₀ 状态的 Q 逼近；同一个原对角测试 `σ(xᵢ)²zᵢ` 及其真实时间导数、对称/非负性、超逼近；真实重构双向比较、载荷界和控制伴随观察界。误差精确为 `aE=Capp·h`、`a₀=Capp·h²`、`ηA=0`。一般辅助运输项保留的 hD 与 `h·w.max≤ε`，在最终盒定理中均内部证明。

未将 NumericalData 的较小字段集合误认原全部 N1–N5。另已读取固定、与接受版本相同的 `cartesian_full_weight_interface` 及其依赖：原同一测试及导数身份、严格正性、全部允许权的质量/载荷/测试双向比较和实际 Hilbert 伴随观察均成立；重构质量伴随与 Γ=id/右逆已在原 LoadInterface 中供应。C158 的完整原命题验收范围没有被本批缩减。最终调用 τStar=2，因为原热指数 d*=1、b*=4，所需 `max(d*/2,b*/2)=2`；底层允许权和测试定理仍支持任意非负 τStar，包括原实现允许的 4。两种空间权符号及全部所需 τ 均被覆盖。

T166 的 `box_heat_continuous_data` 直接以原全部 `PeriodicWeakTrajectory` 为输入，利用 T165 的真实轨道到完整图身份及原区间 C² 估计，清偿 transfer 要求的同符号连续 CE。实际能量/残差/观察等式把原弱梯度和 `s.sign·u′+Au` 与 transfer 对象逐项识别；A=−Δ，符号没有翻转。这个结论与任意数值 X/F/Y 和其范数无关，其常数在这些数据及 g/w 前选择。最终没有 CE、H² 正则性、数值测试估计、给定平滑逼近、频率过滤或 PDE 解条件作为显式前提。

## 原尺度、统一量词与全部状态

选择次序是：固定维数、盒、W、ω、ratio；从实际连续 CE 取得 c、λ、β、qc、Cce；从盒解析结果取得 Creg、Ca、Ccomm；从真实数值实现取得 ε、Ctime、Csuper、Capp、Cnum；再由原 `heat_scale_uniform` 取得 κ₀、h₀、Δ₀、C。所有这些量在 o、δ、N、h、g、w、s、z 之前，且两种方向共享同一组参数。最终空间相位为原负高斯相位，λ≥1、−2<ρ≤−1，0<β≤1、qc≥1。

实际检查 `ScaleUniform`、`ScaleSmallness`、`ScalePowers` 和热指数恒等式。`νE=2`、`ν₀=5` 给准确 `αx=4/5`、`αt=2/5`；aE、a₀ 的原阶数直接代入，刚度缺陷零。缩小 `κ=min(κ₀,ε)>0` 不改变任何指数或 C。由

`Q=w.max≤κ min(h⁻⁴⁄⁵,δt⁻²⁄⁵)`、`0<h≤h₀≤1`

得到 Q≤κ₀min(...) 以应用原尺度推论；同时 `scale_monomial_le` 取 p=ν=1、α=4/5，真实实幂运算给 `hQ≤κ≤ε`。此处使用 `1−4/5≥0` 与 h≤1，方向正确，没有把 h 的负幂当正幂。原数值阈值及观察网格小量因此全部消去；时间和 transfer 吸收小量由原尺度推论内部处理。Δ₀>0、h₀>0，并各自≤1。

权输入确为 `IntervalQClass w.q g.period β qc`：Icc 上 C²、0/1/2 阶端点匹配、q≥qc、`|q′|≤βq²`、`|q″|≤β²q³`；`toRegularity` 从这些原假设证明 transfer 所需正则性。数值载体仍是 `TimeWeight`，其 max 是实际统一上界，允许在该上界下任意原区间权；本定理不另要求区间外光滑或周期。结论的实际类型以 w 承载，不将它描述成此处新定义了一个任意裸函数 q 的物理接口。

最后取实际残差 `f=Dₛz+Aₕz`，用运输后的 Γ=id 逐节点证明载荷方程，然后使用尺度推论的载荷版本。F=X 且 load=state，故其 loadSq 定义上就是原右侧残差平方和；没有另乘逆载荷常数，也没有对 z 增加方程约束。任意 s、任意完整周期 z 均成立。原 Nⱼ≥2 与时间步数≥2 的全部情形包含；接口允许更小合法索引时的空状态等情况是扩展，不是对原状态的限制。

## 固定依赖、公理与本机构建

新三模块的递归 Carleman import 闭包为 **746** 文件，其中 **743** 个旧文件与 mathematical_base 逐文件完全相同。关键已接受版本的相关完整闭包再次逐文件比较，均无变化：

| 依赖 | declaration_version | 比较入口；文件数 |
|---|---|---|
| C182 / [T166](T166-local-acceptance.md) | `28789e8973368055acc0c17d5b395332e6ee7364` | Transfer/BoxHeatContinuous；386 |
| C158 / [T142](T142-local-acceptance.md) | `13c8977bd4c50a11d6bed5fdab64b09aeee0203f` | Spatial/CartesianNumericalData；569 |
| C159 / [T143](T143-local-acceptance.md) | `90ca06c7cd42fae4b870fae9a67219fa729226f7` | Spatial/BoxAnalyticData；362 |
| C011 / [T023](T023-local-acceptance.md) | `8706e95e3a24b09fe6e2675a0c72c827ba9a93f3` | Transfer/HeatScaleUniform；247 |
| C125 / [T109](T109-local-acceptance.md) | `b1611e7c3fe37e6b3ed31556e932f61b657e2be1` | Spatial/CartesianPhysicalStiffness；316 |
| C122 / [T106](T106-local-acceptance.md) | `337d9c1b8c5fadce4e638a2c96311e230ee94bb1` | Spatial/CartesianPhysicalSpaces；310 |

额外读取的 CartesianFullWeightInterface 本身与 C158 固定版本相同，其重要依赖已在上述实际比较内。新增实现无 sorry、admit、axiom、native_decide；没有引入数学循环或以目标离散估计充当数值前提。

Lean pin 为 `leanprover/lean4:v4.35.0`，实际 CI 编译器 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`。mathlib pin/本机实际干净 checkout HEAD 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。配置与基线一致。固定定向 `-target3.log` 实际 **3976 jobs** 成功，根 `-build.log` 实际 **4088 jobs** 成功。

`-axioms.log` 是空 stderr，未用作 PASS 证据。固定 raw 有 **3027** 个依赖公理记录及 **9** 个无公理记录，所有记录仅含 `propext`、`Classical.choice`、`Quot.sound`；七项新声明的完整类型及公理集合逐项核实。实际检查器用 `privateToUserName` 覆盖 Carleman 全部常量并递归 `collectAxioms`；末行明确为 `Axiom audit passed for all 8035 Carleman declarations.`，不是只审计七个入口。

## 独立正式 CI 与原始工件

验收者自行查询 [run 39256167609 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39256167609/attempts/1)，确认 main / push，`head_sha=d4b7f2d6d6894520fc5db06dc3a230be27518297`，最终顶层 `completed / success`，最后更新 `2026-10-19T13:01:27Z`。三个正式作业均最终成功：

| 作业 | job ID | 结果 |
|---|---|---|
| state-check | `118071886312` | completed / success |
| lean | `118071886839` | completed / success |
| dashboard / snapshot | `118073458369` | completed / success |

自行使用 `gh run download` 下载同 run 两个原始工件，未借用主执行者副本。结果 JSON 首次下载发生 TLS 握手超时，原路径无结果文件；原样重试退出 0。公理工件下载退出 0。

| 工件 | artifact ID；ZIP 字节数 | 独立本机路径 |
|---|---|---|
| lean-ci-result | `12187683509`；493 | `/tmp/carleman-t167-box-cartesian-main-ci/result.json` |
| lean-declaration-evidence | `12188125226`；232000 | `/tmp/carleman-t167-box-cartesian-main-axioms/axioms.txt` |

两工件 workflow_run SHA 都绑定本固定证明版本。API ZIP digest 分别为 `sha256:76c19d289209e6df6e17404b2719829036a83cf92141bab9c60069123ab0d249`、`sha256:0fd6162360acb793441711b04505f234cfc4b38e0f9ae9b79b3d2eade5f12360`，与解压后的 raw 哈希分开记录。

实际 result.json：`status=PASS`，`checked_sha` 与 `source_head_sha` 均精确等于报告首部固定 SHA，目标 `Carleman`，`finished_at=2026-10-19T13:00:15.498222+00:00`；Lean/mathlib 与固定 pin 一致。远端 raw 与 `/tmp/carleman-t167-box-cartesian-local-axioms.txt` 独立逐字节比较完全相同，均为 **2494005 bytes**，SHA256 **`0e239b6fe52e852dbd6c02a769a3cfff3db06740ee934cf8820d76978a21f307`**。

## 签发

**C183：PASS / AUXILIARY。** 原物理 Hilbert 范数、Kuhn 重构弱梯度、真实差分及控制伴随、Γ=id 载荷、解析/数值/连续 CE 前提清偿、原尺度与统一量词均通过，未发现阻断缺陷。仅确认本固定盒 Cartesian 实例的全状态双方向 rawCE，不提升一般 P024 或其他原文覆盖；保持 17/26。仅提交本报告，不修改实现、台账或原稿，不推送；通知后正文和 reviewed_at 冻结。
