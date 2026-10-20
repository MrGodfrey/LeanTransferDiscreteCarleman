# T269 / C285：原 Theorem 7.5、Corollary 7.6 独立整体验收

- checked_sha / source_sha：`b04fcf4526dac2c76c92f4d3155fc4e5763e947b`
- mathematical_base：`5458c11848a69d56199fb5e13d517b58eb38953b`
- reviewed_at：`2026-10-20T12:31:45+00:00`
- reviewer：独立数学验收 Agent `/root/accept_section3`
- result / axiom_check：**PASS / PASS，3/3 声明通过，无阻断缺陷。**
- scope：**PAPER P017 / Theorem 7.5（thm:filtered-observability）及 P018 / Corollary 7.6（cor:filtered-control）**。完整原 P1 与 Cartesian 两分支均覆盖，可将 C285 及这两项原文结果登记 REVIEWED；本报告不修改台账。
- evidence_source：**local**。按现行协议核验固定源码、本地真实构建及递归公理产物；未查询看板、远端 CI，未重复全库构建。

## 原命题和全部声明

直接读取固定 Git 中的新模块、两个既有最终入口、三个完整展开类型、实际过滤/HUM/空间算子依赖、T269 分析与 MATH_SPEC。另读取固定治理协议和原稿 Section 6 的两种原实现、Section 7 的物理方程与条件、2136–2223 行的过滤结果，以及附录过滤证明。原稿与数学基线及已验收版本未变，SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

原 Theorem 7.5 要求在原 physicalconditions 和原两个 gap 不等式下，对任意终态属于 F 的完整物理伴随解成立 `‖p⁰‖² ≤ 2 C0 dt Σ‖B*pⁿ⁻¹‖²`。原 Corollary 7.6 要求对每个原初态构造同一完整正向系统的控制，使实际正交投影 `Π_F yᴺ=0`，控制成本不超过 `sqrt(2 C0)‖y0‖`，且**完整**终态范数满足原指数率。既非仅给 F 上的抽象观测，也非仅给投影误差。

下表为本次全部三个声明，均在 `Carleman.Physical` 命名空间；源码路径相对于 `Carleman/Control/`，raw 行指固定原始公理产物。

| 声明 | 固定源码 / 完整 raw 行 | 独立结论 |
| --- | --- | --- |
| `finite_halfspace_p1_filtered_observation_control` | `FiniteHalfspaceP1FilteredControl.lean:16` / 46283–46367 | 新联合定理；一般有界凸多面体上的完整原 P1 状态、真实 L²(ω) 控制，内部供应物理观测后同时给原过滤观测、完整正向控制、正交终态消去及完整终态指数界。PASS。 |
| `box_cartesian_filtered_observability` | `BoxCartesianFilteredObservation.lean:15` / 33145–33242 | 既有完整盒 Cartesian 入口；真实质量、原 FD 刚度及 B*，任意终态子空间和每个真实物理伴随解，准确 2 C0 常数。PASS。 |
| `box_cartesian_filtered_control` | `BoxCartesianFilteredControl.lean:15` / 33406–33511 | 既有完整盒 Cartesian 控制入口；原全部初态、实际节点控制与 N+1 正向轨迹、sqrt(2 C0) 成本、实际正交投影零及完整终态指数界。PASS。 |

三个类型均已完整读取，包含所有 `let` 空间、量词顺序、物理方程和实际结论；未以台账名字、执行者摘要或编译成功代替语义检查。

## 原空间、网格、势和控制

P1 入口的域是任意有界有限严格仿射半空间交，非空由开且非空的 ω⊆S 供给。维数写成 `d+1≤3`，完整包含原 d=2,3，并额外允许一维。原有界凸多面体与原紧包含观测设置均满足这些前提，没有添加边界光滑、正则性、密度或目标观测假设。

真实状态是 `M.conformingSpace (dirichletSubspace S)`。其实际定义及 `mem_conformingSpace_iff` 确认是完整 H¹₀ 中逐单元仿射的原 L² 类，而非仅某个预选节点族。内积为原一致 L² 内积。`galerkinStiffness` 由原 Dirichlet 能量形式及真实 Riesz 对偶定义；`galerkinStiffness_form` 精确给出原梯度配对，内部证明对称、非负和零刚度缺陷。

重新检查 FaceMatching 与 BoundaryFitted 的定义：前者用共有顶点的凸包描述单元交，后者用边界顶点的凸包覆盖单元的边界部分，均是原一致边界贴合网格的几何编码。实际正内球和 diameter≤shape·r 对应固定形状正则性。ℓ 的两侧直径比较和共享顶点单元间 `ℓ_j≤γℓ_i` 保留原 grading；交换 i,j 得反向比界。`1≤γ<Γ_d` 未被收紧，shape/cmesh/Bmesh/γ 在所有具体网格之前固定。

P1 势为实际 `Π_X ∘ b.map ∘ inclusion`。`BoundedMultiplier` 的 a.e. 实有界输入覆盖原 L∞ 势；其实际配对为原 `∫ b y z`，投影及乘法的对称性和算子范数≤M 内部清偿。没有错误要求一般乘子保持 P1 空间。`conformingRegionControl` 的控制空间是实际区域 L²，B 为零延拓后正交投影，B* 为真实区域限制；由 ω⊆S 识别原 L²(ω)。控制空间不被限制为有限维节点空间。

Cartesian 分支覆盖任意正维固定盒、原相互可比的正轴向步长和全内部格点状态。`CartesianPhysicalState`、`CartesianPhysicalControl` 的实际 Hilbert 内积均使用 `(∏δ_j) Σ f_j g_j`；控制索引是真正位于 ω 的内部节点，B 是实际零延拓，Hilbert 伴随是限制。原 `(2d+1)` 点负 Laplacian、自伴性、非负性及任意有界实节点势均由已证实际实现供应。没有网格依赖范数等价常数，也没有把 P1 的维数限制加到 FD 分支。

Cartesian 的辅助 W 为原内观测区，`closure W⊆ω` 是原观测设置；原网格盒与固定盒相等。取 h 为最大步长即原参数，固定 ratio 只表达原步长可比界。这里覆盖两个原 proposition 的实现范围，不把 Section 6 中未命名的伸缩网格推广 remark 另计为已证明结果。

## 任意 F、真实 Rayleigh 上确界和过滤吸收

`filterRayleigh A F` 在 F=⊥ 时准确为零；否则是原非零向量商 `(Ax,x)/‖x‖²` 的真实上确界。直接检查 `rayleigh_le_filterRayleigh`：用实际 ‖A‖ 证明该集合有上界，从而合法使用实数 sSup；‖A‖ 仅在这一步保证上确界存在，不进入最终常数。A 非负给 Λ_F≥0。

`filter_reverse` 作用于实际全 Hilbert 伴随方程。终值为零单独处理，非零终值的真实 Rayleigh 商经已验收有限迭代估计和上确界比较，得到

`K_F = exp(T Λ_F + M T + M² T²/2)`，`‖pᴺ‖≤K_F‖p⁰‖`。

其对称性、非负性和势界均从本次实际 Galerkin/FD 算子内部供应。F 只约束终值；从未要求 A、势、每一步解或演化算子保持 F。零子空间、全空间及任意其它子空间均可输入；无额外基、维数、谱投影或粗网格来源假设。

`filter_condition_budget` 由原两个 gap 不等式精确推出 `4 C0 exp(-2 d0 S) K_F²≤1`。乘上原真实反向范数界的平方，原观测余项至多为 `‖p⁰‖²/4`；在同一观测式中吸收，得到准确的 `2 C0 dt Σ‖B*pⁿ⁻¹‖²`。未更换观察时间层，未把包含未知解的目标估计当作输入。

## 真实补空间 HUM 与完整终态

重新读取 `ComplementaryObservation`、`ComplementaryHUM`、`FilteredControl`、`PhysicalComplementaryHUM` 及物理方程桥。令 R 为真实终值到初值的伴随演化，O 为带 sqrt(dt) 的真实观察映射，P、Q 为 F 与 F⊥ 的实际正交投影。由 `R(Pz)=Rz−R(Qz)`、原反向界和正交平方分解得到全状态补空间观测；此处不假设 R 与 P 交换。

实际惩罚参数为 `η=exp(-d0 S) sqrt(1+2 exp(2MT)² K_F²)`。HUM 使用真实 `O*O+η²Q`；正交配对及观测界给单射，有限维状态给满射，且真实 R 为单射。控制空间仍允许无限维完整 L²(ω)。Euler 方程给实际终态 `R*y0+O*v=η²Qz`，因此 P 作用后严格为零，并控制其完整范数。没有只估计 Q 的某个替代值。

`FilteredControl` 将 Hilbert 控制向量按 `(sqrt(dt))⁻¹` 还原原 u。实际范数身份给 `controlNorm dt u=sqrt(dt Σ‖u_i‖²)`。`existsUnique_forward` 构造整个 y，真实离散对偶恒等式将其终态识别为上述 HUM 终态，而非仅声明存在一个满足抽象线性方程的向量。

展开最终方程，i=0,…,N−1 对应原 n=i+1：

- 正向为 `dt⁻¹(y(i+1)−y(i))+(A_h+V_i)y(i+1)=B u_i`，并明确 y(0)=y0；
- 伴随为 `dt⁻¹(p(i)−p(i+1))+(A_h+V_i)*p(i)=0`；
- 观察为 `dt Σ‖B*p(i)‖²`，终端为真实 p(N) 或 y(N)。

最终轨迹没有周期性附加前提，控制未改变细网格方程。原每个初态、每个满足方程的伴随解均覆盖。

## 同一个 C0 与原统一量词

先固定域、观测区及原形状/分级或步长可比界，再选择 qc、κ、h0、Δ0、Cb、d0，全部先于 T、M。对每个 T>0、M≥0 选 C0，先于所有网格、时间步、势的具体值、F、θ、初态和解。特别是没有将 F 依赖隐入所谓物理常数。

保留原 `qb=Cb(qc+T⁻¹+M^(2/3))` 和 `S=κ min(h^(-4/5),dt^(-2/5))`，以及 h≤h0、dt≤Δ0、dt≤T/12、dt M≤1/2、`16 qb≤S≤qb T/(4dt)`。原 0<θ<1 全部包含在更一般的显式 gap 前提中，未要求额外正谱隙。M=0、F=⊥、零初态的分支合法，没有除以 M、Λ_F 或未知非零解。

完整终态系数必须和原 C(T,M) 的统一性相容。本批明确选择

`J(T,M)=sqrt(1+2 exp(2MT)²) exp(MT+M²T²/2)`，

`C0=max(1,max(Cobs,2 J(T,M)²))`。

原 Section 7 说明 C(T,M) 是可统一选取的 generic 常数；可先将物理观测常数取为此 C0，此时原 `max(1,C(T,M))` 仍是同一 C0。非负右端保证原物理观测对该放大常数成立。该选择在网格和 F 之前完成，gap 始终使用所选的同一 C0，没有先检查较小常数的 gap 再偷偷放大。

由第一条 gap，`filter_penalty_decay` 得 `η≤J(T,M) exp(-(1−θ)d0S)`；预算 `2J²≤C0` 给 `sqrt(2 C0) J≤C0`。故同一实际控制同时满足成本 `sqrt(2 C0)‖y0‖`、`Π_F yᴺ=0` 及 `‖yᴺ‖≤C0 exp(-(1−θ)d0S)‖y0‖`。指数和全部终态范数均与原文相同，常数无 F、dim(X_h) 或 ‖A_h‖ 依赖。

P1 的联合结论直接使用这一共同 C0。两个旧 Cartesian 定理分别导出存在常数，不能仅凭两个存在量词就声称其 witnesses 自动相同：控制入口的实际证明先构造上述放大 C0 下的全伴随 `ho`，同一个 `ho` 和同一 gap 也正好满足已证 `filtered_observation_of_relaxed`，从而可使用共同常数。旧独立观测入口所取的较小 `max(1,Cobs)` 不是控制论证必须保留的额外限制。此核对清偿原两命题共用物理常数的问题，无需改变原条件。

## 前置报告与不变依赖

本次三入口的实际 Carleman 导入闭包共 **875** 个模块：一个新模块，其余 **874** 个与数学基线逐 Git blob 相同。另独立逐文件核对以下已验收边界：

| 闭包入口 | 接受的 proof SHA | 模块数及比较 |
| --- | --- | --- |
| `FiniteHalfspaceP1PhysicalControl` | `5458c11848a69d56199fb5e13d517b58eb38953b` | 746，全不变 |
| `BoxCartesianFilteredObservation` | `f6e35f26cc23e5ca84eb8e869a12864be70e7b27` | 762，全不变 |
| `BoxCartesianFilteredControl` | `113b2c6e318ce5cb48f1fda5696223646e0cd2b1` | 768，全不变 |
| `FilterReverse` | `12d18c9c6548cc70165ad9e4c01314f4438dc5f1` | 11，全不变 |
| `PhysicalHUM` | `549cde718bcf26f00b24f4a1493ee92b839f30b4` | 10，全不变 |
| `FiniteHalfspaceHeatContinuous` | `0a1808091e23386fc8c06d4e2a3434d1fa9f2a34` | 450，全不变 |

已全文读取 [T268 冻结报告](T268-local-acceptance.md)，提交 `038447d47db3314106c903723fc9415646d96bad`，reviewed_at=`2026-10-20T12:26:45+00:00`，checked_sha 等于本批数学基线，4/4 PAPER PASS/P014、P015。独立核验报告 16,434 bytes、SHA256 `7da213fd2c74f21f5af3e4e8dd4c44c8f63ac7a3ee1e678e9428249c228a004e`。报告晚于 proof，作为分离的固定验收证据；实际数学依赖已按上表核实，没有把未签发时的 BUILT 台账状态当成接受结论。

T268 实际调用内部清偿完整原域 CE、原 H² 正则性和 P1 全数值条件。本次又核对其实际物理入口和所用空间/势/控制定义，未保留假设物理观测的具体最终接口。全文核对 T267 冻结报告中的原域弱 CE 与真实四场闭包路线：报告提交 `f9c4dc5fb4770e0075bc857beae0900dc01c5edc`，15,035 bytes，SHA256 `fac07126fb063b62952a3a687729a6551bb59f699816e77828afc8b0afc578c4`。

同时读取 T171/T172 旧报告并重新核对本次实际过滤与 HUM 调用。冻结提交分别为 `f102d1571bad357dedf292a90d4ccc6b832db369` 和 `519939f511ea5c60d68d766d127a9914e38d7ef5`；报告 bytes/hash 分别为 12,144 / `5e17a5e0d8b6d820f2a816350e387a8e38526d88d35cc7e4eed23cc6e58ad3f9` 和 18,399 / `2648a53b03db3022c91b0d96f332dddbc4db6322a1eb003aa25bcdb883f1472e`，与本 proof 中版本相同。旧 AUXILIARY 报告本身不是本次 PAPER 晋升依据；本次审查的是两种原实现加已清偿物理观测后的整条证明。

## 精确本地证据与公理

`/tmp/carleman-t269-local-evidence.json` 实际为 PASS/source=local，checked_sha 与 source_head_sha 均等于本报告 proof。记录真实 `lake build Carleman` 及 `lake env lean tools/CheckAxioms.lean` 均 exit 0，finished_at=`2026-10-20T12:19:09.920158+00:00`。文件 932 bytes，SHA256 `ffb02cc81d5ac0776df8de91d53e7d3cd576ee88f7eb17a221e558c07c908335`。

| 固定证据 | 独立核验 |
| --- | --- |
| `/tmp/carleman-t269-local-source-manifest.txt` | 1,083 项，117,576 bytes，SHA256 `a67adda8d9e898933f57f489ce3ab685cc5957a66fcdcb5214a342f15eb11542`。路径集合精确等于固定提交全部 tracked `.lean` 与三个 Lean 配置文件；逐项内容 SHA256 全部与 Git blob 相同。 |
| `/tmp/carleman-t269-filtered-control-local-axioms.txt` | 3,575,380 bytes，SHA256 `e0e3da2180909af0258d6fa929159430a54a2df9e82c3e6681f31a5752281ee4`；末行明确全部 **10,585** Carleman 声明递归审计通过。 |
| `/tmp/carleman-t269-target-build.log` | 实际 `FiniteHalfspaceP1FilteredControl` 3,998 jobs 成功；121 bytes，SHA256 `b844cd19b9b89b7a60416b150754f8bd05c5c8ecfcf41ef3465a262ad2619ccd`。 |
| `/tmp/carleman-t269-root-build.log` | 实际根构建 4,325 jobs 成功；80 bytes，SHA256 `a7d714a999ed1f9940dad5ea4ca6289b461a0452903948222a4e58c6cb979632`。 |

固定根入口导入新模块及两个旧入口。CheckAxioms 的实际递归逻辑对环境内所有 Carleman 声明调用 collectAxioms 并拒绝白名单外公理；不是仅检查公开声明清单。另独立解析 raw 中 4,250 个公理集合与 10 个无公理记录，所有依赖均在 `propext, Classical.choice, Quot.sound` 内；三个受检定理均只依赖这三个正常基础公理。没有 sorryAx 或新数学公理。

Lean 为固定 `leanprover/lean4:v4.35.0`，证据编译器 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；锁定 mathlib 与实际干净 checkout 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。不使用变化中的 `.ci`、T270 未提交文件或旧批次产物。

## 最终判定

**P017 和 P018 均为完整 PAPER PASS，3/3 声明、公理及版本绑定全部通过，无需修复。** 一般凸多面体的原完整 P1 和任意正维 Cartesian 盒分支共同覆盖原文范围；原物理条件、任意终端 F、全状态、真实控制及两个指数率均保持。此前缺少的一般域物理观测已经由 T268 正式接受，故本报告不再只是条件过滤代数或盒实例的 AUXILIARY 验收。

仅本报告单文件提交，不更改实现、台账、根入口或原稿，不 push。签发后 reviewed_at 与正文冻结；后续控制极限等命题不由本报告自动完成。
