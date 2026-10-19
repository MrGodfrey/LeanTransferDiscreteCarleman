# T169 / C185 独立本机验收：Cartesian 物理控制范数与载荷 Carleman 接口

- checked_sha / source_sha: `7d1cc86d3c0a01b524f099ba90baaf59784f159d`
- mathematical_base: `30a03e32af45ef82baacbbfe6917cd7ceff234f3`
- reviewed_at: `2026-10-19T13:27:00+00:00`
- reviewer: 独立本机 Agent `/root/accept_spatial_lemma`，未参与本批数学实现。
- result: **PASS**；axiom_check: **PASS**；全部 **13/13** 显式声明通过。
- scope: **AUXILIARY**；C185 可在该范围登记 REVIEWED。原文覆盖保持 **17/26**，不据本批提升物理观测、控制或一般几何命题。

本报告依据固定 Git 对象中的全部新源码、展开类型、实际证明及关键依赖，独立查询同 SHA 正式 CI 并自行下载原始工件。执行者说明、旧验收报告及编译成功均未代替本次语义核对。后续 T170–T172 工作树、动态根导入和 `.ci/axioms.txt` 不在审查范围；仅新增并单独提交本报告，不修改实现、台账或原稿，不 push。

## 原文、对象和范围

对照固定 `paper/main.tex:1634–1666` 的原 Cartesian 全内部节点空间、质量 `mδ=∏δⱼ`、标准差分 Laplacian、F=X 载荷以及控制零延拓/限制；`1706` 的原热尺度应用；`1717–1749` 的真实物理内积与控制系统；`1900–1949` 的周期截断状态、负向差分载荷方程和带 q³ 观察的 Carleman 使用。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，与基线相同。

读取固定 `analysis/T169-cartesian-physical-load.md`、MATH_SPEC 的 T167–T169 段以及 C183–C185/T167–T169 台账。AGENTS、PROJECT_OPERATIONS、MILESTONES、state/README 的内容哈希与此前已读治理协议一致。本批准确清偿原 Cartesian 物理载荷接口；其结论为 `PhysicalLoadCarleman`，不是完整 `prop:physicalO` 或控制定理。

一般代数项允许任意维数 d、任意正 δ、任意 N 和任意集合 ω，包括空观察节点子类型。最终估计使用维数 d+1、任意固定正边长开盒 Ω、非空开 W⊆Ω、开 ω 且 closure W⊆ω，以及固定 ratio≥1；不要求 ω 的额外边界正规性。原文的 ω₀⊂⊂ω⊂⊂Ω 和 Nⱼ≥2 均被包含。允许更一般 ω 或合法空索引的代数情形，不构成对空观察区可观测性的声明。

## 十三项声明逐项核对

顺序与固定 C185/T169 及 `/tmp/carleman-t169-cartesian-physical-load-declarations.json` 完全一致。源码位置相对于 Carleman，raw 行指固定完整类型的起始行；每项实际类型与公理输出均已独立读取。

| # | 完整声明 | 固定源码位置；raw 行 | 独立结论 |
|---|---|---|---|
| 1 | `Carleman.cartesianPhysicalControl_adjoint_extension` | `Spatial/CartesianPhysicalControlIsometry.lean:13`；32762 | PASS。实际物理 Hilbert 伴随等于节点限制，逐节点限制零延拓得到 B*Bv=v，对全部控制向量成立。 |
| 2 | `Carleman.cartesianPhysicalControlExtension_norm` | 同文件:21；32768 | PASS。由实际 adjoint 配对和第 1 项得到平方范数相等，再用范数非负恢复保范数，常数精确为 1。 |
| 3 | `Carleman.cartesianPhysicalControlExtension_weight` | 同文件:28；32772 | PASS。任意真实节点权乘法与实际零延拓交换，ω 内外两个分支均逐点证明。 |
| 4 | `Carleman.cartesianPhysicalControlExtension_seminorm` | 同文件:41；32778 | PASS。第 2、3 项用于原状态/控制 seminorm，得到加权物理范数精确相同。 |
| 5 | `Carleman.cartesianCountLpEquiv` | `Spatial/CartesianCountWeights.lean:14`；32784 | PASS。使用真实 √mδ 节点缩放的计数 L² 线性等距满射，保留原全部状态。 |
| 6 | `Carleman.cartesianCountObservation` | 同文件:18；32790 | PASS。实际线性映射为 E∘B∘B*，域是原物理状态、值域是完整内部节点计数 L²。 |
| 7 | `Carleman.cartesianCountObservation_norm` | 同文件:25；32798 | PASS。E 和 B 的实际保范数给 ‖EBB*z‖=‖B*z‖U，无质量或节点数损失。 |
| 8 | `Carleman.cartesianCountProfile` | 同文件:33；32803 | PASS。节点相位为 r(xᵢ)，给定全局逐点界实际供应有限计数 SpatialProfile；没有从 Lebesgue a.e. 身份取节点值。 |
| 9 | `Carleman.cartesianCountProfile_seminorm` | 同文件:39；32812 | PASS。任意 τ、t、w 的实际 q(t)^τ exp(r(xᵢ)q(t)) 乘子经 E 精确恢复原状态权范数。 |
| 10 | `Carleman.cartesianCountProfile_observation` | 同文件:47；32819 | PASS。第 9、4 项给同一权下 EBB*z 的计数范数等于原控制权范数，B* 未被替换。 |
| 11 | `Carleman.cartesianInteriorCountProfile` | `Control/BoxCartesianLoadCarleman.lean:17`；32828 | PASS。取真实高斯相位的实际节点值，使用 −2<ρ≤−1 的逐点界，固定 bound=2 与网格无关。 |
| 12 | `Carleman.cartesianInteriorCountProfile_negative` | 同文件:24；32834 | PASS。实际全部节点均≤−1，进而得到计数测度 a.e. 负性；相位与第 11 项完全相同。 |
| 13 | `Carleman.box_cartesian_physical_load_carleman` | 同文件:31；32839 | PASS。完整 T167 CE 内部供应所有周期状态和所有计数 L² 载荷的负向物理载荷估计；原尺度、物理质量、观察范数及统一量词保持。 |

## 真实控制 Hilbert 空间、质量与权交换

直接读取 `PhysicalFiniteSpace`、`CartesianNodalControl`、`CartesianPhysicalSpaces`、`CartesianPhysicalNorms`。原状态是全部内部节点函数，控制指标是真实子类型 `{i // xᵢ∈ω}`。两者内积分别为 `mδ·Σᵢ zᵢvᵢ` 和该式在控制指标上的限制，mδ>0 由每个 δⱼ>0 得到；物理范数由这个 inner core 构造，没有沿用普通有限函数空间的 sup 范数。

实际 B 的节点公式是：xᵢ∈ω 时取对应控制值，否则为零。`cartesianControlExtension_pairing` 以同一质量和真实有限子类型求和证明原配对身份，`cartesianPhysicalControl_adjoint` 再用 Hilbert 内积唯一性得到 B*=restriction。新第 1 项由此退回真实节点限制零延拓身份，第 2 项用 `⟨Bv,Bv⟩=⟨v,B*Bv⟩` 证明保范数，不是只给一个抽象右逆。

第 3 项展开两个实际乘法算子和 B：在 ω 内两边都是 σ(xᵢ)vᵢ，在外两边均为零。σ 不需光滑、非零或正；空控制子类型也不需要例外或除以节点数。第 4 项所用 seminorm 正是实际物理乘法后范数，因此其平方为 `mδ Σ_{xᵢ∈ω} σ(xᵢ)²vᵢ²`，与原文一致。

再次读取 `PhysicalFiniteLp`、`PhysicalFiniteWeights` 的实际构造。E z 的计数 L² 代表是 √mδ·zᵢ，其逆为 fᵢ/√mδ；mδ>0 保证合法，计数测度零测集为空保证逐节点身份。真实平方积分等于 mδ Σzᵢ²，故 E 是原完整物理空间到全部计数 L² 的线性等距满射。有限维自动连续性不提供任何估计损失常数；此处范数身份直接计算。

观察映射 O=EBB* 的实际节点值是 √mδ·zᵢ 在 ω 内、零在外。E 不是把物理质量删去的未缩放嵌入。对任意 τ∈ℝ、t∈ℝ、TimeWeight w 及满足显式逐点界的 r，第 9、10 项用同一乘子计算给出

`‖q(t)^τ exp(q(t)r)·E z‖²count = mδ Σᵢ [q(t)^τ exp(q(t)r(xᵢ))zᵢ]²`，

以及将求和限制到 xᵢ∈ω 后的 O z 身份。r 可以取任一空间符号的相位，代数恒等式不依赖符号；最终 Carleman 使用的是实际负高斯相位，不声称反号相位也满足其负性。

## 节点相位、完整载荷方程和实际 CE 调用

`cartesianInteriorCountProfile` 直接使用 `interiorCarlemanProfile c l`，即 `exp(−l‖x−c‖²)−2`。已有 `interiorCarlemanProfile_bounds` 对每个实际 x 证明 −2<ρ(x)≤−1（l≥0），第 11 项以此得到绝对值≤2，第 12 项在每个节点使用同一界。没有依靠连续域的 a.e. 上界推断有限采样点的性质。最终 l≥1，由真实盒连续估计选取；c 位于 W，所有网格共享同一 c、l。

展开 `PhysicalLoadCarleman`：对所有 `z : Fin g.steps → X` 和所有 `f : Fin g.steps → Lp ℝ 2 count`，若每个 i 有 `g.dMinus z i + A(z i)=E.symm(f i)`，则 q³ 状态平方和由无 q 次数的载荷平方和加 q³ 观察平方和控制。全部范数项都乘实际 g.dt，时间点均为同一 g.nodeTime，权均为 exp(qρ)。`dMinus` 实际定义为 `(zᵢ−z_{next i})/dt`，包括循环末端，正好是原负时间方向，未误用正向差分或把整个空间算子取负。

此抽象接口的参数名 R 在本实例取 E，Γ 取 E⁻¹，观察参数取 EBB*。这只是原物理状态、载荷及观察范数的精确计数表示，并非宣称 E 等于原 Kuhn 重构 Rₕ。原 Kuhn 重构仍在底层 `cartesianHeatGeometry` / `box_cartesian_heat_estimate` 的 nodeEnergy 中；本批先取得完整估计，再由 `zeroth_le_nodeEnergy` 舍去非负 q 加权重构弱梯度项，得到所需 q³ 原物理状态项。

第 13 项的证明逐项构造 hstate、hcontrol、hleft、hload、hobs。hload 使用给定载荷方程逐 i 改写整个负向残差为 E⁻¹f，然后 E(E⁻¹f)=f 精确消去，无右逆损失常数。hobs 使用第 10 项及原 heat.o=3，hleft 使用 heat.c₀=3；真实实幂与整数三次方通过 `Real.rpow_ofNat` 识别。最后对任意 z 调用同一 T167 定理 `.minus z`，改写两项右侧并传递 hleft，保留同一个 C。

因此该接口实际上等价于原物理载荷 F=X、Γ=id 的对应估计：给任意物理载荷 Fᵢ，取 fᵢ=E Fᵢ，原方程与新接口方程一致且权范数精确相同；反向由 E 满射覆盖全部计数载荷。没有缩小状态或载荷到光滑、谐波、截断、过滤或某个固定 PDE 解子空间。

## 前提清偿与统一量词

直接读取 T167 `box_cartesian_heat_estimate` 及其实际 `BoxHeatContinuous`、`CartesianHeatGeometry`，核对其内部调用。盒 Dirichlet H² 域界来自已证明的 `box_dirichlet_domain_le_h2`；允许权族来自 `box_analytic_data_uniform`；完整数值数据来自 `cartesian_numericalData_on`；真实连续 CE 来自 `box_heat_continuous_data`，其进一步调用 T165 全部原弱轨道、两时间符号的盒 C² 估计。没有把 CE、目标离散界、H² 正则或数值测试界新增为本批前提。

T167 实际以 κ=min(κ₀,ε)、0<h≤h₀≤1 和原尺度推出 h·w.max≤ε，再供应原数值小量。新第 13 项原样传递 h、h₀、dt、Δ₀ 和 `w.max≤κ min(h^(−4/5),dt^(−2/5))`，没有留下第二个额外阈值。实际连续/空间解析/数值统一常数都先于网格，不能从有限维性选择一个随 N 增长的隐藏 C。

最终量词次序明确为：固定维数、lo/hi、W、ω、ratio；选择 c、l、β、qc、κ、h₀、Δ₀、C 及全部正性/大小性质；然后才是 o、δ、hδ、N、域等式、h、g、w；最后在 `PhysicalLoadCarleman` 内量化全部 z、f。故 C、阈值和相位不依赖原点、节点数、网格步长、时间周期、qmax、状态或载荷。时间周期 T=g.period>0 任意；本批只使用负方向，底层 T167 的同一常数适用于两个方向。

最终输入确为 `PhysicalQClass w g.period β qc`，它要求全局光滑 q、全局 qc 下界和真实一二阶导数预算，以及 0/1/2 阶端点匹配。它是物理权的既有充分输入，并非本批宣称任意仅区间 C² 权都具有全局光滑表示。已直接读取 `PhysicalQClass`、`smooth_interval_derivatives` 和 `PhysicalQClass.toInterval`：通过 T>0 的 Icc UniqueDiffOn，将实际全局导数与一二阶 within 导数在包括端点的整个 Icc 精确识别，全部 β/qc/T 和端点条件保持，然后调用 T167 的完整 IntervalQClass 接口。原物理正则化正弦权由既有 physical_qclass_uniform 供应此输入；本批不完成其后势吸收、N+1 物理观测或 HUM 控制。

## 固定依赖、公理和本机证据

三个新模块的 Carleman 递归导入闭包共 **752** 文件；除三新模块外 **749** 个旧文件与 mathematical_base 逐字节相同。另独立比较关键已接受版本的完整相关闭包，均无变化；旧报告仅作为依赖验收凭证，实际对象与调用已如上重新读取。

| 依赖 | 接受版本 | 比较入口；完整闭包文件数 |
|---|---|---|
| C183 / [T167](T167-local-acceptance.md) | `d4b7f2d6d6894520fc5db06dc3a230be27518297` | `Transfer/BoxCartesianHeatEstimate`；746 |
| C184 / [T168](T168-local-acceptance.md) | `30a03e32af45ef82baacbbfe6917cd7ceff234f3` | `Spatial/PhysicalFiniteWeights`；44；`Control/PhysicalIntervalQClass`；33 |
| C122 / [T106](T106-local-acceptance.md) | `337d9c1b8c5fadce4e638a2c96311e230ee94bb1` | `Spatial/CartesianPhysicalSpaces`；310 |

三个新模块均由固定根目标实际导入，13 项均有 `#check @...` 和 `#print axioms`。新源码无 sorry、admit、新 axiom 或 native_decide。固定检查器遍历所有 `privateToUserName` 属于 Carleman 的常量，逐项递归 `collectAxioms`，仅准许 propext、Classical.choice、Quot.sound。

固定 raw 中 **3056** 条有公理打印记录和 **9** 条无公理记录均正常；13 项新声明各自仅使用三项标准基础公理。显式打印数不与递归总数混同：实际末行为 `Axiom audit passed for all 8093 Carleman declarations.`。完整类型未出现额外 CE、目标估计、频率滤波、状态正规性或不可实现的载荷前提。

实际读取定向日志 `/tmp/carleman-t169-control-isometry-target.log` 为 **3514 jobs** 成功，`/tmp/carleman-t169-box-load-target2.log` 为 **3982 jobs** 成功；固定 `-build.log` 为根目标 **4094 jobs** 成功。`-axioms.log` 是零字节 stderr，未以它单独作为审计成功证据。Lean pin 为 4.35.0，CI 编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib pin 及本机实际干净 checkout HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。工具链、manifest、两份 CI workflow 和 tools/lean_ci.sh 均与基线相同。

## 独立正式 CI 和原始工件

本 Agent 独立查询 [run 39259282628 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39259282628/attempts/1)，确认 main / push、精确 head SHA 与本报告相同。实际终态为 `completed / success`，updated_at=`2026-10-19T13:23:39Z`。第一次查询时 dashboard 尚在运行，已继续实际查询到最终成功后才签发。

| 正式 job | 实际 ID | 最终状态及 completed_at |
|---|---|---|
| state-check | `118082421451` | completed / success；`2026-10-19T13:20:27Z` |
| lean | `118082421944` | completed / success；`2026-10-19T13:23:26Z` |
| dashboard / snapshot | `118083948157` | completed / success；`2026-10-19T13:23:39Z` |

本 Agent 自行运行两次 `gh run download`，均退出 0，未使用主执行者的 root 副本替代独立下载。两份工件 API 元数据未过期，workflow_run.id、main 分支和 head_sha 均精确绑定本次证明版本。

| 工件 | artifact ID；归档字节数 | 独立下载路径 |
|---|---|---|
| lean-ci-result | `12189237824`；493 | `/tmp/carleman-t169-cartesian-physical-load-main-ci/result.json` |
| lean-declaration-evidence | `12188094956`；233488 | `/tmp/carleman-t169-cartesian-physical-load-main-axioms/axioms.txt` |

实际 result.json 为 **537 bytes**，SHA256 `428d1fbe0381e8405085a5c9fda69544b455e6e46aca0a3eef1e683b11d09ede`。内容为 status=PASS、checked_sha=source_head_sha=`7d1cc86d3c0a01b524f099ba90baaf59784f159d`、targets=[Carleman]、finished_at=`2026-10-19T13:22:23.384873+00:00`；ci_url 指向上述同一 run/attempt，实际 Lean/mathlib 与固定 pin 一致。

独立下载的 raw 与固定 `/tmp/carleman-t169-cartesian-physical-load-local-axioms.txt` 已实际 **逐字节比较完全相同**，各 **2510276 bytes**，SHA256 均为 **`2163ab6209f04e62d9563574a6ef1df423c1705878b0ffeb049544cbb7307eb4`**。原始实际类型、逐项公理和全部 8093 声明递归审计 PASS 相同；归档大小与解压后 raw 大小分别记录。

## 签发

**13/13 PASS；C185 可在 AUXILIARY 范围登记 REVIEWED。** 原控制空间/真实伴随、保范数与权交换、计数表示中的物理质量、逐点高斯相位、全部周期状态/载荷、负向差分符号、真实 CE 内部供应和统一量词均通过，未发现阻断数学或对象身份缺陷。仍不据此完成物理观测/控制或一般几何，覆盖保持 17/26。本报告单独提交，不 push；通知后正文和 reviewed_at 冻结。
