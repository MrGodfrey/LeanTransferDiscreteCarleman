# T126 / C142 独立本机验收

- `checked_sha`: `8bfc0cb3d9a3d394805cfbb9720d903fc139bdfe`
- `base_commit`: `ed02ecc45e5edf8cb96085c4aff7e5da38397bcf`
- `reviewed_at`: `2026-10-19T06:24:31+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：原完整 conforming P1 空间、原 L²(ω) 控制及真实限制伴随的一致质量 NumericalData；N3、N4 由既有证明内部供应，aE=Capp h、a₀=Capp h²、ηA=0。具体 Dirichlet 算子域的 H² 包含 hD 仍显式保留，P011 不提升，原文保持 **14/26**。

本 Agent 从固定 Git 对象读取两模块全部证明、5项完整展开类型、T126 分析、MATH_SPEC、C142/T126 条目和关键依赖，对照原 `paper/main.tex` A1（333–353）、N1–N5（422–468）、P1 空间及控制定义（1469–1500）和 Step 2/3。执行者说明与 CI 未代替语义核查。后续弱导数分析文件、变化中的工作树和 `.ci/axioms.txt` 均排除。

## 全部五项声明

名称省略公共前缀 `Carleman.`，位置以 `Carleman/Control/` 为根；顺序与固定交付 JSON、C142 和 T126 完全一致。三项 theorem、两项实际 def 均已核验。

| # | 声明 | 固定位置 | 独立结论 |
|---|---|---|---|
| 1 | `Physical.restrictRegion_weighted_sq` | `ConformingRegionWeightedData.lean:15` | PASS；真实受限权乘子作用于真实区域 L² 限制后的平方范数，精确等于原区域上的权密度积分。 |
| 2 | `Physical.conforming_region_weighted_observation` | `ConformingRegionWeightedData.lean:25` | PASS；实际 B 的 Hilbert 伴随是限制，ω₀⊆ω 和真实非负可积密度给观测平方界，常数1。 |
| 3 | `Physical.galerkinRegionNumericalData` | `ConformingRegionWeightedData.lean:44` | PASS；以实际 inclusion、正交投影载荷、Galerkin 刚度、零缺陷和原 L²(ω) 控制构造 NumericalData；通用层明确接受 N3/N4。 |
| 4 | `p1ErrorScales` | `FullP1NumericalData.lean:17` | PASS；实际 ErrorScales 字段为 Ch、Ch²、0，给出全部非负性，允许 h=0。 |
| 5 | `full_p1_numericalData` | `FullP1NumericalData.lean:25` | PASS；在全部网格和时间权前选正统一阈值/常数，内部证明通用层所需 N3/N4，输出同一实际全 P1 数值数据。 |

## 真正的区域控制、a.e. 类与权积分

已直接读取 `ObservedRegionLp`、`ConformingRegionControl`、`BoundedMultiplier.restrictMeasure`、`WeightedL2` 和 `Observation`。`restrictRegionLp ω u` 由同一原 L² 代表在 ν.restrict ω 下的 MemLp 构造；`restrictRegionCLM` 的连续性使用真实限制范数≤原范数。`restrictMeasure` 保留同一乘子函数和上界，通过 ν.restrict ω≤ν 转移可测性及 a.e. 有界性，没有定义一个与原 σ 不同的区域权。

第1项先用实际 L² 内积得到 `seminorm_sq_integral`，再利用 `restrictRegionLp_ae` 作积分 a.e. 同余，故严格得到

\[
\|\sigma|_\omega\,(u|_\omega)\|_{L^2(\nu|_\omega)}^2
=\int_\omega |\sigma(x)|^2\|u(x)\|^2\,d\nu.
\]

每个 L² 类只通过 a.e. 身份使用，没有读取任意等价类的指定点值。`integrable_density` 是由有界乘子保持真实 MemLp 和平方可积性证明；第2项的积分单调性因此作用于真正可积、非负的密度，并非利用不可积积分的默认值。

控制算子本身是 `X.orthogonalProjectionOnto ∘ (restrictRegionCLM ω).adjoint`，其源明确为 `Lp E 2 (ν.restrict ω)`。由真实 Hilbert 伴随复合、双伴随和正交投影伴随公式，`conformingRegionControl_adjoint_apply` 给 B* z=z|ω。对于原论文的可测（特别是开）ω，既有 `restrictRegion_adjoint` 进一步识别限制伴随为真实零延拓，且 `conformingRegionControl_pairing` 给

\[
(B_hu,z)_{X_h}=\int_\omega u z\,d\nu.
\]

这里 X 继承原 L² 内积，B_h 即原区域控制的 Riesz 实现。没有把控制空间替换为全域 L²、节点空间或任意有限维代理。控制函数的全部原 L²(ω) 类均覆盖。

第2项将两侧分别还原为 ω₀、ω 上同一密度的积分，用 `setIntegral_mono_set` 和 hinc 得平方界常数1。两侧本为非负 seminorm，故这也对应原未平方 N5 界常数1。原 R 是 inclusion，因此不需要 FD 型网格支撑阈值或缩小观测区域。一般引理甚至允许任意集合 ω；原可测 ω 情形的零延拓/配对身份另有明确可测性前提，未对非可测集合无条件宣称该身份。最终只要求 ω₀ 可测及 ω₀⊆ω，覆盖原合法控制域。

ω=∅ 或 ν(ω)=0 时真实区域 L² 是零类空间，ω₀ 的观测也为零；证明未除以区域体积，未假设 ω、ω₀ 正测度或非空。对一般 Hilbert 值 E 的前两项，完备性只在使用 Hilbert 伴随的第2项出现；最终 E=ℝ，X 的完备性由真实有限维性内部供应。

## 同一完整 P1 空间、一致质量、刚度和载荷

最终 X 是 `M.conformingSpace (dirichletSubspace S)`。已核对其实际成员刻画：原 H¹₀ 值类且每个真实单元上 a.e. 为仿射多项式；它不是预选节点插值像或较小子空间。真实有限单元分割给有限维性，继而给 L² 完备性和正交投影。这里没有把无限维 H¹₀ 误当作 L² 闭子空间。

实际 `conformingReconstruction` 使用 R:X→V 的包含、J=Π_X 的 L² 正交投影，mass_adjoint 由投影的真实内积恒等式证明。RH 是原 L² 包含，G=JR=Id，Q=RJ 对应原 Π_h；R 单射，无权质量范数相等。`conformingWeightedState` 就是原 σ seminorm 与 inclusion 的复合，故加权重构上下界同样恰为等式。没有采用质量集中、节点 Euclidean 内积或依赖网格的范数等价常数。

`boundedDirichletOriginalForm` 的 V 是原 H¹₀，form 是真实全部弱梯度的 L² 内积；有界性、对称性、密度、图闭性和由 Poincare 得到的强制性均已有证明。模型使用完整变分算子域，`domain_le` 内部证明 D(A)⊆V。该构造并未把 D(A) 定义为事先给定的 H² 子空间。

`galerkinStiffness` 通过 X 的真实 Hilbert Riesz 映射表示同一梯度形式；`galerkinStiffness_form` 给 `(A_hz,v)=a(Rz,Rv)`，已有实际 symmetric/nonneg 定理。因此新 NumericalData 的 stiffness 字段采用真正的零缺陷 b=0，其 defect 对任意允许符号/幂和全部状态都为0；ηA=0 时原逆权双因子界严格成立，未假定一个待证刚度误差。

载荷空间为完整原 H=L²(S)，Γ=Π_X、lift=Id，兼容式 J·lift=Γ 是实际等式。原右逆 I_h 取 X 的 L² inclusion，`conforming_load_right_inverse` 给 ΓI_h=Id；真实载荷/状态加权范数下，lift 和 I_h 的稳定常数均为1。通用层的 reconstruction_upper/lower、lift_bound 和 observation_bound 统一使用 Cnum=1。

已展开 `Section5.NumericalData`：它保存传递证明所需的原数值字段，未重复保存 injectivity、刚度对称非负、载荷右逆或测试严格正定等已由具体构造证明的性质。验收没有只凭结构名称把这些视为已证，而是另行读取上述真实数据和定理。该存储范围不改变本次具体数据的原数学性质。

## N3 由原全部弱 H² 状态内部供应

通用 `galerkinRegionNumericalData` 的 approximation/test 是明确输入；第5项不把它们留给调用者，而分别调用 C141 `full_p1_weightedApproximation_interface` 和 C127 `full_p1_weightedTest_interface`。已直接读取两条接口及其本次使用的关键证明，并核对固定依赖版本。

N3 中 D 取真实 a.model.domain，hDV 使用 a.domain_le，hD 仍是显式原 H² 包含。C141 对该域中每个 v 使用实际 canonical `domainSobolevJet`，由已经证明的原全部弱 H²∩H¹₀ 节点/投影误差给真实完整 P1 正交投影的同一误差 E。经开域上的完整弱 jet 值注入性，−E 正好是原 v−Qv 的 canonical H¹ jet；没有仅对齐标量值后假定梯度相同。

原误差方向、真实 R/J 和 L² 投影均一致。N3 能量字段是包含 q 加权值与全部弱梯度的原 N 范数，L² 字段是同一 v−RH(Jv)；不是仅梯度半范数，也没有限制为节点数据或光滑状态。原 parameterNorm 的二阶项系数为 q⁰=1，给 `‖σ field₂u‖≤Rσ(u)`，从而输出 aE=Capp h、a₀=Capp h²。

N3 的固定 C 与阈值在固定空间域 S 后，先于全部网格、所选域子空间 D 和状态选取；它适用于任意 τ 和两个 η 符号。新证明在该分支不使用 |τ|≤τStar，是因为已有空间界更强，而非漏掉必要幂条件。`WeightedApproximation` 两字段量化原整个闭周期 [0,T] 的所有 t 和全部 v:D；继承证明实际上先得到任意实 t 的界。

## N4 的实际投影测试、真实时间字段及逆权

C127 的输出明确带同一个测试及导数的身份。新证明用 `Classical.choose` 选择此已证明存在的对象；它没有重新选一个仅满足名字或估计的任意算子。令 F 是 σ 乘法复合 inclusion，实际测试为 F*F，严格等于 Π_X(σ²z)。真实配对恒等式为 `(z,Tz)=‖σz‖²`，原允许权严格正且其 seminorm definite，因而测试严格正定；对称性和非负性也由同一实际构造证明。

实际导数表达式为 F′*F+F*F′，F′ 来自已证权乘法在 L² 连续算子空间中的真实导数。它产生原闭区间上的二次配对 `HasDerivWithinAt`，保留平方权的因子2。正式 WeightedTest 微分字段是该二次配对导数；本批没有新增整个 Galerkin 路径的算子范数导数声明。端点匹配来自 `TimeWeightRegularity.endpoint` 的 q(0)=q(T)，没有从一般上下界推断周期性。

时间常数可取 `2*β*(τStar+ρ.bound)+1>0`，与网格、T、qmax、状态无关；|η|=1 保留同一 profile 上界。空间超逼近由真实完整 Vh 的 C127/C082 依赖内部供应，误差是 `R(Tz)−σ²Rz`，在真正逆权 `(−η,−τ)` 下估计，尺度为 Csuper h qmax。已读取其弱 jet 值唯一性识别，确保原差的方向和全部弱梯度一致，没有把节点函数候选残差替代全空间状态。

`WeightedTest.superapprox` 对权保持 V 的证明参数 hw 作全称量化；它不是要求调用者再假定目标超逼近估计。原允许权的 H¹₀ 保持已有真实乘法/闭包证明，此处测试构造本身是全 L² 上的有界乘法和正交投影。最终 N3、N4 共享同一实际 X、R、J 和 q/σ 族。

## 统一量词、实际网格条件与保留义务

固定 d、S、profile、κ、c、B、γ、β、τStar 及观测集合后，定理先选 δ>0、δ≤1、Ctime>0、Csuper>0、Capp>0，再量化全部有限索引、网格、内球/局部尺度、hD、TimeWeight、TimeGrid 和时间权正规性。所有状态、时刻、|τ|≤τStar 和两符号随后位于 NumericalData 的字段中。证明取 δ=min(δtest,δapprox)，真实小尺度条件同时供给两个已证接口，不另引入时间步或状态限制。

M 的原 FaceMatching/BoundaryFitted、真实内球和 diam(K)≤κr、c·diam(K)≤ℓ_K≤B·diam(K)、ℓ_K>0 以及所有共享顶点有序对的 ℓ_j≤γℓ_i 均显式保留。邻接对称性给原双侧 grading；Γ_d 是实际 `(sqrt(d+2)+1)/(sqrt(d+2)-1)`，没有放宽原 γ<Γ_d。h 是 `M.maxDiameter`，即真实有限单元 Metric.diam 的最大值；空索引取0，非负性供给 p1ErrorScales，未除以 h。

维数条件 0<d≤3 包含原 d=2、3；开凸紧闭包域包含原有界凸多面体。profile 的域内 C² 条件包含原光滑闭包轮廓，空间证明不要求域外延拓。有限测度实例在第5项内部由紧闭包/有界域推出，调用者不另给体积、完整性、连续代表、节点表示或误差估计。原 q 的 C² 和端点条件供应 TimeWeightRegularity 所需的一阶字段；没有增加原状态轨迹的时间正则性。

实际 NumericalData 的状态/载荷/控制 seminorm 按既有 schema 采用基权 τ=0、ρ；N3/N4 字段另外覆盖全部 |τ|≤τStar 和 signed ρ。前两项区域结论本身对任意 BoundedMultiplier 成立，重构与载荷的等式也对任意真实权成立。因此没有把原加权控制关系仅靠命名推定，也没有用基权范数替换 N3/N4 的允许权。

剩余 `hD : a.model.domain ≤ sobolevSubspace d 2 …` 是实际完整 Dirichlet 变分算子域进入原弱 H² 的包含，属于原 A1。该批不证明凸多面体上的这一正则性，也不证明原定量椭圆正则界或连续 Carleman 估计。`Nonempty NumericalData` 是实际构造见证的存在，不是包含最终离散 CE、观测或控制结论的新假设。故本阶段仍为 AUXILIARY，不能升 P011 或改变14/26计数。

## 依赖版本、构建和公理

依赖验收门槛已通过：[C141 / T125](T125-local-acceptance.md) 供应原 N3；[C127 / T111](T111-local-acceptance.md) 供应实际完整 P1 WeightedTest；区域 Hilbert 控制依赖 [C046 / T030](T030-local-acceptance.md)。本次另直接检查真实限制/零延拓/伴随、完整 NumericalData/WeightedApproximation/WeightedTest 类型、OriginalForm/DirichletForm、质量/载荷/刚度、N3 误差符号和 N4 测试身份，未只接受既有 PASS 标签。

两新模块 Carleman 导入闭包共 **511** 模块，其中 **509** 个旧模块与 base 逐字节不变。C141 `FullP1ApproximationInterface` 的498模块闭包相对 base 不变；C127 `FullP1WeightedTest` 的402模块闭包相对 `0d91a94335bd491366597b81f45de26b4559b7ad` 不变；C046 `ConformingRegionControl` 的54模块闭包相对 `31d5e165a595849bc1c882523838aad69576b594` 不变。没有混入后续工作树或改变后的依赖。

已读治理协议、原稿和工具链 pin 自 T123 不变。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean固定4.35.0，mathlib pin及本机实际干净HEAD为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。固定 root 显式导入两模块，CheckAxioms 对5项输出完整类型及公理，另递归审计全部 Carleman 公开/私有声明，仅允许三项正常基础公理。

实际读取 `/tmp/carleman-p1-numerical-target.log` 的 **3724 jobs** 成功记录和 `-full.log` 的 **3889 jobs** 成功记录，末行为 **6782声明递归审计PASS**。这是核对已有固定日志，没有声称验收时重新运行全库。固定 `-local-axioms.txt` 为 **2,081,313 bytes**，SHA256 **`58f0f1235c93292ca05aa2a345b4fa18aaf03178401c7a6428dc5902431d7e12`**。

5/5项实际展开类型已核验，均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。原始文件全部2357条非空公理记录及8条无公理记录均无异常集合；显式打印统计与6782项递归审计是不同计数。新增两模块无 sorry/admit/新增 axiom，没有未证明的数学公理。

## 同 SHA 正式 CI 和独立下载的原始产物

本 Agent 自行经 GitHub connector 查询 [main CI 39209309105 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39209309105/attempts/1)。实际run为main/push，head SHA精确匹配本报告，最终completed/success，updated_at为 `2026-10-19T06:23:27Z`。三项job均completed/success：state-check **117918922195**、lean **117918922535**、dashboard / snapshot **117919862472**。Lean的pin、证明构建、结果记录和原始证据保存步骤全部成功；没有因产物先可下载便提前认定全部job成功。

同run原始artifact为 `lean-ci-result` **12166488471**，压缩产物492 bytes，digest `sha256:8063d03a68f2a93bd533c35683e661ba31593b4e18bee8ac1925fc4b7a6d9f72`；`lean-declaration-evidence` **12166064627**，压缩产物191124 bytes，digest `sha256:564da0645cbf21ddbd9ada91915035f2b75a406bced5e6534263f93c231035e8`。两份workflow_run元数据均绑定上述run、main和精确SHA。本 Agent 自行用 `gh run download 39209309105` 下载至 `/tmp/carleman-p1-numerical-main-ci` 与 `-main-axioms`。

实际 `-main-ci/result.json` 为 **PASS**，`checked_sha=source_head_sha=8bfc0cb3d9a3d394805cfbb9720d903fc139bdfe`，targets为Carleman，`finished_at=2026-10-19T06:22:18.635671+00:00`，ci_url为上述run/attempt。Lean提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib为上述pin。解压result为537 bytes，SHA256 `f6858e44ccb7914c6843aaf83b1d8738d230a61028ed04c5a38008fd77f8188e`。

独立逐字节比较实际远端 `-main-axioms/axioms.txt` 与固定本机副本，完全一致：**2,081,313 bytes**，SHA256 **`58f0f1235c93292ca05aa2a345b4fa18aaf03178401c7a6428dc5902431d7e12`**；末行实际为 **6782项全声明递归审计PASS**，包含本批5项完整类型和标准基础公理。原始文件摘要与artifact ZIP摘要分别记录，未混同。

## 验收决定

**C142：PASS，可升级为REVIEWED，scope保持AUXILIARY。** 5项声明未发现需修复的语义、量词、真实控制空间、a.e. 代表、权积分或依赖缺陷。原全 P1 一致质量数据、真实区域伴随、内部供应的 N3/N4、统一正常数和 Ch/Ch²/0 误差尺度均成立；同SHA三项正式CI与独立下载的原始公理产物一致。

具体 Dirichlet H² 域包含及定量连续正则性仍待清偿，P011不提升，原文保持 **14/26**。本次仅新增本报告，未修改实现、台账、原稿或root导入，未commit/push。签发UTC如上固定；最终核对并通知主Agent后冻结本报告内容和时间戳。
