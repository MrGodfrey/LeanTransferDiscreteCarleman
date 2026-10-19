# T174 / C190 独立本机验收：完整 P1 盒物理及滤波观测、区域控制

- checked_sha / source_sha: `d93e52fc433c99d25a188effa0c451488098a451`
- mathematical_base: `7c4ed351ef6097a8543e7e9da53aa1b8ca756b1d`
- reviewed_at: `2026-10-19T14:03:55+00:00`
- reviewer: 独立本机数学验收 Agent `/root/accept_spatial_foundations`
- result / axiom_check: **PASS / PASS**；全部 **4/4** 显式声明通过，其中两个是完整结论定义，两个是实际证明该结论的定理。
- scope: **AUXILIARY**；C190 可登记 REVIEWED。原文覆盖保持 **17/26**，不据盒实例提升一般凸多面体、一般算子或整条 PAPER 覆盖。

## 固定版本和原文范围

直接读取固定 Git 对象中的三个模块、四项完整类型、两个结论定义的全部正文、实际证明和关键依赖；同时读取 T174 分析、MATH_SPEC 和固定 C188–C190 台账。AGENTS、PROJECT_OPERATIONS、state/README、MILESTONES、PAPER_COVERAGE 与本 Agent 已读 T171 版本逐字节相同，继续适用。未来 T175 等工作树增量、动态根导入和动态 `.ci/axioms.txt` 均排除。

原文对照 `paper/main.tex` Section 6 一致质量 P1 空间、刚度、载荷与控制（1460–1507 行），Section 7 原势形式、完整正向/伴随方程和时间控制范数（1715–1817 行），physicalO/physicalC（1825、2028 行起），filtered-observability/filtered-control（2135–2215 行）及 Appendix C 互补 HUM 证明（3089 行起）。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

签发前已完整读取独立 [T173 正式报告](T173-local-acceptance.md)，报告提交 `59e16ce40ad11d2c62abb0b0776a2055efa458fb`，checked SHA 正是本批 mathematical_base，reviewed_at=`2026-10-19T13:57:43+00:00`，1/1 PASS。固定 T174 台账中的 C189 仍为 BUILT/PENDING；该明确版本的冻结报告补齐验收门槛，没有把旧状态误读为已审查。T172 的正式 PASS 证据为报告提交 `519939f511ea5c60d68d766d127a9914e38d7ef5`、checked=`113b2c6e318ce5cb48f1fda5696223646e0cd2b1`；本次另行读取实际互补 HUM、滤波控制和常数证明，并比较完整相关依赖闭包。

## 四项声明逐项核对

顺序与固定 manifest、C190/T174 一致。源码位置相对于 `Carleman/Control/`；raw 行指固定完整声明类型的起始行。

| 序号 | 完整声明 | 固定源码 | raw 行 | 判定 |
| --- | --- | --- | --- | --- |
| 1 | `Carleman.Physical.PhysicalObservationControl` | `PhysicalControlConclusion.lean:12` | 33583 | 完整松弛观测与每个初态的真实控制、全轨道结论的透明定义；定义忠实性 PASS。 |
| 2 | `Carleman.Physical.PhysicalFilteredObservationControl` | `PhysicalControlConclusion.lean:21` | 33592 | 完整终态滤波观测与真实区域控制、精确投影零值及全终态指数界的透明定义；定义忠实性 PASS。 |
| 3 | `Carleman.Physical.box_p1_physical_observation_control` | `BoxP1PhysicalControl.lean:17` | 33604 | 内部供应实际 P1 载荷 CE、算子和区域观察，证明第 1 项的全部结论；PASS。 |
| 4 | `Carleman.Physical.box_p1_filtered_observation_control` | `BoxP1FilteredControl.lean:16` | 33689 | 原两滤波条件配同一统一 C0，证明第 2 项的全部结论；PASS。 |

### 完整结论定义已实际展开

`PhysicalObservationControl g L B C d S` 是以下两个命题的合取：对每个完整 `p : Fin(steps+1) → X`，由原 AdjointEquation 推出

`‖p0‖² ≤ C [dt Σ ‖B* p_i‖² + exp(-2dS) ‖pN‖²]`；

并且对每个原初态 y0∈X，存在 `u : Fin steps → U` 和完整 `y : Fin(steps+1) → X`，同时满足 y0 初值、原 ForwardEquation、`controlNorm dt u ≤ sqrt(C)‖y0‖` 和 `‖yN‖≤sqrt(C)exp(-dS)‖y0‖`。这不是仅给出一个抽象终端向量。sqrt(Cphys) 是原 physicalC 中可取的网格统一成本常数，允许与 physicalO 常数的命名不同。

`PhysicalFilteredObservationControl g L B C0 θ d S F` 第一项只限制伴随终态 pN∈F，结论为原 `2C0 dt Σ‖B* p_i‖²`。第二项对任意初态存在同一实际控制和完整正向解，成本≤sqrt(2C0)‖y0‖，且同时满足 **F.starProjection(yN)=0** 和 **‖yN‖≤C0 exp(-(1−θ)dS)‖y0‖**。

两个定义没有把上述命题作为额外输入，也没有用命名 Prop 隐藏较弱结论。它们仅定义目标；第 3 项的 `exact hdata ...` 实际提供两个分量，第 4 项用 `refine ⟨?_,?_⟩` 分别证明观察与控制。本次不把两个定义本身计作两份观测/控制证明。

## 原完整 P1 空间和真实物理对象

维数为 n=d+1≤3，包含原 n=2、3，同时允许 n=1。固定盒每边正长；ω 是盒内非空开集。它完整包含原紧包含控制区域的适用情形，并未缩小原观察区域。网格是任意真实有限 SimplicialPartition，保留 FaceMatching、BoundaryFitted、真实正半径内球与 diam(K)≤shape*r_K。局部 ℓ_K 正且与 diam(K) 双侧可比；有序共享顶点邻接条件给双向比值，仍为原 1≤γ<Γ_n，没有增加准一致网格要求。

重新展开 `M.conformingSpace (dirichletSubspace S)` 的成员等价：它是原 H¹₀ 与每个真实单元上 a.e. 仿射 L² 类的交，包含全部原 V_h 状态。有限维性在内部证明，范数和内积继承真实 L²(Ω)；不是预先选取的节点像空间或集中质量空间。h 是真实 maxDiameter，正性由非空盒和实际分割供给。

`a` 是 `boundedDirichletOriginalForm` 的原 H¹₀ 形式。`galerkinStiffness a X hX` 经 X 的 L² Riesz 表示构造，实际满足 `⟨A_h x,y⟩=a(x,y)`；对称、非负和零刚度缺陷均由该身份内部推出。构造 energy lift 时虽使用有限维连续性，其范数没有进入统一常数；最终使用的是原配对身份和非负性。

势为任意实 BoundedMultiplier b_i，只要求 a.e. 可测有界且 bound≤Mbound；没有节点取值、连续性或有限维势族限制。真实算子为 **Π_X(b_i x)**。实际证明给配对 `∫Ω b_i x y`、自伴性及 ‖V_i‖≤bound≤Mbound，完全对应原有限元势形式。Mbound=0 被保留。

控制空间实际为 **Lp ℝ 2 ((volume.restrict S).restrict ω)**，即原 L²(ω)，没有 FiniteDimensional U 前提。`conformingRegionControl` 等于 Π_X 复合区域零延拓，其真实 Hilbert 伴随是原状态限制到 ω；配对正是 `∫ω u x`，算子范数≤1。ambient cutoff 观察与区域限制的范数相等由真实 Lp 身份证明，故没有用任意观察或环境空间控制代替区域控制。

原物理方程展开后，正向为 `dt⁻¹(y_(i+1)−y_i)+(A+V_i)y_(i+1)=B u_i`；伴随为 `dt⁻¹(p_i−p_(i+1))+(A+V_i).adjoint p_i=0`。i.castSucc 对应论文 p^(n−1)，求和覆盖全部时间步，终值为 Fin.last。最终轨道不要求周期性、低频或额外光滑性。

## T173 载荷输入在本批内部清偿

重新读取固定 `BoxP1LoadCarleman` 及它对 FullP1NumericalData、盒解析数据和 BoxHeatContinuous 的实际调用。T173 对同一原 X、同一 Galerkin A、包含 R 和 L² 正交投影载荷 Γ 供应 PhysicalLoadCarleman，量化全部真实周期状态和完整 L² 载荷。实际原域 H² 正则、全弱轨道 CE、N1–N5 和 h/h² 误差均已在该入口内部供应。

第 3 项先从 T173 得相位及 β、qc、κ、h0、Δ0、CCE。ρ 是相同的真实 Gaussian 相位，l≥1 给 ρ≤−1；这一步不假定任意相位恰好满足负性。然后调用已证 `conforming_observation_control_uniform`；该旧接口确实保留载荷 CE 输入，本批以 `hload ... w hw.toInterval ...` 逐个清偿所有 PhysicalQClass 权。PhysicalQClass 到 IntervalQClass 保留原 β、qc、T 和端点/一二阶预算，不把较弱一阶正则性充当完整权类。

旧观察桥中 R=I=实际包含、Γ=同一正交投影，真实势兼容、右逆和质量比较均精确成立；区域观察通过真实 B* 范数身份转换。新定理的完整类型已经没有调用者提供的 CE、H² 域嵌入、解析常数、数值近似/测试、额外观察界或任意自伴刚度前提。旧接口曾是 CONDITIONAL，不表示组合后的盒实例仍遗留这些义务。

## 常数顺序、原尺度和滤波预算

固定盒、ω 和 shape/cmesh/Bmesh/γ 后，先选择 qc、κ、h0、Δ0、Cb、d0，再量化任意 T>0、Mbound≥0，选择 Cphys(T,Mbound)。随后才量化单元索引类型、全部网格、内球/ℓ 数据、时间网格、势及状态。基础阈值先于 T/M，Cphys 可以依赖 T/M，却不依赖网格、具体势或状态。

两个定理保留 `Smax=κ min(h^(-4/5),dt^(-2/5))`、h=maxDiameter、`qb=Cb(qc+T⁻¹+Mbound^(2/3))`，以及 h≤h0、dt≤Δ0、dt≤T/12、dt Mbound≤1/2 和 **16qb≤Smax≤qbT/(4dt)**。没有附加 h–dt 比例条件，亦未在给定尺度后重新选择 κ。T173 内部由该尺度证明 h*qmax≤数值阈值，不把它另作为本批条件。

滤波定理先在 T、Mbound 之后定义

`factor(T,M)=sqrt(1+2 exp(2MT)²) exp(MT+M²T²/2)`，

`C0=max(1,max(Cphys,2 factor(T,M)²))`。

这个同一 C0 在所有网格、势、θ、F 之前固定。观察右侧非负，故 Cphys→C0 的放大合法；两个滤波条件中的 log(4C0)、观察常数 2C0、成本 sqrt(2C0) 和最终前因子 C0 全部用同一个值。原 C(T,M) 是可一次放大的存在常数，这与原 C0=max(1,C(T,M)) 的组织方式兼容；结论不声称对预先给定的任意更小 C0 仍有效。

原条件 `TΛ_F≤θd0Smax` 和 `MT+M²T²/2+log(4C0)/2≤(1−θ)d0Smax` 给精确预算 **4C0 exp(-2d0Smax)K_F²≤1**。Λ_F 是同一 Galerkin 刚度和原一致质量内积的真实 Rayleigh 商上确界。观察用已核验 T171 反向界吸收终态余项；仅终态属于 F，不要求 A、V_i、轨道或任何步算子保持 F。θ 的 Lean 范围更宽，但完整包含原 0<θ<1；F=⊥、y0=0 均允许。

## 真实 HUM 与完整终态

读取 RelaxedControl、PhysicalHUM、FilteredControl、ComplementaryHUM、ComplementaryObservation、FilterPenaltyBound 和实际 PhysicalFlow。dt M≤1/2 给每步真实 resolvent 可逆，故任意初态与真实控制产生完整正向解。HUM 中 O 的目标是 PiLp 2 的完整控制时间序列，带 sqrt(dt) 缩放；反缩放后 `‖controlVector(dt,u)‖=sqrt(dt Σ‖u_i‖²)`，没有遗漏 dt 或误用有限维 U。

实际互补算子为 `O*O+η² P_(F⊥)`。其零核由真实互补观察和 initialMap 单射推出；有限维用在状态 X 上，给唯一最优性解。取 u=−O z 后实际终态表示 `yN=R* y0+O* v=η² P_(F⊥)z`，因此 **P_F yN=0**。正向解由 `existsUnique_forward` 构造，再以真实对偶恒等式识别终态；没有只产生一个抽象最优向量或事后替换轨道。

η 的真实值为 `exp(-d0S) sqrt(1+2 exp(2MT)² K_F²)`。从 A≥0 得 Λ_F≥0、K_F≥1，包括 F=⊥；原第一个滤波条件给 `η≤factor(T,M) exp(-(1−θ)d0S)`。C0 的预先预算再给 `sqrt(2C0)*factor(T,M)≤C0`，故原完整终态指数率与前因子成立，所有 F 依赖均已消去。过程中没有节点数、‖A_h‖ 或 mesh 相关常数进入统一估计。

## 固定闭包、公理和构建

递归解析三模块实际 Carleman 导入共 **703** 个模块，其中 **700** 个旧模块与 mathematical_base 逐字节相同。关键已验收入口的完整闭包另行比较，均无变化：

| 依赖入口 / 既有验收 | 固定接受版本 | 闭包模块数 |
| --- | --- | --- |
| BoxP1LoadCarleman / T173 | `7c4ed351ef6097a8543e7e9da53aa1b8ca756b1d` | 689 |
| FilterPenaltyBound / T172 | `113b2c6e318ce5cb48f1fda5696223646e0cd2b1` | 20 |
| FilteredObservation / T171 | `f6e35f26cc23e5ca84eb8e869a12864be70e7b27` | 12 |
| ConformingPhysicalControl / T030 | `31d5e165a595849bc1c882523838aad69576b594` | 61 |
| GalerkinStiffness / T032 | `1cf3071913d460625411022e4ea16c8336399bf8` | 283 |

固定根目标导入三个新模块，四个名字都实际执行 `#check @...` 与 `#print axioms ...`。新源码无 sorry/admit/axiom/native_decide，四项均仅依赖 `propext, Classical.choice, Quot.sound`。独立解析 raw 中 **3096** 条显式记录（3092 个不同名字、9 条无公理记录），白名单外依赖为零；真实末尾审计对全部 Carleman 常量（含还原私有名字）逐项 collectAxioms，给 **8151 项递归审计 PASS**。

实际读取定向 `/tmp/carleman-t174-p1-control-conclusion-target4.log` 的 **3922 jobs**、`/tmp/carleman-t174-p1-filter-target3.log` 的 **3933 jobs**，以及固定 `-build.log` 的根目标 **4109 jobs** 全部成功。`-axioms.log` 为零字节 stderr，未拿它代替实际公理结论。

Lean pin 为 v4.35.0、实际 CI compiler commit=`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib pin 和本机干净 HEAD 都是 `56a005855ea17e0b0958f73ec801ae140b0a1679`。工具链、manifest、正式 CI workflow 与 lean_ci.sh 和已审 T171 相同；实际脚本检查 resolved mathlib，构建 Carleman 并运行整个递归审计。

## 独立同 SHA CI 与工件

本 Agent 自行查询 GitHub API，并分别执行两次 `gh run download` 取得同次原始 result/raw，两个命令均 exit 0；没有使用 root 下载副本代替独立取证。

- run: [39264879548 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39264879548/attempts/1)，event=push、branch=main、head_sha 精确等于本报告 SHA；最终 completed/success，updated_at=`2026-10-19T14:03:31Z`。
- 三项 jobs：lean **118101748107**、state-check **118101784627**、dashboard / snapshot **118103880478**，均 completed/success。曾观察到 lean 仍运行，后实际查询最终三项成功才签发。
- `lean-ci-result` artifact **12192772371**，ZIP 492 bytes；API digest `sha256:bcd798bc540d84784150a5c2956458aa5d9b5e7f71312d77ca59ac52678c8bf2`。
- `lean-declaration-evidence` artifact **12193855254**，ZIP 238622 bytes；API digest `sha256:452f6f5202728fdb142dc74e9e4ea5fc6e793cd692ba795d0b6631c60eef8284`。
- 两工件 workflow_run 均绑定精确 SHA、main 和同一 run；ZIP digest 与解包 raw digest 分开记录。

独立 result 路径 `/tmp/carleman-t174-p1-physical-control-main-ci/result.json`，537 bytes，SHA256 `a2072b947c2d4c061be95fb05ff95011dfecda2c1cda50d5bfefd86b94753b33`；实际 status=PASS、checked_sha=source_head_sha=`d93e52fc433c99d25a188effa0c451488098a451`、targets=[Carleman]、finished_at=`2026-10-19T14:02:16.398808+00:00`，ci_url/Lean/mathlib 与上述证据一致。

独立 raw `/tmp/carleman-t174-p1-physical-control-main-axioms/axioms.txt` 与固定 `/tmp/carleman-t174-p1-physical-control-local-axioms.txt` **逐字节完全一致**，均为 **2586965 bytes**，SHA256 **`6595415ee4e2cd6bca0812c4c3e78d2a7f4665845b64d980f26f4a96d6920c79`**。完整类型、公理及最终 8151 项成功记录均实际读取。

## 最终结论

**4/4 PASS，未发现阻断缺陷。** 两个定义忠实展开全部原结论，两个定理以实际完整 P1 空间、一致质量刚度、投影势和无限维 L²(ω) 控制证明原物理及滤波观测/控制的盒实例；所有载荷 CE、数值和正则输入内部清偿，统一常数、原热尺度、两滤波条件、完整轨道及精确投影终态均保留。C190 可登记 AUXILIARY/REVIEWED，覆盖维持 **17/26**。一般凸多面体、一般算子和控制收敛不由本批完成。本报告仅单文件提交，不 push、不改数学/原稿/台账；通知后正文及 reviewed_at 冻结。
