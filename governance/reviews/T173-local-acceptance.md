# T173 / C189 独立本机验收：完整一致质量 P1 盒物理载荷估计

- checked_sha / source_sha: `7c4ed351ef6097a8543e7e9da53aa1b8ca756b1d`
- mathematical_base: `113b2c6e318ce5cb48f1fda5696223646e0cd2b1`
- reviewed_at: `2026-10-19T13:57:43+00:00`
- reviewer: 独立本机数学验收 Agent `/root/accept_section3`
- result / axiom_check: **PASS / PASS**，1/1 显式声明通过。
- scope: **AUXILIARY**；C189 可在完整一致质量 P1 盒物理载荷估计范围登记 REVIEWED。原文覆盖保持 **17/26**，不据此提升一般凸多面体 P1、P011 或最终物理观测/控制结果。

## 审查版本和原文

从固定 Git 对象独立读取新模块的全部实现、raw 中完整展开类型，以及实际 P1、Galerkin、Dirichlet、权族、连续 CE 和热尺度依赖。固定治理协议 AGENTS、PROJECT_OPERATIONS、state/README、MILESTONES/PAPER_COVERAGE 与基线一致，沿用已读要求；读取本版本 `analysis/T173-box-p1-load.md` 和 MATH_SPEC 对应段。没有使用动态根导入、公理文件或未来 BoxP1PhysicalControl/BoxP1FilteredControl/PhysicalControlConclusion 等工作树增量。

对照 `paper/main.tex` 的 `eq:state-load-equation`/`eq:finalCE`（562 行起）、`eq:rawCE`、`cor:scales`/`eq:mainS`（617–625 行）、Section 6 一致质量 P1 定义及 `eq:grading`/`prop:p1`（1465–1503 行），并核查该命题的近似与指定测试证明。固定原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

本批是由原 P1 数值实现、实际盒解析数据和连续 CE 推出的完整周期物理载荷实例；输出只需原热能量中的 q³ 状态项。没有把这一接口声称为一般凸多面体上的全部 prop:p1，亦没有将周期载荷结论冒充非周期物理观测或 HUM 控制。

## 唯一声明及实际数学对象

| 完整声明 | 固定源码 / raw 类型行 | 判定 |
| --- | --- | --- |
| `Carleman.Physical.box_p1_physical_load_carleman` | `Carleman/Control/BoxP1LoadCarleman.lean:19` / 33516 | **PASS**：真实完整一致质量 P1 空间、原投影载荷和 ambient 观察在全部原网格条件及热尺度下满足 PhysicalLoadCarleman，所有解析和数值输入内部清偿。 |

空间维数为 n=d+1，且 n≤3，因而包括原文 n=2、3，也覆盖 n=1；没有遗漏原维数或收紧其范围。固定盒各边长严格正，ω 是盒内非空开集。网格是由真实非退化 n 单纯形组成的任意有限 SimplicialPartition；有限单元覆盖原闭域、内部不相交，FaceMatching 和 BoundaryFitted 表达实际共面匹配及边界由边界节点生成。它们是原 conforming、边界拟合网格条件，没有添加状态的光滑性或节点表示前提。

原 shape 条件以真实内球 `ball(centers_i,r_i) ⊆ K_i`、r_i>0 及 `diam(K_i)≤shape*r_i` 给出。真实 ℓ_i>0 满足 `cmesh*diam(K_i)≤ℓ_i≤Bmesh*diam(K_i)`，所有共享顶点的有序单元对满足 `ℓ_j≤γ*ℓ_i`；交换 i/j 给反向比值。实际 `p1GradingLimit n=(sqrt(n+2)+1)/(sqrt(n+2)-1)`，仍为原 `1≤γ<Γ_n`，没有替换为更窄范围或乘出 γ²。h 是真实 `M.maxDiameter`，从非空 ω⊆S、网格覆盖和正维单纯形内部证明 h>0；不额外要求准一致网格。导入 ConformingUniformInverse 在此使用的是 maxDiameter_pos，不把其中另一个定理的准一致前提带入本结论。

X 取 `M.conformingSpace (dirichletSubspace S)`。重新展开 SimplicialPartition 的成员等价：这正是原 H¹₀ 与每个真实单元上 a.e. 仿射 L² 类的交，包含所有原 conforming P1 状态，不是预选节点函数的更小像空间。有限维性及所需完备性内部供应。内积继承真实 L²(Ω)；Galerkin stiffness 由该 Hilbert 空间的 Riesz 表示构造，实际配对等于原完整弱梯度 Dirichlet 形式，故为一致质量刚度，ηA=0。没有改为集中质量或以任意有限维范数等价替代原范数。

R 是实际包含；J=Γ 是同一 X 的 L² 正交投影。独立读取 mass_adjoint、`conformingReconstruction_G` 和实际 load 定义：G=id、Q 是投影后包含、载荷 lift=id、ΓI=id。原全部 L² 载荷保留，不要求 f 属于 X，也不把 Γ 换成节点采样或某个可选右逆。

## 解析与数值输入的清偿

`a = boundedDirichletOriginalForm` 是原 H¹₀ 闭形式及其完整变分算子，而非把 D(A) 定义为某个 H² 子域。`box_dirichlet_domain_le_h2` 对该同一原域供给真实 H² 包含；`box_analytic_data_uniform` 给 canonical H² jet 的全图范数界 `‖jet(v)‖≤Creg‖Av‖`，以及所有 w/τStar 的原 AllowedFamily。重新核查其通过原图方程、实际盒正则性和弱 jet 值唯一性识别同一域元素，故未偷加光滑解、零延拓 H² 或调用者给定正则性前提。

实际 Gaussian 相位由 `box_heat_continuous_data` 在固定 ω 中选择中心 c，给 l≥1、β>0 且 β≤1、qc≥1 和原全弱轨道连续 CE。该 CE 对所有 Orientation、全部 `PeriodicWeakTrajectory` 成立，采用原 ε∂t−Δ 残差和真实梯度/观察积分；新模块只按同一包含、载荷和控制半范数实例化它，没有把连续 CE 重新作为参数保存。

`IntervalQClass w.q g.period β qc` 的实际字段是原闭区间 C²、0/1/2 阶端点匹配、q≥qc、|q′|≤βq²、|q″|≤β²q³；TimeWeight 仍是既有有界正权载体。本批没有把区间权改为全局 C∞ 权。通过 toRegularity 只取得转移所需较弱正则性，而完整 hq 同时提供连续 CE 的全部条件。

`full_p1_numericalData` 的前提在本实例全部满足：盒开、凸、闭包紧，真实相位 C²，原 shape/ℓ/grading，真实 hD，以及内部证明的 h*qmax≤ε。其 N3 由原全部弱 H²∩H¹₀ 的同一正交投影误差给出，N4 由真实 `Π_h(σ²z)` 和其时间导数给出。独立读取 FullP1ApproximationInterface、FullP1WeightedTest 和 GalerkinWeightedTest：实际弱 jet 身份、投影、σ² 乘法和导数保持，不是任意存在的测试算子。

误差精确为 `aE=Capp*h`、`a₀=Capp*h²`、`ηA=0`，Cap 先于网格、权和状态。新模块从完整 NumericalData 取得 approximation/test，GalerkinHeatData.toConforming 再通过真实 galerkinNumericalData 供给 stiffness、质量/载荷和观察恒等式，比较常数为 1。未由较小接口缺省地宣称 N1/N2/N5 成立。

数值调用取 ω₀=ω，观察包含使用 Subset.rfl 合法：原数值观察要求子集，不要求严格包含或紧包含。实际 ambient 控制为 `Π_X ∘ χ_ω`，其 Hilbert 伴随为 `χ_ω ∘ inclusion`。因此最终加权观察平方范数正是 `∫_ω |σz|²`，并与既有真实区域 L²(ω) 限制观察一致，没有扩大观察区域。这里输出 ambient 形式，未来物理控制的区域控制序列不在本声明中声称。

新模块使用 τStar=2；实际 heat exponents d*=1、b*=4 给 `max(d*/2,b*/2)=2`，故覆盖转移全部所需权幂。原上游 P1 接口依然量化任意 τStar，双空间符号仍通过 η=±1 内部提供；这不是将原权族或最终 q 取值范围缩小。AllowedFamily 和连续 CE 的两个方向保持，最终 PhysicalLoadCarleman 则按其原用途选负向差分。

## 统一尺度与最终结论展开

相位及全部 β、qc、κ、h0、Δ0、C 在任意索引类型 ι、网格 M、内球/ℓ 数据、时间网格 g 和权 w 之前选择；常数只依赖固定盒/维数、ω、shape/cmesh/Bmesh/γ 等固定数据。g.period 可任意为正，故没有 T 或网格基数进入这些常数。

先从原 conforming_heat_load_uniform 取得 κ0/h0/Δ0/C，再取统一 `κ=min(κ0,ε)>0`。由 0<h≤h0≤1 和 `qmax≤κ*h^(-4/5)`，实际 scale_monomial_le 给 `h*qmax≤κ≤ε`；同时 κ≤κ0 保留原转移范围。dt 的 `-2/5` 幂及空间 `-4/5` 幂完整保留。数值阈值已内部清偿，没有另加 h*qmax 条件；κ 在未来物理尺度选择之前就已确定，不会在给定物理尺度的两侧条件之后再修改它。

展开最终 PhysicalLoadCarleman：对每个周期序列 z_i∈X 和每个 f_i∈L²(Ω)，只要 `g.dMinus z_i + A_h z_i = Π_X f_i`，即有

`dt Σ_i q(t_i)³ ‖exp(q(t_i)ρ) z_i‖² ≤ C [dt Σ_i ‖exp(q(t_i)ρ) f_i‖² + dt Σ_i q(t_i)³ ‖exp(q(t_i)ρ) χ_ω z_i‖²]`。

检查 PhysicalTransferGeometry 的实际证明：用同一 z/f/Γ 的 minus 方向转移结论，载荷和观察是精确范数身份；左端由完整节点能量的非负梯度部分得到 q³ 项。没有遗漏 RHS 的幂次、把强载荷换成投影后载荷范数，或错误丢弃有符号项。声明对全部周期状态/载荷有效，没有低频、光滑代表、状态边界值之外的新限制或目标估计前提。

## 依赖版本、构建及公理

实际导入闭包为 689 个 Carleman 模块，除本次一个新增模块外，688 个旧模块与数学基线逐文件相同。又对关键接受版本的整个闭包逐文件比较，均未变化：

| 依赖入口 / 正式报告 | 已接受证明 SHA | 闭包模块数 |
| --- | --- | --- |
| FullP1NumericalData / [T126](T126-local-acceptance.md) | `8bfc0cb3d9a3d394805cfbb9720d903fc139bdfe` | 511 |
| BoxAnalyticData / [T143](T143-local-acceptance.md) | `90ca06c7cd42fae4b870fae9a67219fa729226f7` | 362 |
| BoxHeatContinuous / [T166](T166-local-acceptance.md) | `28789e8973368055acc0c17d5b395332e6ee7364` | 386 |
| ConformingHeatTransfer / [T031](T031-local-acceptance.md) | `4223cdff025d68431b81dc2f3fb620e8bdc9ec6b` | 283 |
| GalerkinHeatData / [T032](T032-local-acceptance.md) | `1cf3071913d460625411022e4ea16c8336399bf8` | 287 |

旧 T126 报告保留的 hD 和 T031/T032 条件性 analytic/numerical/continuous 输入，本次分别由上述实际盒数据和真实 P1 数据清偿；没有仅以旧报告为 PASS 就省略这些义务。T172 滤波控制不是本次证明的依据，未来 T174 模块完全排除。

新模块已固定根导入，唯一声明在固定 CheckAxioms 中打印完整类型和公理。实际递归审计遍历所有 Carleman 声明（含 privateToUserName 还原的私有声明），每项执行 collectAxioms。原始末行是 `Axiom audit passed for all 8138 Carleman declarations.`；独立解析 3083 项显式公理记录和 9 项无公理记录，白名单外依赖为零。唯一新定理仅依赖 `propext, Classical.choice, Quot.sound`；新增源码无 sorry/admit/axiom/native_decide。空的 axioms.log 只是 stderr，不作为 PASS 依据。

实际读取本机 target3.log：3919 jobs 成功；build.log：4106 jobs 成功。Lean pin 为 4.35.0，实际 CI compiler commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib pin 及本机干净依赖 HEAD 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。固定 workflow/lean_ci 脚本检出 github.sha、构建 Carleman 并运行全声明递归审计；未改变这些验证规则。

## 独立同 SHA 远端证据

本 Agent 自行查询 GitHub API 的真实 run/jobs/artifacts，并自行执行两次 `gh run download`，均 exit 0。没有使用主执行者下载目录替代本次独立下载。

- run: [39263701979 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39263701979/attempts/1)，event=push、branch=main、head_sha=`7c4ed351ef6097a8543e7e9da53aa1b8ca756b1d`，最终 completed/success，updated_at=`2026-10-19T13:56:37Z`。
- 三项实际 jobs：state-check **118097695489**、lean **118097696162**、dashboard / snapshot **118100313243**，全部 completed/success；proof build、结果记录、两次上传步骤均 success。
- `lean-ci-result` artifact **12192360837**，ZIP 492 bytes，API digest `sha256:b114939932230a5529d356b36ca26ebbee6647f8f90716e57f3016559e2b0088`。
- `lean-declaration-evidence` artifact **12192425941**，ZIP 237819 bytes，API digest `sha256:b87c2f1c29b2de744f3e059d1dd7f40b7173832db5592d3f3b235d4a5b27c62c`。

两工件 workflow_run 均绑定上述精确 SHA/main/run。独立解包目录为 `/tmp/carleman-t173-p1-load-main-ci` 和 `/tmp/carleman-t173-p1-load-main-axioms`。实际 result.json 为 537 bytes，SHA256 `644ad1842663e586d3a9ad7cc8bb2362b112239b18204d4c42cf5c46ada688d4`；status=PASS、checked_sha=source_head_sha 为本报告 SHA、targets=[Carleman]、finished_at=`2026-10-19T13:55:23.927193+00:00`，ci_url/Lean/mathlib 均与上述记录相同。

独立逐字节比较解包 axioms.txt 与固定 `/tmp/carleman-t173-p1-load-local-axioms.txt`，完全一致：**2567557 bytes**，SHA256 **`abdf47e14194df5f7b1f6a62ea0eec8aaa2beb2531f36792ebb3c668ba7606a3`**。完整类型及 8138 项审计均从该 raw 读取；ZIP digest 和 raw digest 分别记录。

## 最终结论

**1/1 PASS；C189 可登记 REVIEWED/AUXILIARY。** 未发现阻断性数学、对象身份、量词或额外前提缺陷。实际一致质量 P1 盒载荷估计已经内部完成原解析、数值、连续 CE 与统一热尺度的组合；仅此实例通过，不提升一般几何、原 P011 或后续物理控制，原文维持 **17/26**。本报告单文件提交，不 push、不改实现/原稿/台账；通知后正文与 reviewed_at 冻结。
