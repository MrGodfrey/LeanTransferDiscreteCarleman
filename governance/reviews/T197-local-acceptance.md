# T197 / C213 — 独立细化下原差分控制序列验收

- checked_sha: `3998fb3b4353576457a0773e69d587e5cf92e7e8`
- mathematical_base: `9c62b704e83c3e25302aa14d665337a646beb8ee`
- reviewed_at: `2026-10-20T02:45:42+00:00`
- reviewer: `/root/accept_spatial_lemma`
- result: **PASS，9/9 声明；未发现阻断缺陷**
- scope: **AUXILIARY；17/26，P021 不提升**
- evidence_source: **local**。遵循已简化的规则，未查询或等待远端 CI。

独立读取固定提交三模块全部证明、全部展开类型与公理记录、T197 分析/MATH_SPEC、原稿及关键依赖。对应原稿 `2124–2133` 的独立细化尺度极限、`2363–2392` 的控制选择和终端消失步骤。原稿 SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef` 未变。

## 声明与结论

名称均以 `Carleman.` 为前缀；源码位于 `Carleman/Control/`，行号属于 checked_sha。9 项均为 theorem，与 manifest 精确一致。

| 模块:行 | 声明 | 核查结论 |
|---|---|---|
| PhysicalRefinement:13 | `Physical.physicalMeshScale_tendsto_atTop` | 原 κ min(h⁻⁴⁄⁵,dt⁻²⁄⁵) 趋于正无穷；PASS |
| 同上:27 | `Physical.physicalMeshScale_dt_bound` | 精确 0≤dt·S≤κdt³⁄⁵；PASS |
| 同上:39 | `Physical.physicalMeshScale_dt_tendsto_zero` | dt·S→0，无时空耦合；PASS |
| 同上:47 | `Physical.physical_conditions_eventually` | 原六项物理条件同时最终成立；PASS |
| 同上:66 | `Physical.physical_terminal_norm_tendsto_zero` | 变化状态空间中的真实终端范数由指数估计趋零；PASS |
| FixedBoxControlData:15 | `cartesianGridPotential_bound` | 原势沿真实域/时间等式运输，bound 不变；PASS |
| 同上:24 | `cartesianBoxTimeControl_norm` | 实际 K_h=E_hB_h 的时间重构范数精确等于原控制范数；PASS |
| 同上:36 | `cartesianBoxTimeControl_supported` | 真胞元包含条件给 a.e. 时间值的真实区域支撑；PASS |
| CartesianControlRefinement:18 | `Physical.box_cartesian_controls_independent_refinement` | 全部充分细网格上实际原 HUM 控制、完整状态、原数据及端点极限；PASS |

## 数学核查

**尺度和物理条件。** 两个正变量独立趋零，负幂分别趋于正无穷，故原尺度的 min 亦趋于无穷。dt·S 的上界只用 min 的时间分支以及真实正底数幂运算，指数严格为 3/5；其趋零甚至无需 h 的极限。随后有限个 eventually 条件合并，得到 h≤h₀、dt≤Δ₀、16q_b≤S、S≤q_bT/(4dt)、dt M≤1/2、dt≤T/12。上界从 dt·S≤q_bT/4 乘除正 dt 得到，未输入它本身或附加 dt≤ch²。

**量词与完整尾段。** 主定理固定正维盒、内部开区域 W、ωsharp、ω 和统一步长比 ratio≥1 后，先选择 κ,d₀>0；再对所有 T>0、M≥0 选择 C>0；之后才量化全部网格序列、时间网格、同一势 b 和任意 y₀∈L²。既有盒观测/控制定理的常数次序原样保留。原 qb=`physicalBaseAmplitude Cb qc T M` 的正性在内部证明。`eventually_atTop` 给 J 后，明确使用每一个 `n+J`；所有数据、控制、状态、估计和极限采用同一偏移。这里仅舍去有限个粗网格，没有改成稀疏子列。h、dt 独立趋零，无嵌套、速率或时空耦合假设。

**实际控制和原方程。** 对每个尾段网格，使用 `box_cartesian_physical_control`，其实际观测估计在内部供应，再经真实 penalized HUM 与物理控制缩放得到控制。已重读 `PhysicalHUM` 中 `sqrt(dt)` 控制向量、终端伴随表示及原 Forward 解构造。T197 通过 `choose` 从逐网格存在性取得 u_n 和全部 `Fin(steps+1)` 状态 y_n。`ForwardEquation` 展开为 `(y^{i+1}−y^i)/dt+(A_h+V_h^i)y^{i+1}=B_hu^i`；使用实际物理 Laplacian、实际节点乘法势和零延拓控制。未投影全状态、未假设频率子空间不变，也未把目标方程或控制费用作为输入。

**同一原数据。** `cartesianGridPotential` 只是对同一个 b 沿盒端点与 period 等式的类型运输。之后 `cartesianAveragedPotential` 的实际积分正是 `(dt∏δ_j)⁻¹∫时间胞元∫对偶胞元 b`，原 a.e. 界给每个平均值≤M，未换势或重复平均。初态严格为 E_h* y₀；已核对伴随的原单元平均公式和 `‖E_h*y₀‖≤‖y₀‖`。因此保留原离散费用 `sqrt(C)‖E_h*y₀‖`、终端界 `sqrt(C)e^(−d₀S)‖E_h*y₀‖`，并得到重构控制费用≤sqrt(C)‖y₀‖。sqrt(C) 来自原观测平方常数，与原 HUM 能量推导一致。

**真实区域支撑。** 由 closure ωsharp 紧且包含于开集 ω，先得到统一正距离余量；真实对偶胞元中点到单元点的距离不超过空间维数乘 h，故所有充分细活动胞元实际包含于 ω。`cartesianBoxCellControl` 就是 E_h∘B_h；E_h 等距、B_h 物理等距、真实时间胞元范数公式给控制范数的严格等式。区域支撑结论经限制至 ω 补集的闭核得到，意味着 a.e. 时间截面的 L² 类在 ω 外 a.e. 零，并非仅节点位于 ω。固定盒和固定 T 的运输没有更换测度。

**端点和范围。** 任意原 L² 初值的单元平均强一致性给 E_hy_n(0)→y₀；该依赖实际处理未覆盖边界条带，并经稠密性推广到全部 L²，无初值光滑要求。终端先在变化物理空间中证明范数趋零，再通过 E_h 等距得到同一固定 L² 空间中的终端重构强趋零；二者属于前面选择的同一状态序列。N_j>0 被用于平均一致性，原 N_j≥2 满足它；正步长和固定宽度等式保留原网格。几何 W、ωsharp 是原内部控制区域的显式选择；本批只覆盖正维 Cartesian 盒实现。没有识别连续状态时间迹，也没有清偿每个控制弱积点的有限弱恒等式、V′ 时间导数或完整 P021。

## 依赖、公理与本机证据

三个新模块的项目 import 闭包共 833 个文件，其中 830 个既有文件与数学基线逐字节不变。关键的实际盒控制、支撑、单元平均强一致性及固定势运输已读取；相应闭包与既有接受版本一致。没有重复把旧论文结果标为本批新完成。

三个模块均由固定根导入；9 项完整类型与公理记录均在固定 audit 中。实际工具通过 `privateToUserName`/`collectAxioms` 递归检查 Carleman 全命名空间，raw 末行 **8726 项 PASS**。本批每项以及全部显式公理记录均只含 `propext`、`Classical.choice`、`Quot.sound`，无 sorryAx 或新数学公理。

独立计算并核对源码清单全部 **954 个不同路径**：恰好覆盖全部 tracked Lean 文件及 lean-toolchain、lake-manifest.json、lakefile.toml，与 checked_sha 的 Git 字节全部匹配，无遗漏；审查时这些工作树受检文件也相同。Lean 4.35.0/compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` 和 mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 保持固定。

| 本地文件 | 独立核对结果 |
|---|---|
| `/tmp/carleman-t197-target.log` | 4071 jobs 成功；245 bytes；SHA256 `9a8367f5602f82b6a2136d3e37d97f503f87794e7c816b4d301d6752d41d525d` |
| `/tmp/carleman-t197-build.log` | 全库 4189 jobs 成功；80 bytes；SHA256 `66400bf305ab35fc7048188068733d7c06efcfdbf70ee3fb6c0cd9fc88412bc2` |
| `/tmp/carleman-t197-axioms.log` | stderr 0 bytes |
| `/tmp/carleman-t197-refinement-local-axioms.txt` | 2864551 bytes；8726 项；SHA256 `65a777f78bd2aabf23508bc8b1d8aad10a420402af8ac4e7fe55722bf2d425cd` |
| `/tmp/carleman-t197-local-source-manifest.txt` | 954 条，103386 bytes；SHA256 `c7aa2c7608c568198cc7e80c14c2e76ca78f5d2b33e848ff7138b56cfe28cc78` |
| `/tmp/carleman-t197-local-evidence.json` | 931 bytes；SHA256 `d5ed6c677a2ea5f995049f0f52c69e3c9ac00c5cf86904d12cd9fa7db13bad30` |

evidence.json 的 checked/source SHA 均精确对应本报告版本，source=local、status=PASS、ci_url=null，finished_at=`2026-10-20T02:41:26.974440+00:00`。记录 `lake build Carleman`、`lake env lean tools/CheckAxioms.lean` 的实际退出值均为 0，manifest/raw 摘要与独立计算一致。本报告核验这些真实本机执行证据，不声称审查者另行重跑构建或取得远端成功。

只提交本报告；签发后正文及 reviewed_at 冻结，不修改证明、台账或其他报告。
