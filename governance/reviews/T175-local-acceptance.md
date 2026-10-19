# T175 / C191 独立本机验收：真实 Cartesian 对偶单元重构与平均伴随

- checked_sha / source_sha: `7c2ceacf62d42b168879106b8c6d6fc246c45794`
- mathematical_base: `d93e52fc433c99d25a188effa0c451488098a451`
- reviewed_at: `2026-10-19T14:17:27+00:00`
- reviewer: 独立本机数学验收 Agent `/root/accept_spatial_lemma`
- result / axiom_check: **PASS / PASS**；全部 **21/21** 显式声明通过，其中 5 个实际定义、16 个定理。
- scope: **AUXILIARY**；C191 可登记 REVIEWED。原文覆盖保持 **17/26**，不提升控制收敛的完整原命题。

## 固定版本、原文和验收方法

直接读取固定 Git 对象中的全部三模块、21 项完整展开类型及实际证明，同时核对 T175 分析、MATH_SPEC、C191/T175 台账、原稿和关键依赖。AGENTS、PROJECT_OPERATIONS、state/README、MILESTONES、PAPER_COVERAGE 与基线逐字节相同，继续执行独立语义验收协议。固定台账仍记录 SPECIFIED/RUNNING，这不被误读为已有验收；本报告给出这一精确证明版本的独立结论。当前工作树后续 TimeCellAverage、BoundedMultiplierAverage、CartesianAveragedPotential 和动态 `.ci` 均排除。

原文核对 `paper/main.tex:2290–2345`：`eq:conv-dual-cells` 的实际内部对偶开盒及体积；`eq:conv-data-fd` 的初值单元平均；`eq:conv-pairings` 的 E_h 物理内积、K_h 控制范数及紧随其后的控制配对。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。同一数据公式中的**时空势平均**尚不在本批；时间重构、紧包含活动区给控制支持、强收敛和极限 PDE 也不在本批。

签发前读取已冻结 [T174 报告](T174-local-acceptance.md)，其 checked SHA 正是本批基线，报告提交 `08759a4cb612cbb34ffc8be7a4f7ebbf6fa0a085`，reviewed_at=`2026-10-19T14:03:55+00:00`。T174 作为已验收基线，并不替代本批几何与积分证明。实际控制范数依赖是 [T169 报告](T169-local-acceptance.md) 对应的固定版本；本次重新读取真实控制零延拓、限制伴随、质量内积及保范数证明，并比较其完整源码闭包。

## 21 项声明逐项核对

顺序与固定 manifest、C191/T175 一致。源码位置相对于 `Carleman/`；raw 行指本批固定原始产物中实际完整类型的起始行。

| 序号 | 完整声明 | 固定源码 / raw 行 | 判定及实际内容 |
| --- | --- | --- | --- |
| 1 | `Carleman.cartesianDualCell` | `Geometry/CartesianDualCells.lean:13` / 33798 | PASS；以真实内部节点为中心、各方向半步长的开盒定义。 |
| 2 | `Carleman.cartesianDualCell_measurable` | 同文件:18 / 33801 | PASS；实际开盒的 Borel 可测性。 |
| 3 | `Carleman.cartesianDualCell_subset` | 同文件:22 / 33804 | PASS；真实全部内部节点的单元包含于原物理开盒。 |
| 4 | `Carleman.cartesianDualCell_disjoint` | 同文件:37 / 33809 | PASS；不同整数节点给严格不交的开放单元。 |
| 5 | `Carleman.cartesianDualCell_volume` | 同文件:58 / 33814 | PASS；真实 Lebesgue 实测度等于 ∏δ_j。 |
| 6 | `Carleman.cartesianDualCell_restrict_volume` | 同文件:66 / 33819 | PASS；原域限制测度下仍为同一质量。 |
| 7 | `Carleman.finiteCellLinear` | `Spatial/FiniteCellReconstruction.lean:18` / 33826 | PASS；实际 L² 指示函数的有限线性和。 |
| 8 | `Carleman.finiteCellLinear_ae` | 同文件:27 / 33836 | PASS；L² 类与逐单元常值指示和 a.e. 一致。 |
| 9 | `Carleman.finiteCellLinear_inner` | 同文件:41 / 33841 | PASS；真实 L² 内积精确等于 mass Σ f_i g_i。 |
| 10 | `Carleman.finiteCellIsometry` | 同文件:61 / 33849 | PASS；由真实内积身份构造线性等距嵌入。 |
| 11 | `Carleman.finiteCellLinear_pairing` | 同文件:65 / 33863 | PASS；任意 L² 数据的实际单元积分配对。 |
| 12 | `Carleman.finiteCellIsometry_adjoint` | 同文件:70 / 33869 | PASS；真实 Hilbert 伴随逐坐标为 mass⁻¹∫K_i u。 |
| 13 | `Carleman.finiteCellIsometry_average_norm` | 同文件:88 / 33876 | PASS；真实伴随平均对物理范数不增，常数 1。 |
| 14 | `Carleman.cartesianCellIsometry` | `Spatial/CartesianCellReconstruction.lean:16` / 33882 | PASS；实际 Cartesian E_h 内部供应全部单元条件。 |
| 15 | `Carleman.cartesianCellIsometry_ae` | 同文件:23 / 33890 | PASS；完整物理状态对应原对偶单元指示和。 |
| 16 | `Carleman.cartesianCellIsometry_inner` | 同文件:29 / 33896 | PASS；原物理质量内积与真实域 L² 内积完全相同。 |
| 17 | `Carleman.cartesianCellControl` | 同文件:34 / 33900 | PASS；同一 E_h 与实际节点零延拓 B_h 的 CLM 复合。 |
| 18 | `Carleman.cartesianCellControl_norm` | 同文件:40 / 33909 | PASS；K_h 保原 U_h 范数。 |
| 19 | `Carleman.cartesianCellControl_pairing` | 同文件:46 / 33913 | PASS；原控制配对使用同一 B_h 的真实 Hilbert 伴随。 |
| 20 | `Carleman.cartesianCellIsometry_adjoint_average` | 同文件:55 / 33919 | PASS；平均公式以原 Lebesgue 单元积分表达。 |
| 21 | `Carleman.cartesianCellIsometry_average_norm` | 同文件:68 / 33927 | PASS；任意原域 L² 数据的物理平均范数不增。 |

## 几何、边界条带和退化情形

实际索引为 `CartesianInteriorIndex N = ∀ j, Fin (N j−1)`，节点坐标为 `o_j+(a_j.val+1)δ_j`，完整覆盖原内部节点。由 a_j 的真实 Fin 上界取得 a_j.val+2≤N_j；结合 δ_j>0，两个半步长端点均严格位于原盒内部。首末内部节点也适用，没有删除靠边界一层节点。原稿允许各方向 h_r，本批对应 δ_j，未引入各向同性前提。

不交证明对 a≠b 选择实际不同坐标，利用不同整数至少相差 1 与 δ_j>0，使两个开区间不能同时含同一点。相邻单元的闭包可接触；证明没有把闭单元误作严格不交。体积使用 `openCoordinateBox_volume_real`，其依据是 Euclidean 坐标图的真实 Lebesgue 测度保持和乘积开区间测度，逐边长度精确化简为 δ_j。限制体积使用真实包含关系与 `Measure.restrict_apply`，没有选择或公理化一个“单元体积”。

E_h 是指示函数之和。显式代表在各 D_a 上等于 z_a，在所有单元之外为零；L² 类与该代表的关系为原域限制测度下 a.e.，并未声称任意选定 L² 代表逐点等于该值。未覆盖的边界条带保留为零，单元接口处同样由该代表取零。没有假设单元并等于整个 Ω，也没有把 E_h 定义成 L² 上的满射等距。

不要求非空索引。某方向 N_j≤1 时，全内部索引可以为空，有限和为零，源物理空间为零空间，所有等距与伴随结论仍成立。d=0 时坐标空积为 1、空间为单点、索引为单点；体积公式来自真实零维乘积测度，未假设单点零测或强行套用正维边界零测。开放盒的有限测度实例由真实有界性内部供应，最终 Cartesian 类型没有额外有限测度前提。

## 真实物理范数、积分及伴随

重新展开 `PhysicalFiniteSpace`：其内积直接定义为 `mass * Σ f_i g_i`，范数由该正定内积构造；完整状态和控制都取 mass=∏δ_j。此处没有使用函数空间的 sup 范数，也没有通过未知的有限维范数等价常数取得结论。通用构造量化有限 ι、可测单元 K_i、有限环境测度 ν、正 mass；不交与等质量只在需要等距的声明中显式输入。最终 Cartesian 构造实际证明并供应这些条件。

`finiteCellLinear` 使用 mathlib 的 `indicatorConstLp`，该对象实际是可积指示函数的 `MemLp.toLp`；其 a.e. 公式经过有限和与数乘的真实 Lp 代表身份。内积证明用真实指示函数内积等于 ν.real(K_i∩K_j)，对角项为 mass，非对角项由严格不交为零，再化简双有限和。因此实际获得原 `eq:conv-pairings` 第一式和范数等距。

对任意真实 L² 数据 u，单元积分不是“非可积时为零”的形式表达。本次读取固定 mathlib `L2Space.lean` 的实际证明：`inner_indicatorConstLp_one` 经 `integrableOn_Lp_of_measure_ne_top` 先取得有限测度单元上的可积性，再移出内积和积分。于是配对确为 Σ f_i ∫K_i u。定义候选平均向量后，对**所有**物理 f 比较内积，应用真实 CLM 的 `adjoint_inner_right` 和内积唯一性，证明已存在的 Hilbert 伴随等于该向量；只使用 mass>0 消去 mass，未把一个任意平均算子命名为伴随。

Cartesian 平均公式起初用 ν=volume.restrict Ω。通过 D_a 可测、D_a⊆Ω，实际 `restrict_restrict` 与交集恒等式把积分变为 `∫D_a f ∂volume`。原域外的 Lp 代表值无关，域内 a.e. 变更也不影响单元积分。故对任意 y₀∈L²(Ω)，E_h* y₀ 的每个坐标精确等于原初值离散 `(∏δ_j)⁻¹∫D_a y₀`；不需要连续性、点值或较小的数据子空间。

平均范数界从 E_h 的算子范数≤1 和真实伴随的算子范数身份推出，再用 CLM 的标准范数界。没有要求源空间非零，因此只断言≤1，并未对空索引错误宣称算子范数等于 1。所有精确恒等式和不增范数常数 **1** 同时适用于全部维数、位置、正步长、网格整数、完整状态和全部 L² 数据；无网格大小、长宽比、节点数或数据依赖常数。

## 控制与范围边界

实际控制索引为满足节点位于 ω 的内部索引子类型。`cartesianPhysicalControlExtension` 是在此子类型之外补零的原 B_h；`cartesianPhysicalControl_adjoint` 证明其真实 Hilbert 伴随为节点限制，且相同质量给 B_h*B_h=id。T169 的真实证明由此得 ‖B_hv‖=‖v‖。本批 K_h 定义为同一 E_h.toContinuousLinearMap 复合 B_h，等距立即给 ‖K_hv‖=‖v‖；内积等距与实际伴随身份给 `(K_hv,E_hz)=(v,B_h*z)`，符号和配对方向与原文相同。

ω 在本批可为任意集合，包括空集，所有有限节点条件仍有意义。这没有带来“控制重构支撑于 ω”的结论：节点位于 ω 的对偶单元仍可能越出 ω。原稿后续通过 ω₀⊂⊂ω_sharp⊂⊂ω 和足够细网格解决该问题，本批明确未清偿。也未证明时空势平均、E_hE_h*→Id、数据强收敛、相对弱紧性、连续极限方程或终端零值。AUXILIARY 范围准确，不能据三个标签的局部完成提升整个控制收敛命题。

## 依赖闭包、公理和本机构建

递归读取三模块的实际 Carleman 导入共 **326** 个模块，其中 **323** 个旧模块与 mathematical_base 逐字节相同。进一步比较关键已验收版本：`PhysicalFiniteSpace` 的 1 模块闭包与 C122 固定 SHA `337d9c1b8c5fadce4e638a2c96311e230ee94bb1` 相同；`CartesianPhysicalControlIsometry` 的完整 **323** 模块闭包与 C185/T169 固定 SHA `7d1cc86d3c0a01b524f099ba90baaf59784f159d` 全部相同。后者也覆盖本批调用的内部节点、真实开盒/测度、KuhnCellVolume 和物理控制依赖，没有沿用已变动的旧审查结论。计数 L² 等距虽然在既有项目中可用，本批构造的是新的真实 Lebesgue L² 指示重构。

固定根 `Carleman.lean` 导入全部三模块，`tools/CheckAxioms.lean` 对 21 项均执行实际 `#check @...` 和 `#print axioms ...`。新源码无 sorry、admit、axiom、native_decide。21 项均仅依赖 `propext, Classical.choice, Quot.sound`。独立解析完整 raw 的 **3117** 条显式公理记录（**3113** 个不同名字，含 9 条无公理记录），白名单外依赖为零；实际末尾 `collectAxioms` 对所有 Carleman 常量、包括还原私有名字，给 **8190 项递归审计 PASS**。正常基础公理不被误判为数学假设。

实际读取最终几何定向 `/tmp/carleman-t175-dual-cells-target.log`：**3326 jobs**；最终完整重构 `/tmp/carleman-t175-cartesian-cell-target3.log`：**3517 jobs**；固定 `-build.log`：根目标 **4112 jobs**，均成功。目录中较早的失败草稿日志未被算作成功证据；最终提交及远端完整构建清偿这些已修正问题。固定 `-axioms.log` 是零字节 stderr，结论以完整 raw 为准。

Lean pin v4.35.0，实际 CI compiler commit=`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib pin 与本机干净 HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。工具链、manifest、正式 lean/dashboard workflows 和 `tools/lean_ci.sh` 与基线逐字节相同。检查包括真实类型、公理及源码语义，未把 CI 成功视为数学忠实性的替代。

## 独立同 SHA CI 与原始工件

本 Agent 自行访问 GitHub run、jobs、artifacts API，并分别执行两次 `gh run download`，均 exit 0。实际下载路径为下列 `-main-ci`、`-main-axioms`，没有使用主 Agent 的 root 副本代替独立取证。

- run: [39266504703 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39266504703/attempts/1)，branch=main，head_sha 精确等于本报告 SHA；最终 completed/success，updated_at=`2026-10-19T14:14:12Z`。
- lean job **118107346280**：completed/success，完成于 `2026-10-19T14:13:58Z`。
- state-check job **118107346788**：completed/success，完成于 `2026-10-19T14:10:18Z`。
- dashboard / snapshot job **118109367148**：completed/success，完成于 `2026-10-19T14:14:11Z`。
- `lean-ci-result` artifact **12193517359**，ZIP **493 bytes**；API digest `sha256:ddda3e32b5ec7a592009ef47534750a35728c43d437fe4956cf28b6975f93eef`。
- `lean-declaration-evidence` artifact **12193846838**，ZIP **239808 bytes**；API digest `sha256:ee2e822130c0f05f228c7b7dc39d0db8fa599886e8b64034ce9447264c89f5f4`。

两个工件的 workflow_run 均绑定上述同一 run、main 和精确 SHA。解包后的 result `/tmp/carleman-t175-cartesian-cell-reconstruction-main-ci/result.json` 为 **537 bytes**，SHA256 `22bb2669f8c322435d96b310ebe6dd3f2717161e4354f6d14b98acc611099e86`；实际 status=PASS、checked_sha=source_head_sha=`7c2ceacf62d42b168879106b8c6d6fc246c45794`、targets=[Carleman]、finished_at=`2026-10-19T14:12:48.522344+00:00`，ci_url、Lean 和 mathlib 与上述证据一致。

独立下载的 `/tmp/carleman-t175-cartesian-cell-reconstruction-main-axioms/axioms.txt` 与固定 `/tmp/carleman-t175-cartesian-cell-reconstruction-local-axioms.txt` **逐字节完全一致**，均为 **2597481 bytes**，SHA256 **`99c931015fc5ffe57120be21d7dbc2c41ea0aa517bf7c657ddb8a9f998429293`**。ZIP digest 与解包 raw digest 分别记录；raw 中完整类型、21 项公理及最终 8190 项成功记录实际核对。

## 最终结论

**21/21 PASS，未发现阻断缺陷。** 真实对偶单元、完整物理状态的 Lebesgue L² 等距嵌入、真实单元平均伴随及 K_h=E_hB_h 的原控制范数与配对均已证明。边界条带、空索引和零维情形合法，最终接口无新增目标估计或数据正则性前提。C191 可登记 AUXILIARY/REVIEWED，覆盖维持 **17/26**；完整控制收敛和前述后续义务不由本批完成。本报告仅单文件提交，不 push，不改实现、原稿或总台账；通知后正文与 reviewed_at 冻结。
