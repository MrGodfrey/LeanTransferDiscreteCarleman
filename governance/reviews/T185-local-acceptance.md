# T185 / C201 独立本机验收：原平均势与弱状态的极限配对

- checked_sha / source_sha: `fe308a7e6958dc8a2caa9f9dec3c331ae5678a03`
- mathematical_base: `01d32d5c9dc4a907e058d302714a3f64366e8767`
- reviewed_at: `2026-10-19T16:01:12+00:00`
- reviewer: 独立本机数学验收 Agent `/root/accept_section3`
- result: **PASS，7/7**；三项实际作业由独立下载的完整日志确认成功结束，原始 result/raw 核验通过；API 摘要字段迟滞单独如实记录。
- scope: **AUXILIARY**；仅原势项的弱极限配对，原文覆盖保持 **17/26**。

## 固定版本和原文范围

直接读取固定 Git 对象三模块的完整源码、七项实际展开类型和证明，核对 [T185 分析](../analysis/T185-potential-weak-pairing.md)、MATH_SPEC 及 C201/T185 台账；完整名字、顺序、依赖和 scope 与 manifest 相同。AGENTS、PROJECT_OPERATIONS、state/README、MILESTONES、PAPER_COVERAGE 与本 Agent 已审 T182 逐字节一致，沿用独立验收协议。后续 T186 几何、Kuhn 误差和动态 root/audit 全部排除。

实际对照原 `paper/main.tex:2294–2314` 的 FE 时间平均与 FD 时空单元平均、`2893–2926` 的固定 T 和原数据、独立时空细化、`eq:conv-potential-consistency` 及精确势配对；另读取 `2375–2419` 的状态弱极限与 `eq:conv-limit-identity` 中 **∫(by,φ)**。本批仅识别这个势项，不能用它代替完整极限恒等式。原稿 SHA256=`492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，与已审版本不变。

## 全部七项声明

源码相对 `Carleman/Control/`；raw 行为本次固定完整类型产物中的起始行。

| 序号 | 完整声明 | 固定源码 / raw 行 | 数学判定 |
| --- | --- | --- | --- |
| 1 | `Carleman.BoundedMultiplier.map_toL2_comm` | `PotentialTestConsistency.lean:13` / 35116 | PASS；同一实际有界函数的 L² 乘法交换身份。 |
| 2 | `Carleman.BoundedMultiplier.test_product_error` | 同文件:18 / 35119 | PASS；真实乘积误差分解及正确两项范数界。 |
| 3 | `Carleman.BoundedMultiplier.test_product_strong_convergence` | 同文件:28 / 35123 | PASS；同界势与测试的强 L² 乘积极限。 |
| 4 | `Carleman.hilbert_weak_strong_pairing` | `PotentialWeakPairing.lean:13` / 35132 | PASS；完整弱测试与强收敛因子的真实内积极限。 |
| 5 | `Carleman.potential_weak_pairing_tendsto` | 同文件:30 / 35139 | PASS；真实实值乘子对称性识别原势项。 |
| 6 | `Carleman.timeAveragedPotential_weak_pairing` | `AveragedPotentialWeakPairing.lean:12` / 35151 | PASS；原 FE 时间平均内部供应同界与势一致性。 |
| 7 | `Carleman.cartesianAveragedPotential_weak_pairing` | 同文件:28 / 35166 | PASS；原 FD 时空平均及独立细化的势项极限。 |

## 真实 L² 乘法、误差分解与强乘积

重新读取实际 BoundedMultiplier、map、map_ae、seminorm_le 及 toL2：原 value 只需 AEStronglyMeasurable 和 a.e. 有限绝对值界；map 由真正乘积的 MemLp 构造 L² 类，toL2 则在有限测度下把**同一个 value**放入 L²。第 1 项同时取得两个乘法类和两份 toL2 的 a.e. 代表身份，再以实数乘法交换及 Lp.ext 得 b.map φ.toL2=φ.map b.toL2；不是为 L² 等价类赋予处处相等的代表。

第 2 项通过实际线性乘法的 map_sub 和第 1 项，先在 L² 类中严格证明

`a v − b φ = a(v−φ) + φ(a−b)`。

随后用三角不等式和真实乘子范数界，得到 **‖a v−b φ‖₂≤a.bound·‖v−φ‖₂+φ.bound·‖a−b‖₂**。右侧第二项使用固定测试 φ 的有界性；没有误用 b.bound，也没有遗漏变化测试误差。输入 v 仅为任意 L² 类，允许每个近似测试没有 L∞ 界。

第 3 项保留明确假设 `(a_n).bound≤M`、a_n.toL2→b.toL2 和 v_n→φ.toL2；以同一个 M 控制第一项，再用两项范数趋零和 squeeze_zero 得 **a_n.map v_n→b.map φ.toL2**，这是原 L² 范数拓扑的强收敛。没有假设原势逐点趋近、测试统一有界、状态强收敛或额外光滑性。M 不另写非负是合法的：每个实际 bound≥0，存在 n 的界已强制 M≥0；M=0 不被排除。

有限测度是本组三项的显式条件，使有界 b、φ 的实际 toL2 合法；原有限柱体满足它。固定有界可测 φ 比原光滑有限和测试更广；原测试的紧空间支撑及紧时间区间给所需有界性，不对原 b 或状态增加正则条件。

## 完整弱强配对与原势项

第 4 项在任意实内积空间上证明，实际类型甚至不要求 CompleteSpace。它明确输入 **∀n, ‖u_n‖≤C** 和 **对全部 w∈H 的内积弱收敛**，以及 v_n→z。证明以 Cauchy–Schwarz 给 `|⟨u_n,v_n−z⟩|≤C‖v_n−z‖→0`，再加上固定测试 z 的弱极限。并未从弱收敛中未经证明地推导统一范数界，也未只检查可数精选测试。C≥0 由实际序列界自动成立，C=0 允许。

第 5 项重新使用固定 `BoundedMultiplier.inner_map_left` 的实际积分证明：两侧 L² 内积由 L2.inner_def 展开，在 map_ae 身份下逐点进行实数乘法交换，得到 **⟨a_n u_n,v_n⟩=⟨u_n,a_n v_n⟩**，目标同样为 **⟨b y,φ⟩=⟨y,b φ⟩**。a_n、b 可以变号，不假设非负或可逆；实值性正是这里的对称性来源。

接着用第 3 项供应变化测试 a_n v_n 的真实强极限 bφ，再调用第 4 项，故极限就是原 **⟨b.map y,φ.toL2⟩**。所有乘法类均通过 MemLp 资格构造，配对是原完整 L² 的实际内积；没有偷换成一个只含数字能量的定义。有限空间测度之外不需要额外代表、点值、域边界或 Sobolev 条件。

## FE 原时间平均实例

第 6 项的共同环境为 **Lp ℝ 2 ((volume|(0,T]).prod ν)**，ν 是任意有限空间测度。T、b、φ、ν 固定，全部 g_n.period=T，唯一步长细化要求为 dt_n→0。实际 `fixedTimePotential` 只沿 period=T 的精确等式运输原 timeReconstructedPotential；其值是原时间单元上的 **dt⁻¹∫ b(s,x)ds**，未对空间变量另作平均，未引入 h、空间网格形状或耦合条件。

该 wrapper 内部以 fixedTimePotential_bound 给 `(a_n).bound=b.bound`，并实际调用 T184 的 timeAveragedPotential_strong_convergence，故调用者无需另提供势强收敛或统一预算。重新读取其完整证明和切片依赖：原 a.e. 可测有界 b 在 a.e. 空间点给合法时间 L² 切片；同一切片的真实 EE* 时间平均强收敛，实际误差平方可积及 Fubini 将其识别为全时空范数平方；可积支配 **(2 b.bound)²T** 和 DCT 给全时空强极限。没有假设每个空间切片良好，也没有把仅切片收敛冒充全时空收敛。

尽管声明写0≤T，合法 TimeGrid 的正 steps、dt 及 period=T 已强制 T>0；没有利用不存在的零周期正步长网格。采用左开右闭物理时间单元，最后端点T保留，与原开柱体只差零测端点，b 不需周期性。该极限定理是固定 T 的定性结论，不声称变化 T_n 或所有势单位球的一致速度。

## FD 原时空平均实例与独立细化

第 7 项把所有网格放入字面相同的 **Lp ℝ 2 ((volume|(0,T]).prod(volume|openCoordinateBox lo hi))**。hbox:lo_j+N_n,j δ_n,j=hi_j 和 hT:g_n.period=T 精确固定原域；实际 fixedSpacetimePotential 沿这些等式运输 T182 的完整时空分片势，系数仍是原 **(dt·∏δ)⁻¹∫timecell∫D_a b**，并在未覆盖区域为零。

内部使用 fixedSpacetimePotential_bound 和 T183 的 cartesianAveragedPotential_strong_convergence。重新读取该依赖：原势的真实 L² 类严格等于实际 **E_(h,dt) E_(h,dt)* b.toL2**，由每个系数的 Fubini 平均和 a.e. 代表身份识别；不是另选一份同界或同范数函数。通用单元逼近先由紧集连续模与真实未覆盖测度给连续类误差，再以实际 L² 密度和 Id−EE* 收缩推广至任意原数据。

实际时空几何内部供给共同紧集、正质量 dt·∏δ、两两不交、点距离≤dt+d h 和条带体积趋零。最终 wrapper 只保留原正步长、N_n,j≥1、固定盒、δ_n,j≤h_n、h_n≥0、**h_n→0 与 dt_n→0 分别成立**；无 CFL 关系、网格嵌套、长宽比或数据光滑前提。粗层可有 N_j=1 从而无内部节点；d=0 时空间单点，结果退化为时间平均，不除以 d。

这里的物理势对象与已验收的精确配对一致：原 FD E_h 上的离散乘法对应同一分片乘子，未用刚度分析的 R_h 替换 E_h。新 wrapper 本身以给定环境 L² 状态和测试序列为输入，没有新声明它们已经来自离散解或某个原插值。原物理内积到时空势配对的既有身份可用于后续组装，不能据此跳过 R_h−E_h、时间测试索引及真实状态识别。

## 保留输入和结论边界

两个具体实例均内部清偿**原平均势**的同界和强一致性；仍明确输入状态统一范数界、状态对全部固定 L² 测试的弱极限，以及测试序列的强 L² 逼近。它们不要求状态强收敛，亦不自行证明这些状态/测试输入。初始数据、控制成本、梯度项、时间分部求和及端点识别均未由本批供应。

因此本批忠实完成原 eq:conv-limit-identity 中的**势项极限**。它不等同于完整 PDE、初终值 y(0)=y0/y(T)=0 或控制收敛命题。固定原 T 和原势不随细化序列改变；所有状态和测试的全称量词均保留。scope 维持 AUXILIARY，原文覆盖17/26。

## 固定依赖、公理和本机证据

完整读取 [T183 冻结报告](T183-local-acceptance.md)（提交 `9c59cce67dc2096daa946b11f69f02942a979aa3`，reviewed_at=`2026-10-19T15:18:34+00:00`，13/13 PASS）和 [T184 冻结报告](T184-local-acceptance.md)（提交 `bd45f6d316fb418a6a721b32f00177979f536c18`，reviewed_at=`2026-10-19T15:33:18+00:00`，15/15 PASS）。同时独立读取前述实际实现，未仅依靠其报告结论。

递归解析三个新入口的实际 Carleman 导入闭包共 **353** 个模块，其中 **350** 个既有模块与 mathematical_base 逐字节一致。TimePotentialStrongConvergence 的完整 **350** 模块闭包与 T184 proof `01d32d5c9dc4a907e058d302714a3f64366e8767` 不变；AveragedPotentialStrongConvergence 的 **346** 模块闭包与 T183 proof `8e2e1e1a269c81ea0f9fdd98c6f13477cf8583b8` 不变；实际乘法对称性所在 WeakProduct 的 **22** 模块闭包与已验 T182 proof `ffa5a6f8061e5b13aa96a7f77081aa4f8482e2e5` 不变。没有新循环或修改已接受依赖。

固定 Carleman.lean 导入三个模块，七项在固定 CheckAxioms 中均执行 #check @ 和 #print axioms；新源码无 sorry、admit、新 axiom、native_decide。七项依赖仅为 `propext, Classical.choice, Quot.sound`。完整 raw 独立解析得 **3261** 条显式公理记录、**3257** 个不同名字、其中 **9** 条无公理记录，白名单外依赖为零。实际 auditor 递归 collectAxioms 扫描全部 Carleman 常量，末行为 **8411 项 PASS**；不以空 stderr 作为成功证据。

实际读取 `/tmp/carleman-t185-original-potential-pairing-target.log` 的 **3545 jobs** 和 `/tmp/carleman-t185-potential-weak-pairing-build.log` 的根目标 **4145 jobs** 全部成功。Lean pin v4.35.0，compiler commit=`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib pin 和本机干净 HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。原稿、工具链、manifest、lean workflow 与 tools/lean_ci.sh 相对已审 T182 不变。

## 同 SHA CI 与自行下载工件

本 Agent 自行访问实际 GitHub run/jobs/artifacts API，并独立执行两次 gh run download，两命令均 exit 0。没有采用执行者的 root 下载副本。

- run: [39278938777 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39278938777/attempts/1)，event=push、branch=main、head_sha 精确为 checked_sha。
- 实际三个 job：lean **118149572860**、state-check **118149573238**、dashboard / snapshot **118152689462**。独立完整日志确认三个作业均实际成功结束，详见下节；不将滞后的 API 字段冒写为 completed/success。
- `lean-ci-result` artifact **12200030909**，ZIP **492 bytes**，API digest `sha256:d1b0ed53d926094731246215b608bda79434cf904e5ad19f07bd83f100005fa5`。
- `lean-declaration-evidence` artifact **12200270492**，ZIP **248665 bytes**，API digest `sha256:c81b70f253e730fc369d001e867b16e736a059516f15ce64f39e17235d12cb81`。

两个 artifact 的 workflow_run 均绑定本 run、main 和精确 proof SHA。独立 `/tmp/carleman-t185-potential-weak-pairing-main-ci/result.json` 为 **537 bytes**，SHA256=`9967d6d7d2cda3364d1aac4321d4e69557c6db2d522eb424c7d01f4a1a44f9f5`；实际 status=PASS、checked_sha=source_head_sha=`fe308a7e6958dc8a2caa9f9dec3c331ae5678a03`、targets=[Carleman]、finished_at=`2026-10-19T15:37:29.839016+00:00`，ci_url、Lean 和 mathlib 与实际记录相符。

独立 `/tmp/carleman-t185-potential-weak-pairing-main-axioms/axioms.txt` 与固定 `/tmp/carleman-t185-potential-weak-pairing-local-axioms.txt` **逐字节完全一致**，均为 **2691718 bytes**，SHA256 **`fba82e681a90378abcbef31210ce25fc2cccc2688f8de9bc927e3964e3b01900`**。实际远端七项完整类型、公理名单和末行8411项审计成功已重新核对；ZIP digest 与解包 raw hash 分别记录。

## API 摘要迟滞与三个完整作业日志

签发前实际 REST 和 GraphQL 查询出现摘要字段与完整日志不一致。保存的 `/tmp/carleman-t185-review-run.json` 仍为 status=queued、conclusion=null、updated_at=`2026-10-19T15:33:39Z`；最新 `/tmp/carleman-t185-review-jobs.json` 中 lean、state-check 为 in_progress，dashboard 为 queued，全部 conclusion/completed_at 仍为 null。本报告**没有读到 API completed/success，不作该项虚假陈述**。

为独立核实实际执行，本 Agent 分别从上述三个精确 job ID 的 GitHub `/actions/jobs/{id}/logs` 端点自行下载完整日志，三条下载命令均 exit 0。每份日志有实际 checkout 的完整 proof SHA、对应作业名、正常任务输出及最终 Post job cleanup / Cleaning up orphan processes。逐一检查没有 `##[error]`、非零 process exit 或中断记录；只存在 runner 的 Node.js 兼容性告警。固定 workflow 未对证明、测试或上传配置 continue-on-error。三个日志的证据如下：

| job / 原始日志路径 | 实际成功输出 | 日志末行 UTC | bytes / SHA256 |
| --- | --- | --- | --- |
| lean / `/tmp/carleman-t185-lean-review.log` | 完整4145 jobs构建成功、8411声明审计成功，BUILD_OUTCOME/SETUP_OUTCOME=success；Recorded PASS 精确 SHA；两个证据工件成功上传；2045605022 bytes缓存上传100%、Cache saved，最终清理完成。 | `2026-10-19T15:39:49.6033424Z` | 3740162 / `0b127b343c7dbc19c08cf4c8a2c4ec7d57c36e2dbef3aeedfb1c003e81dab7e4` |
| state-check / `/tmp/carleman-t185-state-check-review.log` | 21个Python测试OK、10个Node测试pass/fail0，State/coverage consistent、display projection matches，最终清理完成。 | `2026-10-19T15:33:50.8542838Z` | 20369 / `20f3d8e840da76fc6b8aae4ca548b9a91ab131421617d202da80d9a649e632cc` |
| dashboard / snapshot / `/tmp/carleman-t185-dashboard-review.log` | 从同run下载同ID/digest的lean-ci-result；EXPECTED_SHA/EXPECTED_CI_URL精确匹配；State/coverage consistent、display projection generated；progress-dashboard工件12200540297成功上传，最终清理完成。 | `2026-10-19T15:43:50.7802528Z` | 16727 / `01d13f0e06a7e5559987d43b8ac6ea0d2fdca8cb99382a38fb8850e63dbcb68e` |

末行时间均为最终清理之后的非失败兼容性告警。dashboard 上传工件为92415 bytes，ZIP SHA256=`eb81149f196c6f7aa41c89af33e85dbca1f29cd00993888d9211f0c3bdbd0f5e`。其实际日志明确使用本run `39278938777`、attempt 1、精确 proof SHA，未混入后续执行。

因此三项实际作业成功结束的判断来自**同一固定版本的完整执行日志和工件**，不是从排队字段、工件存在或执行者口述推定。按本次独立验收的明确授权，以这组实际证据签发，同时保留 API 摘要迟滞这个可复核差异。

## 最终签发

**T185 / C201 独立验收 PASS，七项声明全部通过，无数学修复项。** 同 SHA 的实际三项作业成功、独立下载 result、全量 raw 逐字节一致及递归公理白名单均已核实，CI 摘要迟滞如上单列。允许将本辅助阶段记为 REVIEWED；仍为 AUXILIARY，原文保持17/26，不能提升完整 PDE 或控制极限覆盖。

本报告只针对顶部固定 proof SHA；`reviewed_at` 和正文于签发后冻结，仅单独提交此报告，不修改数学、唯一台账、原稿或后续草稿，不 push。
