# T184 / C200 独立本机验收：原有限元时间平均势的强 L² 一致性

- checked_sha / source_sha: `01d32d5c9dc4a907e058d302714a3f64366e8767`
- mathematical_base: `8e2e1e1a269c81ea0f9fdd98c6f13477cf8583b8`
- reviewed_at: `2026-10-19T15:33:18+00:00`
- reviewer: 独立本机数学验收 Agent `/root/accept_spatial_lemma`
- result / axiom_check: **PASS / PASS**，全部 **15/15** 显式声明通过，无阻断缺陷。
- scope: **AUXILIARY**；仅原有限元时间平均势的强 L² 一致性，原文覆盖保持 **17/26**。

## 固定版本、原命题和验收范围

直接读取固定 Git 对象的四个新模块全部证明、固定 raw 的十五项完整展开类型、T184 分析、MATH_SPEC 和 C200/T184 台账。AGENTS、PROJECT_OPERATIONS、state/README、MILESTONES、PAPER_COVERAGE 的内容哈希均与本 Agent 已读固定版本相同，沿用其证据与验收规则。本次未将动态 `.ci/axioms.txt`、后续 PotentialTestConsistency / PotentialWeakPairing / AveragedPotentialWeakPairing 或变化中的根导入当作证据。

原文实际对照 `paper/main.tex:2294–2330` 与 `2893–2925`：eq:conv-data-fe 是 **bⁿ(x)=dt⁻¹∫_(tₙ₋₁,tₙ)b(t,x)dt**，2907 行定义有限元分片势在每个时间单元取同一个 bⁿ(x)，2917–2920 行要求保持原 M 界并强时空 L² 收敛。2893 行明确 T、初值、b 固定，时间 dt=T/N 趋零；本批不涉及空间取样，故有限元势根本不依赖 h。本批结论正好清偿这部分势的一致性，没有假设空间细化、形状、分级或时空步长耦合。原稿 SHA256=`492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，与已验原稿不变。

已完整读取 [T183 冻结报告](T183-local-acceptance.md)，并将当前报告字节与其单文件提交 **`9c59cce67dc2096daa946b11f69f02942a979aa3`** 比对相等；其 checked_sha 正是本批 mathematical_base，reviewed_at=`2026-10-19T15:18:34+00:00`，13/13 PASS、AUXILIARY。另重新读取本批真正调用的有限单元强逼近、原时间单元/平均、实际有界乘子与 L² 类、Fubini 和支配收敛入口；不以已有报告代替依赖检查。

## 全部十五项声明

顺序与固定 manifest 一致。源码位置相对 `Carleman/Control/`；raw 行为固定完整类型的起始行。三项是实际定义，其余十二项是已证明定理。

| 序号 | 完整声明 | 固定源码 / raw 行 | 验收结论 |
| --- | --- | --- | --- |
| 1 | `Carleman.fixedTimeCellIsometry` | `FixedTimeCellStrongConvergence.lean:13` / 35008 | 原时间单元指示重构，实际 dt 物理质量到固定区间 L² 的等距；PASS。 |
| 2 | `Carleman.fixedTimeCellIsometry_adjoint_average` | `FixedTimeCellStrongConvergence.lean:18` / 35014 | 真正 Hilbert 伴随逐坐标等于 dt 归一化原 Lebesgue 积分；PASS。 |
| 3 | `Carleman.fixedTimeCell_uncovered_volume` | `FixedTimeCellStrongConvergence.lean:27` / 35019 | 真实时间未覆盖集合的限制测度为零；PASS。 |
| 4 | `Carleman.fixedTimeCell_average_strong_convergence` | `FixedTimeCellStrongConvergence.lean:38` / 35024 | 任意原标量时间 L² 类的真实 EₙEₙ* 强逼近；PASS。 |
| 5 | `Carleman.timeReconstructedPotential` | `TimePotentialReconstruction.lean:14` / 35035 | 同一原时间平均的完整分片势，实际乘积可测与 a.e. 保界；PASS。 |
| 6 | `Carleman.timeReconstructedPotential_bound` | `TimePotentialReconstruction.lean:41` / 35043 | bound 字段准确保持原 b.bound；PASS。 |
| 7 | `Carleman.timeReconstructedPotential_on_cell` | `TimePotentialReconstruction.lean:45` / 35048 | 时间单元上实际值等于原 bⁿ(x)；PASS。 |
| 8 | `Carleman.fixedTimePotential` | `TimePotentialReconstruction.lean:51` / 35055 | 仅以 period=T 运输同一分片势到字面相同的时空域；PASS。 |
| 9 | `Carleman.fixedTimePotential_bound` | `TimePotentialReconstruction.lean:57` / 35065 | 固定域版本保留同一预算；PASS。 |
| 10 | `Carleman.fixedTimePotential_value` | `TimePotentialReconstruction.lean:63` / 35070 | 类型运输后仍是同一 dt⁻¹ 时间积分的有限指示和；PASS。 |
| 11 | `Carleman.BoundedMultiplier.sub_sq_integrable` | `TimePotentialSlices.lean:16` / 35077 | 任意有限测度上两实际有界函数差平方真正可积；PASS。 |
| 12 | `Carleman.BoundedMultiplier.toL2_sub_norm_sq` | `TimePotentialSlices.lean:26` / 35081 | 原 L² 类之差的范数平方恰为真实代表差平方积分；PASS。 |
| 13 | `Carleman.fixedTimePotential_slice_error` | `TimePotentialSlices.lean:36` / 35085 | 合法原切片的误差积分严格等于同一 E E* 投影残差平方；PASS。 |
| 14 | `Carleman.fixedTimePotential_slice_error_tendsto` | `TimePotentialSlices.lean:63` / 35096 | 内部得到 a.e. 合法时间切片，对同一切片得到平方误差趋零；PASS。 |
| 15 | `Carleman.timeAveragedPotential_strong_convergence` | `TimePotentialStrongConvergence.lean:14` / 35108 | 真实 Fubini 与可积支配将切片极限提升为原时空 L² 强收敛；PASS。 |

## 实际时间几何、伴随与任意 L² 数据

`TimeGrid.physicalTimeCell i` 是 **(nodeTime i,nodeTime i+dt]**，其中 i:Fin steps 对应原 n=i+1。重新读取的原构造证明这些单元都包含于 (0,period]、严格不交、真实 Lebesgue 质量恰为 dt。第 1 项使用同一真实单元和 `PhysicalFiniteSpace (Fin steps) dt` 的实际质量内积；其陪域是 **Lp ℝ 2 (volume.restrict (Ioc 0 T))**。这里不是抽象指定平均算子，也没有把不同时间域的范数混同。

第 2 项展开真实 `ContinuousLinearMap.adjoint`：系数恰为 **dt⁻¹∫_(physicalTimeCell i)u(t)dt**。依赖中有限单元的真实积分可积性已供应；本批用单元包含于 (0,T] 和 `restrict_restrict` 消去重复限制，所得是原 Lebesgue 单元积分。没有点值采样任意 L² 代表，亦没有以另一个自定义“伴随”替代 Hilbert 伴随。

第 3 项在有限测度中用真实有限不交并质量公式，已覆盖质量为 steps·dt=T；整个限制区间质量也为 T，所以真实补集测度为零。未预设单元全覆盖。左开右闭使内部时间端点无重复，末端 T 被包含；0 与原积分区间的差异是 Lebesgue 零测集。第 4 项内部选择固定紧集 [0,T]、左端点 nodeTime i，并从实际单元定义证明 **dist(t,nodeTime i)≤dt**；左端点虽不在左开单元内，却确实在所需的共同紧集中，符合通用逼近定理的准确假设。

通用 `finiteCell_average_strong_convergence` 的依赖本次重新读取：先用紧集上的连续模给有界连续函数的真实单元平均误差，再用实际 L² 稠密性与 **Id−EE*** 范数≤1推广到全部 L² 类。辅助连续函数的节点值只用于比较候选，不进入原 u 的定义。固定时间区间的有限 Borel 测度内部提供所需弱正则实例。本批没有假设原 u 连续、H¹ 或已有逼近序列，没有要求时间网格嵌套，也没有要求所有层的有限指标类型相同。

最终时间逼近量词为固定 T、任意 g_n 且 period(g_n)=T、dt_n→0、任意同一个 u∈L²(0,T)。TimeGrid 的 dt>0、steps>0 与 period=T 实际强制 T>0；写出的 0≤T 允许 T=0 的空前提分支，但没有借用不存在的正步长零周期网格。没有声称变化 T_n 的极限或全 L² 单位球上的统一收敛速度。

## 原分片势、a.e. 代表与切片资格

`BoundedMultiplier` 的完整字段仅为实际 value、AEStronglyMeasurable、非负有限 bound 以及 a.e. 绝对值界。它没有处处连续、空间正则、时间周期性或额外可积性字段。原有限柱体上的 b∈L∞ 可用同一预算 M 表示；本批不要求精确本质上确界等于 bound。

第 5 项实际构造有限和 **Σ_i 1_(timecell i)(t) · bⁱ(x)**，bⁱ 是既有 `timeCellPotential` 对同一 b 的真实时间平均。乘积可测性由原空间平均系数的 AEStronglyMeasurable，经真实第二投影的 quasiMeasurePreserving 拉回，再乘可测时间单元指示并有限求和。内部证明的 a.e. 系数界经过有限指标 `ae_all_iff` 统一，再由单元不交得整体界 **b.bound**，没有多出 steps 因子。

第 7 项在每个真实时间单元逐点化简为同一平均系数，覆盖原 bⁿ(x) 公式。坏空间切片上的 Bochner 积分仍有定义，但分析性结论只在合法的 a.e. 切片使用；没有把这些定义值冒称原势的任意点代表。第 8–10 项仅消去 period=T 的等式，保留全部实际值与 bound；没有引入新势、空间平均或随网格变化的原数据。有限和在单元外为零，区间内未覆盖测度已证为零。

第 13 项是条件明确的切片引理：给定 x、真实时间 L² 类 u 和 **u(t)=b(t,x) a.e.**，先将该身份正确限制到每个时间单元，证明每个原平均系数严格等于 E*u 的对应坐标，再通过真实有限指示重构的 a.e. 身份得到 E(E*u)=重构势切片。最后用 `Lp.coeFn_sub`、L² 内积积分公式与同一原切片身份证明误差积分恰为 **‖EE*u−u‖²**。这不是仅一个上界，也没有假设目标逼近。

第 14 项完全内部清偿上一引理的切片前提：`b.measurable.prodMk_right` 给 a.e. 空间点的时间可测性；真实乘积交换的 measurePreserving 与 `ae_ae_of_ae_prod` 给这些时间切片的原 a.e. 界。有限时间测度上的 `MemLp.of_bound` 构造同一切片的真实 L² 类 u，随后对所有 n 使用这个固定 u。整个论证只交有限个 a.e. 性质，未交换不可数全称量词与 a.e.，也未假设每个 x 的切片都良好或原 b 在时间点上逐点收敛。

通用分片构造和切片结论只保留 SFinite ν；最终强时空结论收紧为 **IsFiniteMeasure ν**，以保证原 b∈L² 及支配常数可积。这是原有限体积空间域已满足的条件，不要求空间是欧氏、开、凸、拓扑可分，亦不排除零测空间或空空间。时间平均的既有 `averageFirst_congr` / `timeCellPotential_congr` 与本批所有 a.e. 身份保证原代表的零测修改不会变成节点采样误差。

## 真实 Fubini、可积支配与强时空极限

第 11 项先对任意两个实际有界乘子证明差平方真正可积：用实际 a.e. 可测性和上界 **(b.bound+c.bound)²**，在有限测度上调用 integrable_const 和 mono'。第 12 项通过真正 L² 内积及 toL2 的 a.e. 代表身份识别平方积分，不是以目标积分定义范数。

第 15 项设 μ=volume|(0,T]、β_n 为同一固定原 b 的时间平均，**F_n(x)=∫_t(β_n(t,x)−b(t,x))²dμ**。F_n 的真实 AEStronglyMeasurable 由乘积可测性、交换和实际参数积分定理供应。两个原界给 **|β_n−b|≤2 b.bound a.e.**，交换并取时间切片后实际积分范数估计给 **‖F_n(x)‖≤(2 b.bound)²T a.e.**，其中 μ.real univ=T 已内部计算。这个界独立于 n、dt、空间网格、空间点和原代表。

空间测度有限使这个常数函数真正可积；第 14 项已给 F_n→0 a.e.。本次重新读取 mathlib 的 `tendsto_integral_of_dominated_convergence`，所需每项可测性、可积支配、a.e. 界与同一序列的 a.e. 极限均在实际调用中提供。没有用原势光滑性替代密度，也没有通过未经证明的时间点态收敛应用支配收敛。

关键换序是 **‖β_n.toL2−b.toL2‖²=∫_ΩF_n dν**。代码先用第 12 项得到真实乘积积分，再向 `integral_prod_symm` 明确传入第 11 项在有限乘积测度上的 Integrable 证明。本次读取该 mathlib 定理的真实签名，确认确有全乘积 L¹ 前提；不是使用不可积 Bochner 积分默认值制造 Fubini 身份。虽然中间范数积分上界本身可不要求可积性，最终换序所需可积性在此明确清偿。

支配收敛给真实范数平方趋零；连续平方根和 norm≥0 给范数趋零，最后由 `tendsto_iff_norm_sub_tendsto_zero` 得到 **原时空 L² 范数拓扑中的强收敛**。T、ν 和 b 固定；其支配常数可以依赖 T 和原 b.bound，正符合原固定数据的一致性命题。结论没有偷换成弱收敛、仅切片收敛或范数数值收敛，也不声称变化 T 的统一速率。

## 固定依赖闭包、公理与构建

递归解析四入口的实际 Carleman 导入共 **350** 模块，其中除四新增模块外 **346** 个与 mathematical_base 逐字节一致。另与对应已验收版本比较实际完整闭包，均无变化：

| 关键入口 | 已接受证明版本 | 闭包模块数 |
| --- | --- | --- |
| FiniteCellStrongConvergence / T183 | `8e2e1e1a269c81ea0f9fdd98c6f13477cf8583b8` | 6 |
| AveragedPotentialStrongConvergence / T183 | `8e2e1e1a269c81ea0f9fdd98c6f13477cf8583b8` | 346 |
| TimeCellReconstruction / T177 | `d1134c0ccc8f343aef6223f304fe52f86a7aff1d` | 23 |
| TimeCellAverage / T176 | `ef4e3f83320e3a2d4cc7a074a1df996c13bd9d52` | 18 |
| FiniteCellMultiplier / T182 | `ffa5a6f8061e5b13aa96a7f77081aa4f8482e2e5` | 46 |

固定 Carleman.lean 导入全部四模块；固定 tools/CheckAxioms.lean 对十五项逐条执行 `#check @` 和 `#print axioms`。新源码无 sorry、admit、新 axiom 或 native_decide。十五项仅依赖 **propext、Classical.choice、Quot.sound**。独立解析固定 raw 全部 **3254** 条显式公理记录、**3250** 个不同名字，其中 **9** 条无公理记录，白名单外依赖为零；递归 auditor 末行真实确认 **8404 项 Carleman 声明全部 PASS**。显式记录数与实际递归扫描数分开记录，没有把十五项抽查冒充完整审计。

实际读取 `/tmp/carleman-t184-time-strong-target4.log` 的目标构建 **3542 jobs** 与 `/tmp/carleman-t184-time-potential-consistency-build.log` 的全库 **4142 jobs** 均成功；`-axioms.log` 为零字节 stderr，递归成功取自固定 raw。Lean pin **4.35.0**，compiler commit=`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib pin 和本机干净 HEAD 均为 **`56a005855ea17e0b0958f73ec801ae140b0a1679`**。工具链、manifest、lean-ci/dashboard workflow 与 tools/lean_ci.sh 的哈希和此前已验版本一致。

## 独立同 SHA CI 与原始工件

本 Agent 自行查询实际 GitHub run/jobs/artifacts，并自行执行两次 `gh run download`，均 exit 0。结果工件与声明审计均下载到本批独立 `-main-ci` / `-main-axioms` 目录，未采用执行者的 root 副本。

- run: [39277180466 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39277180466/attempts/1)，event=push、branch=main、head_sha 精确等于本报告 SHA；最终 **completed/success**，updated_at=`2026-10-19T15:29:47Z`。
- jobs: lean **118144497646**（completed_at=`2026-10-19T15:27:07Z`）、state-check **118144497970**（`2026-10-19T15:21:44Z`）、dashboard / snapshot **118147106702**（`2026-10-19T15:27:22Z`）；三项均独立实际查询为 **completed/success**。run 摘要与 job 列表曾暂时不同步；最终通过同 run 的 jobs 分页 API 单独核实 dashboard 的精确 SHA 和终态后才签发。
- `lean-ci-result` artifact **12197174875**，ZIP **493 bytes**，API digest=`sha256:bb5fb0c6701ea35870c44c2472af3aeb3e3bad4aaec5ce3474745198b2c26aa2`。
- `lean-declaration-evidence` artifact **12198531597**，ZIP **248064 bytes**，API digest=`sha256:4d2a1f8b4bef585cd947ec4520894533f1607654e7c8a58c7ca6754769a2ff6a`。
- 两 artifact 的 workflow_run 绑定同一 run、main 和精确 head_sha；压缩 ZIP 的 API digest 与解包 raw hash 分别记录。

独立 `/tmp/carleman-t184-time-potential-consistency-main-ci/result.json` 为 **537 bytes**，SHA256=`50bfba858a6b38ae238afb100b1d1122b3cc72fb10c3b404e98abb57daa07307`。实际 status=PASS、checked_sha=source_head_sha=`01d32d5c9dc4a907e058d302714a3f64366e8767`、targets=[Carleman]、finished_at=`2026-10-19T15:24:34.274299+00:00`，ci_url、Lean、mathlib 与上述记录一致。

独立 `/tmp/carleman-t184-time-potential-consistency-main-axioms/axioms.txt` 与固定 `/tmp/carleman-t184-time-potential-consistency-local-axioms.txt` **逐字节完全一致**，均为 **2684909 bytes**，SHA256 **`caad765bc632187491bf0ba734a38af9ed33fab78ea036d581aafef4897d8a83`**。完整十五项类型、全局公理记录和8404项成功末行均实际核对。曾观察到 PASS result 已存在而 job 尚未终态，未据此提前正式签发。

## 最终结论

**15/15 PASS，无需修复**。同一原有限元时间平均具有真实可测性和同一预算，其 a.e. 合法切片的投影误差严格身份与真实 Fubini、可积支配给任意原有界可测势的强时空 L² 一致性。同 SHA 三项 CI 与原始工件均独立核验通过，C200 可登记 **AUXILIARY / REVIEWED**，原文覆盖保持 **17/26**。本批没有完成状态紧性、极限 PDE、初终值识别或整个控制收敛。仅本报告单文件提交，不 push，不改实现/台账；最终通知后正文与 reviewed_at 冻结。
