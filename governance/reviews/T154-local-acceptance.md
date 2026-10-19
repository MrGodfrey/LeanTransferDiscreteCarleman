# T154 / C170 独立本机验收

- `checked_sha`: `abadce407f55be6c99212cbf92654e8fa44a7c2d`
- `base_commit`: `7a2da98bcead43801f48dc03ecffbc70adc7585e`
- `reviewed_at`: `2026-10-19T11:02:16+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：全实线 C² 周期时间权的真实归一化光滑卷积、实际导数交换、统一上下界及 qclass 逼近。**P024 / prop:continuousCE 不提升，原文覆盖保持 17/26。**

本 Agent 直接读取固定 Git 对象中四模块全部证明、19 项完整展开类型、原 `paper/main.tex:292–299,2672–2731`、T154 分析、MATH_SPEC 和固定 C170/T154 台账，独立核查关键依赖及其版本。AGENTS、PROJECT_OPERATIONS、state/README 与此前已读协议逐字节相同。正式 CI 的状态和两份原始工件由本 Agent 自行查询、下载及比较；执行者报告、旧验收和 CI 未替代数学判断。后续 BoxTimeIntegralLimit、BoxC2HeatEstimate、PeriodicPrimitive、PeriodicC2Extension 草稿及动态 `.ci/axioms.txt` 全部排除。

## 原文对应与准确范围

原 qclass 要求 T>0、q∈C²([0,T])，零至二阶端点匹配，1≤q_c≤q≤q_max，|q′|≤βq²、|q″|≤β²q³；原连续 CE 对全部符合该类的权与全部指定 Sobolev 轨道成立。本阶段输入是更强的**全实线 ContDiff ℝ 2 q 与实际 T 周期性**，只证明光滑时间权逼近。尚未从闭区间 C² 及端点匹配构造这一全局延拓，尚未证明加权积分极限、原完整弱轨道或一般多面体结论。

最终 `exists_periodic_C2_smooth_qclass_exact` 的输入导数界是 **β/9** 和 **(β/9)²**，输出才是 β 和 β²；不能读成对固定 β 的任意原 qclass 权无损平滑。这个固定数值余量不依赖 T、q，符合未来先选择足够小 β 的用途，但本批没有因此完成原 CE。辅助定理允许 β=0 和任意 q_c>0，比原 β>0、q_c≥1 更广；T>0 保持原范围。

## 全部 19 项公开声明

名称省略 `Carleman.`。源位置相对于 Carleman；源行来自固定提交，类型行来自本 Agent 独立下载的原始 `axioms.txt`。清单顺序与交付 manifest、固定 C170 和 T154 完全一致。

| # | 声明 | 固定源位置 / 完整类型行 | 独立结论 |
|---|---|---|---|
| 1 | `temporalBump` | `Weights/TemporalMollification.lean:14` / 30826 | PASS；真实 ContDiffBump，内外半径分别为 1/(n+1)、2/(n+1)，所有 n 包括 0 均正且严格有序。 |
| 2 | `temporalMollification` | `Weights/TemporalMollification.lean:20` / 30828 | PASS；实际 Lebesgue 归一化核与原 q 的乘法卷积，不是任意逼近序列或形式导数字段。 |
| 3 | `temporalMollification_smooth` | `Weights/TemporalMollification.lean:23` / 30830 | PASS；紧支 C∞ 核与连续 q 的真实局部可积性给全局 C∞。 |
| 4 | `temporalMollification_periodic` | `Weights/TemporalMollification.lean:28` / 30833 | PASS；在同一卷积中逐点使用 q(t+T−s)=q(t−s)，保持实际周期。 |
| 5 | `temporalMollification_bounds` | `Weights/TemporalMollification.lean:37` / 30836 | PASS；内部证明卷积可积，以非负单位质量核精确保持任意全局上下界。 |
| 6 | `temporalBump_radius_tendsto` | `Weights/TemporalMollification.lean:51` / 30843 | PASS；真实外半径 2/(n+1) 趋零。 |
| 7 | `temporalMollification_tendsto` | `Weights/TemporalMollification.lean:55` / 30845 | PASS；对每个实 t，实际卷积值收敛于同一连续 q(t)。 |
| 8 | `continuous_periodic_bounded` | `Weights/TemporalMollification.lean:59` / 30848 | PASS；闭周期区间紧性和周期代表内部产生正全局绝对值界 B，不增加有界性假设。 |
| 9 | `temporalMollification_hasDerivAt` | `Weights/TemporalMollificationDerivative.lean:14` / 30851 | PASS；真实参数微分与可积支配证明导数为同核对实际 q′ 的卷积。 |
| 10 | `temporalMollification_deriv_periodic` | `Weights/TemporalMollificationDerivative.lean:45` / 30858 | PASS；从 C¹ 周期 q 内部供应 q′ 全局界，输出实际函数级 deriv 恒等式。 |
| 11 | `temporalMollification_second_deriv_periodic` | `Weights/TemporalMollificationDerivative.lean:52` / 30865 | PASS；C² 给 q′ 的 C¹，应用同一一阶结论两次，得到实际 q″ 卷积，无 C³ 前提。 |
| 12 | `temporal_derivative_difference` | `Weights/TemporalMollificationBounds.lean:12` / 30873 | PASS；真实一阶导数界经凸集均值定理给全部 s,t 的 Lipschitz 差界。 |
| 13 | `temporalMollification_uniform_error` | `Weights/TemporalMollificationBounds.lean:21` / 30876 | PASS；真实核支持和均值差界给所有 t 的误差 ≤D r_n。 |
| 14 | `temporalMollification_local_norm_bound` | `Weights/TemporalMollificationBounds.lean:33` / 30883 | PASS；仅核支持内的实际函数绝对值界即可控制卷积；支持外核严格为零。 |
| 15 | `temporalMollification_support_comparison` | `Weights/TemporalMollificationBounds.lean:51` / 30886 | PASS；D r_n≤q_c/2、同一原下界与两次均值误差内部推出 q(t−s)≤3q_n(t)。 |
| 16 | `periodic_time_weight_bounds_global` | `Weights/PeriodicC2Mollification.lean:11` / 30898 | PASS；q、真实 q′、真实 q″ 联合周期性选同一周期代表，将区间三界推广至所有实时间。 |
| 17 | `temporalMollification_qclass` | `Weights/PeriodicC2Mollification.lean:32` / 30906 | PASS；正性保证平方、立方比较方向，实际导数交换和局部平均给 9β、27β²，不把它们作为前提。 |
| 18 | `exists_periodic_C2_smooth_qclass` | `Weights/PeriodicC2Mollification.lean:64` / 30927 | PASS；内部选择统一有限前缀 N，全部 n、全部 t 保持 q_c、共享上界 B、周期及放大导数界，并逐点收敛。 |
| 19 | `exists_periodic_C2_smooth_qclass_exact` | `Weights/PeriodicC2Mollification.lean:94` / 30950 | PASS；输入 β/9 余量，输出目标 β/β²，同一序列和统一 B 保持不变。 |

## 真实核、可积性及导数交换

令 κ_n(s)=(temporalBump n).normed volume s。已核查固定 mathlib 的 `BumpFunction/Normed.lean:32–80`：κ_n 是原 bump 除以其严格正积分，非负、C∞、紧支，支持精确为 ball(0,r_n)，真实 Lebesgue 积分为 1。正分母由有限维 Lebesgue 测度的开集正测度性质证明，不是假设归一化成功。实际 q_n(t)=∫κ_n(s)q(t−s) ds。

`ContDiff/Convolution.lean:428–433` 的光滑卷积定理要求紧支光滑核与原函数局部可积；代码由 q 连续内部供应后者，Lebesgue 平移及负号不变性满足所需实例。上下界证明另显式构造实际乘积 Integrable，再用积分单调性和单位质量；因此没有利用不可积函数默认积分值假装正平均。

微分交换直接对 F(t,s)=κ_n(s)q(t−s) 计算 HasDerivAt，候选导数是真实 κ_n(s)deriv q(t−s)。已核对 `ParametricIntegral.lean:284–305` 全部前提：原点的实际可积性、邻域可测性、导数可测性、全部邻域参数上的导数界、可积支配以及真实逐参数导数。这里取整个实线作为邻域，支配是 κ_n(s)D；κ_n≥0 与 |q′|≤D 给范数界，κ_n 的实际可积性给支配可积。定理还返回导数被积函数的可积性。

周期导数并非另加假设：已重读 `smoothD_periodic`，它由真实 Fréchet 微分的平移链式恒等式及周期函数相等证明；在实线上 e=1 正是实际 deriv。C¹ 周期 q 的 q′ 连续且周期，在 Icc(0,T) 上取界再延至全实线。C² 情形中 q′ 为 C¹，二次应用同一交换结论；没有要求原 q 的三阶导数或原 q 全局可积。

局部平均界第14项允许任意 f，使用 mathlib `norm_integral_le_of_norm_le` 的一般 Bochner 积分不等式，本身不输出任意 f 的可积性。实际 qclass 应用只用连续的 q′、q″，其紧支核乘积确实可积；特别没有从该广义辅助引理偷推任意不可测函数的可积性。

## 常数、同一序列和 qclass 量词

均值定理给 |q(s)−q(t)|≤D|s−t|，因此所有 t 的卷积误差 ≤D r_n。若 D r_n≤q_c/2，核支持内同时有 q(t−s)≤q(t)+q_c/2 和 q_n(t)≥q(t)−q_c/2。由 q(t)≥q_c 得前者 ≤3q_n(t)。比较完全来自原函数和真实卷积，没有将所需 qclass 或支持比较作为最终外部前提。

q_c>0 保证原采样值及 q_n 均为正。对支持内同一比较分别取平方、立方，再用原导数界及单位正平均，得到 |q_n′|≤9βq_n²、|q_n″|≤27β²q_n³。二阶系数是 **27β²**，不是 (9β)²，也没有漏掉 β 的平方。

区间界推广时，将 (q,q′,q″) 作为一个周期三元组，用同一个 s∈Ico(0,T) 代表任意实 t，保证三个值和幂次一致。固定 q、T 后，内部选择实际 q 的全局正界 B 和 q′ 的正界 D；r_n→0 与 q_c>0 产生一个 N。输出恰为 qs(n)=q_{n+N}，N 对所有 t 和后续 n 相同。B 在选择 qs 之前出现，对全部 n、t 统一；B、D、N 可以依赖原 q、T，不是声称跨所有 q/T 的统一上界。原给定 q_max 若作为全局上界，也由第5项精确保留；最终存在性入口不需要另输入 q_max。

最后将输入参数换成 β/9，9(β/9)=β，27(β/9)²=β²/3≤β²；第二步使用 qs≥q_c>0 保证三次幂非负，β=0 也包含。数值余量独立于 T、q、q_c、q_max。全序列逐点收敛由实际卷积收敛及 n↦n+N 趋无穷证明，不要求原 q 有光滑代表。当前公开最终结论只输出值的逐点收敛和导数界，未宣称已经输出加权积分极限或完整 CE。

## 固定依赖、公理及构建

四模块声明数 8+3+4+4=19，全部由固定 `Carleman.lean` 导入，固定 `tools/CheckAxioms.lean` 中各有实际完整类型及公理打印；没有漏列的新公开或私有辅助声明。新源码无 sorry、admit、新数学 axiom 或 native_decide。

实际递归 Carleman import 闭包共 **86** 模块，其中 **82** 个旧模块均与基线逐字节相同。唯一直接引入旧 Carleman 理论的入口 `PeriodicHeatFlux` 的整个82模块闭包与已验收 C162 版本 `c598090a2e592f2e2a5441e5d05eaec994e9b1b3` 完全相同，实际所用 `smoothD_periodic` 已重读。治理前序 C169 的 `BoxSmoothHeatBothSigns` 及其129模块闭包也与基线已验收版本完全相同；本批卷积证明并未调用这个 CE 结论，故不存在用待推广估计反过来证明平滑 qclass 的循环。版本追溯见 [T146](T146-local-acceptance.md)、[T153](T153-local-acceptance.md)。

Lean pin 为4.35.0，mathlib pin 与本机实际 HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，依赖工作树干净。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。已实际读取 `/tmp/carleman-t154-periodic-qclass-final-target.log` 的3236 jobs成功，以及 `/tmp/carleman-t154-periodic-c2-mollification-build.log` 的4034 jobs成功。该前缀 `-axioms.log` 为空，因此本报告的公理证据来自实际固定 raw 和同 run 下载 raw 的内容，而不以空日志证明审计通过。

已读审计主体：按 privateToUserName 遍历全部 Carleman 环境常量并递归 collectAxioms，仅容许 propext、Classical.choice、Quot.sound。raw 末行实报 **7613** 项递归审计 PASS；另扫描2860条非空公理打印记录和9条无公理记录，未见其他公理，未将打印条数与全量递归声明数混同。19项本批声明均有实际展开类型，所列公理均恰为上述三项正常基础公理。固定 CI、构建脚本和工具链配置与此前核验版本相同。

## 独立正式 CI 与原始工件

本 Agent 实际查询 [main CI run 39241104262 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39241104262/attempts/1)：event=push、head_branch=main、head_sha=`abadce407f55be6c99212cbf92654e8fa44a7c2d`，顶层 completed/success，updated_at=`2026-10-19T11:00:32Z`。三项 job 均 completed/success：

| job | 实际 ID | 最终结果 |
|---|---:|---|
| state-check | 118021835701 | success |
| lean | 118021836470 | success |
| dashboard / snapshot | 118023095522 | success |

本 Agent 从同 run 自行 gh run download 两份原始工件，两下载进程 exit 0；实际 artifact 元数据均绑定同 SHA：

| 工件 | 实际 artifact ID | 归档 bytes | 归档 SHA256 |
|---|---:|---:|---|
| lean-ci-result | 12180624872 | 492 | `7f36b8dbd741a468b0e2399960f4cf3bf08273a398831c57eb55eff8c807be24` |
| lean-declaration-evidence | 12181825941 | 219724 | `f1a64d18d1e2fb6c4a55b67ab8d6781eab947fc05314273e7380a366718bf11e` |

实际读取 `/tmp/carleman-t154-periodic-c2-mollification-main-ci/result.json`：status=PASS，checked_sha 与 source_head_sha 均等于本报告固定 SHA，ci_url 为同 run/attempt，finished_at=`2026-10-19T10:59:13.474014+00:00`，targets=[Carleman]；Linux Lean4.35.0 编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib 与上述 pin 一致。

实际下载 `/tmp/carleman-t154-periodic-c2-mollification-main-axioms/axioms.txt` 与固定 `/tmp/carleman-t154-periodic-c2-mollification-local-axioms.txt` **逐字节相同**，均 **2366953 bytes**，原始 SHA256 **`03366ecb34540e5c9d18ced9c1ddd8cf686f8866194a6ec20b37efda00c98626`**。原始文件 hash 与 ZIP 归档 hash 分开记录；远端 raw 含全部19项完整类型及7613项递归公理 PASS。

## 签发结论

**T154 / C170 可在该固定版本登记 REVIEWED，scope 保持 AUXILIARY。** 19项声明的语义、公理及版本证据均 PASS，未发现需修复缺陷。输入全局 C² 周期性和最终 β/9 余量均明确存在；闭区间周期延拓、实际加权积分极限、完整弱轨道与一般多面体仍未在本批清偿，不得提升完整 P024，原文覆盖保持17/26。签发后冻结正文和 reviewed_at，仅单独提交本报告，不改数学、台账、root/audit 或原稿，不推送。
