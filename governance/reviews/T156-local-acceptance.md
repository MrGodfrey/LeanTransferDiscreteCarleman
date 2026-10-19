# T156 / C172 独立本机验收：原闭区间 C² 权的周期延拓

- checked_sha / source_sha：`b65d78fa150ea0cc5c0cd7d7b3342e7498b1bc50`
- mathematical_base：`069e313b5c03c66aec7c41e72055f95292515e58`
- reviewed_at：`2026-10-19T11:16:02+00:00`
- reviewer：独立本机 Agent `/root/accept_spatial_lemma`，未参与本批实现。
- result：**PASS**；axiom_check：**PASS**；全部 **5/5** 显式声明通过。
- scope：**AUXILIARY — 原闭区间 C² 时间权、光滑周期状态、坐标盒**。C172 可登记 REVIEWED；**P024 / prop:continuousCE 不提升，原文覆盖保持 17/26**。

本 Agent 从固定 Git 对象读取三模块全部实际类型和证明、完整展开声明、原稿、T156 分析、MATH_SPEC、台账、治理协议及关键依赖，独立查询实际同 SHA CI 三个 job，自行下载同 run 原始 result/raw 并逐字节比较固定本机副本。规格、执行者说明、既有报告和 CI 均未替代数学判断。动态 `.ci/axioms.txt` 与后续 LocalOddConvolution / EvenCoordinateKernel / EvenSpatialMollifier / EvenKernelConvolution 草稿全部排除。仅新增并单独提交本报告，不改数学、根导入、审计、台账或原稿，不 push；签发后冻结正文及时间。

## 原文、输入和完成范围

固定 `paper/main.tex:292–299` 要求 q∈C²([0,T])，q、q′、q″ 在 0/T 匹配，并满足 qc≤q、|q′|≤βq²、|q″|≤β²q³；上界 qmax 可以取闭区间最大值。`2672–2733` 的完整连续 CE 还要求原弱周期轨道和相应 Dirichlet 域。本批准确消除先前 C171 要求输入已经是全实线 C² 周期 q 的限制：只输入闭区间 `ContDiffOn ℝ 2 q (Icc 0 T)`、真实一二阶 `derivWithin` 的界和零至二阶端点匹配，内部得到真正全局周期 C² 延拓并用于估计。

这里 q:ℝ→ℝ 只是 Lean 中承载闭区间数据的总函数；没有要求其在区间外连续、可测、可微或周期。端点用原闭区间内导数，不以任意区间外延拓的全导数冒充。T>0 与原命题一致，并内部供应闭区间 `UniqueDiffOn`，所以两端点的实际内导数唯一且有意义。原 qmax 未成为新前提或常数依赖：`ContDiffOn` 给闭区间连续性，紧性已保证有限上界。

最终对象仍是正坐标盒、任意非空开 W⊆Ω、全部全时空 C∞ 周期 u 及所有时刻 frontier Ω 上逐点零值。空间维数 d+1≥1 包含全部正维数盒；原相对紧包含的观察开集属于该 W 范围。**本批恢复的是原时间权范围，不是原完整状态或几何范围。** 尚未覆盖全部 H¹_tL²_x∩L²_tD(A) 周期轨道及一般凸多面体，故不能据此提升 P024。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，没有改写原文。

## 五项声明逐项核对

下表路径前缀为 `Carleman/`，行号均指 checked_sha。清单及顺序与固定 C172 / T156、`/tmp/carleman-t156-interval-c2-heat-declarations.json` 一致；五项完整展开类型均已逐条读取。

| # | 完整声明 | 固定源码位置 | 独立数学核查结论 |
|---|---|---|---|
| 1 | `Carleman.exists_continuous_periodic_extension` | `Weights/PeriodicPrimitive.lean:13` | PASS。用实际 AddCircle 周期商和 Ico 基本域构造全局连续周期 g；端点相等与周期性单独恢复右端点 T，结论是整个 Icc 上 EqOn，不只开区间或 a.e.。 |
| 2 | `Carleman.periodic_primitive_of_interval` | `Weights/PeriodicPrimitive.lean:29` | PASS。构造 G(t)=F(0)+∫₀ᵗf；真实 FTC 给全部实 t 的 HasDerivAt G (f t)，F 的原闭区间端点匹配推出单周期积分为零，真实周期积分公式给 G 周期且整个 Icc 上等于 F。 |
| 3 | `Carleman.exists_periodic_C2_extension` | `Weights/PeriodicC2Extension.lean:12` | PASS。真实 ddq 连续周期延拓为 R，积分两次得到 P/Q；全局 deriv P=R、deriv Q=P，得到真实 Q C²、T 周期，并在整个闭区间恢复 q、dq 和 ddq，包括两个端点。 |
| 4 | `Carleman.boxTimeIntegral_congr_on` | `Spatial/BoxIntervalC2HeatEstimate.lean:13` | PASS。实际限制乘积测度化为可测柱限制，柱内逐点相等给 a.e. 相等再用 integral_congr_ae；无需对区间外函数作假设。 |
| 5 | `Carleman.box_interval_C2_gaussian_heat_both_signs` | `Spatial/BoxIntervalC2HeatEstimate.lean:23` | PASS。内部构造同一个 Q、供应 C171 的全部实际 qclass 前提，然后把值/梯度/残差/观察四个实际柱积分换回原 q；所有参数仍先于 T/q/ε/u，符号、指数、状态与观察区域不变。 |

## 周期延拓与端点的实际证明

**连续延拓不是假设。** 第 1 项把正 T 注册为实际 `Fact (0<T)`，定义 `g(t)=AddCircle.liftIco T 0 f (t : AddCircle T)`。固定 mathlib 的 `liftIco_zero_continuous` 使用 f 在 Icc 上连续及 f(0)=f(T)，将两个端点粘合到同一个周期商点；再复合真正连续的商映射得到全实线连续 g。周期性来自 `(t+T : AddCircle T)=(t : AddCircle T)`。对 t<T 用 Ico 基本域的原值公式；对 t=T，证明明确使用 g(T)=g(0)=f(0)=f(T)。没有遗漏右端点，也没有假设 f 自身已经周期。

**原函数周期性来自真实零平均。** 第 2 项的输入是原闭区间连续 F、全局连续且 T 周期 f、闭区间内 `HasDerivWithinAt F (f t)` 及 F(0)=F(T)。对任意 0≤t≤T，实际 FTC-2 给 ∫₀ᵗf=F(t)−F(0)。在其所需的 s∈(0,t) 上有 0<s<T，从而 Icc 0 T 是 s 的邻域，源码在此处才将 within 导数转成全导数；没有在端点错误执行这一转换。t=0 的退化积分与 t=T 的右端点均由同一合法 FTC 结论包含。

取 t=T 后得到 ∫₀ᵀf=0，而不是把这个零平均作为额外前提。定义的 G 使用真实有向区间积分，因此负 t 同样有意义。全局连续 f 保证任意有限区间可积、每点连续和所需强可测性；FTC-1 于是给每个实 t 的实际全导数 G′(t)=f(t)。周期积分恒等式 `∫₀^(t+T)f=∫₀ᵗf+∫₀ᵀf` 再给 G(t+T)=G(t)。最终 G(t)=F(t) 在整个 Icc 上逐点成立。这一构造没有借助未证明的周期原函数存在性，也没有遗留周期漂移常数。

**二阶链条是同一函数的真实导数。** 令 dq=`derivWithin q I`，ddq=`derivWithin dq I`，I=[0,T]。由 T>0 得 `uniqueDiffOn_Icc`，再从 q 的 C² within 正则性得到 dq∈C¹(I)、ddq∈C⁰(I)。这使用真实导数的唯一性和固定 mathlib 的 `ContDiffOn.derivWithin` / `continuousOn_derivWithin`，不是把 dq/ddq 当自由字段。

先用 ddq(0)=ddq(T) 将 ddq 连续周期延拓为 R。以 F=dq、f=R 调用第 2 项：实际 within 微分由 dq 的 C¹ 及 R=ddq 在 I 上的身份内部供应；dq(0)=dq(T) 给周期 P，且 P′=R、P=dq 于 I。再以 F=q、f=P 调用同一引理：P 连续由其真实 HasDerivAt 得到，q 的 within 导数通过 P=dq 内部供应；q(0)=q(T) 给周期 Q，且 Q′=P、Q=q 于 I。

源码随后证明两个**全函数等式** `deriv Q=P`、`deriv P=R`，由 R 连续及真实 P 可微取得 P∈C¹，再由真实 Q 可微和 Q′=P 取得 Q∈C²。最终 `Q=q`、`deriv Q=dq`、`deriv (deriv Q)=ddq` 在 I 上全部成立。正则性没有循环依赖，二阶全导数身份不只在内点成立；原函数在 I 外的任意值不参与该证明。

## 原 qclass、四积分与统一常数

最终声明先从已验收 C171 取得 c、λ、β、qc、C，再引入任意 T>0、闭区间 q、ε 和 u。在本次 q 上构造 Q 可能依赖 T/q，但 c/λ/β/qc/C 已经选择完毕。通过完整 Icc 上的三个身份，将原 qc 下界和两个真实 within 导数界分别改写为 Q、全导数 Q′、Q″ 的原界；由已构造的全局 C² 和真实周期性满足 C171 的全部输入。没有给最终常数增加延拓范数、qmax、T 或状态依赖，也没有再缩小 β。继承的是 C171 已经固定的 β（该依赖内部从光滑 β₀ 选择 β₀/9），本阶段原值保留。

对任意参数函数 F，源码仅用 Q(t)=q(t) 于 I，得到 `∫F(Q(t),(t,x))=∫F(q(t),(t,x))`。实际 `boxTimeIntegral` 的测度仍为 `(volume.restrict [0,T]).prod (volume.restrict Ω)`；`Measure.prod_restrict`、可测柱的 `ae_restrict_mem` 和 `integral_congr_ae` 供应真实积分相等。观察项单独按 x∈W 与 x∉W 分支，因此并不要求观察示性函数连续，也没有遗漏观察项。

三个连续参数表达式与观察项实际为：

| 项 | 替换 Q/q 时保留的表达式 |
|---|---|
| 值项 | `r³ exp(rρ(x))² u(t,x)²` |
| 梯度项 | `r exp(rρ(x))² ‖gradient(u(t,·))(x)‖²` |
| 残差项 | `[exp(rρ(x)) spaceTimeOrientedHeat ε u(t,x)]²` |
| 观察项 | `1_{x∈W}` 乘同一个值项 |

这里只将参数 r=Q(t) 换成 r=q(t)；同一 ρ、u、真实空间梯度、实际 ε∂tu−Δu、两时间符号和原 W 均原样保留。目标积分不含 q 的导数，故不需要比较任意区间外全导数。即使原 q 在 I 外很不规则，柱上的 integrands 与合法全局 C² Q 的 integrands a.e. 相等，具有相同真实积分及可积性；不是利用非可积时默认积分值。原 q 在 I 上本身也连续。W⊆Ω 与既有 `boxTimeIntegral_observation` 给真实观察柱积分；时间端点相对 (0,T) 只是 Lebesgue 零测集。

输出仍保留 c∈W、λ≥1、0<β≤1、qc≥1、C>0、−2<ρ≤−1，原指数 (3,1;3) 以及所有 T/q/ε/u 之前的参数顺序。无外给延拓、光滑时间代表、目标估计或额外端点条件。T=0 不被本批延拓定理接受，与原 T>0 一致，且避免闭单点上 within 导数不唯一的问题；一般积分相等辅助声明允许任意 T/盒端点，不改变最终正盒假设。

## 固定依赖、公理与本机证据

三新模块的 Carleman import 闭包共有 **138** 文件，其中 **135** 个旧文件与 mathematical_base 逐字节相同。正式依赖 C171 的 `BoxC2HeatEstimate.lean` 完整 **135 文件闭包**与已验收 proof `069e313b5c03c66aec7c41e72055f95292515e58` 全相同。已读取 [T155 独立报告](T155-local-acceptance.md)，并重新直接核对其完整最终全局 C² 双方向接口、实际四积分及光滑 q 序列极限的使用方式；本批所有调用前提均由原数据或延拓内部供应。

另外直接读取固定 mathlib 的 AddCircle `liftIco_zero_coe_apply` / `liftIco_zero_continuous`、周期积分 `intervalIntegral_add_eq_add`、FTC-1 `integral_hasDerivAt_right`、FTC-2 `integral_eq_sub_of_hasDerivAt_of_le`、`uniqueDiffOn_Icc` 和 C¹/C² 导数刻画，逐项核对上述可测性、连续性、导数及端点前提。Lean 版本固定 4.35.0，实际 CI 编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；固定 manifest、实际干净的 mathlib checkout 和 CI result 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。

三模块均由固定 `Carleman.lean` 导入，五项均有固定 `tools/CheckAxioms.lean` 的 `#check @...` 与 `#print axioms ...`。本机 `/tmp/carleman-t156-interval-c2-estimate-target.log` 记录 **3308 jobs** 成功；`/tmp/carleman-t156-interval-c2-heat-build.log` 记录根目标 **4039 jobs** 成功。实际 `-axioms.log` 是 **0 bytes**，不作为审计 PASS 日志引用；有效公理证据来自完整固定 `-local-axioms.txt` 和独立下载的同 SHA 远端 raw。没有声称重新构建变动中的工作树。

实际 raw 的全部显式打印记录为 2868 条仅含正常基础公理及 9 条无公理记录，没有未知公理。五个新声明各仅依赖 `propext`、`Classical.choice`、`Quot.sound`。固定审计器枚举全部 Carleman 常量（含 privateToUserName），对每个声明执行 collectAxioms 并仅允许这三项；原始末行是 **`Axiom audit passed for all 7621 Carleman declarations.`**。显式输出数不与递归总数混同；本批源码没有 sorry / admit / 新增 axiom 或未清偿占位。

## 独立真实 CI 与下载产物

独立通过 GitHub API 核实 [main run 39242968737 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39242968737/attempts/1) 最终整体 **completed/success**，head 精确为 checked_sha，分支 main。三个实际 job 全部属于同一 proof SHA：

| job | 实际 ID | 最终结论 | completed_at UTC |
|---|---|---|---|
| lean | `118027962650` | completed / success | `2026-10-19T11:15:30Z` |
| state-check | `118027963065` | completed / success | `2026-10-19T11:12:44Z` |
| dashboard / snapshot | `118029154444` | completed / success | `2026-10-19T11:15:42Z` |

本 Agent 实际执行两次 `gh run download 39242968737`，独立下载同次 lean-ci-result 和 lean-declaration-evidence；实际 API 确认二者 run/main/head 一致且未过期：

- result artifact **12181319086**（API 压缩大小 493 bytes）：原始 `/tmp/carleman-t156-interval-c2-heat-main-ci/result.json` 为 **537 bytes**，SHA256 **`e501ec7bcbc151e425a3206a9f5dd1a553c0fdd8bafe437f8e4912a807cf0648`**；实际 `status=PASS`、`checked_sha=source_head_sha=b65d78fa150ea0cc5c0cd7d7b3342e7498b1bc50`、`targets=[Carleman]`、`finished_at=2026-10-19T11:14:31.291714+00:00`，ci_url 为同次 attempt。result 生成后另等三个 job 结束再签发，未把可下载产物等同于最终 job 成功。
- raw artifact **12181354214**（API 压缩大小 220420 bytes）：原始 `/tmp/carleman-t156-interval-c2-heat-main-axioms/axioms.txt` 与固定 `/tmp/carleman-t156-interval-c2-heat-local-axioms.txt` **逐字节完全一致**，均为 **2378103 bytes**，SHA256 **`037637d42768669d66a9355cf5dc870ac3e52ee2bd083d0f0bfbc5358849fd53`**；远端末行同为 7621 声明递归审计通过。

## 签发结论

**5/5 PASS，无阻断本批 AUXILIARY 验收的数学或证据缺陷。** 原闭区间 C²、零至二阶实际内导数端点匹配、真实周期延拓及原 q 的四积分恢复已完成；全部参数仍先于 T/q/ε/u。C172 可登记 REVIEWED / AUXILIARY，但状态仍 C∞、区域仍坐标盒，完整弱轨道与一般凸多面体仍待，因此 P024 不提升、原文保持 17/26。本报告及 reviewed_at 在签发通知后冻结。
