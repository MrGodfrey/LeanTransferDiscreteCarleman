# T263 / C279 独立本机数学验收

- checked_sha / source_sha：`556cdaef8f161664657049e6fc2829b82fbb4404`
- mathematical_base：`49ca9a4344f0e015567fd8916e61a9a768358ba7`
- reviewed_at：`2026-10-20T11:21:48+00:00`
- reviewer：独立 Agent `/root/accept_section3`，未参与实现。
- result：**PASS，18 / 18 显式声明**；axiom_check：**PASS**。
- scope：**AUXILIARY**。C279 可登记 REVIEWED；不提升 P024，原文完成数保持 **20 / 26**。
- evidence_source：**local**。按现行协议核对固定源码和本地执行产物；未查询 CI / 看板，未重复全库构建。

本报告直接核对固定 Git 对象中的三个新模块全部实际类型、证明、完整 raw 类型与公理输出、分析文件、MATH_SPEC 对应段落及原稿。固定根 AGENTS、PROJECT_OPERATIONS、state/README 与此前已读版本不变。下述依赖以实际代码和闭包版本核对，冻结报告用于确认独立验收状态，没有用报告或执行者规格替代数学判断。工作树后续实现及动态 `.ci/axioms.txt` 不属于本次证据。

## 原文对应及完成范围

原 `paper/main.tex:292–299` 的 qclass 是闭区间 C²、零至二阶端点匹配、\(q\ge q_c\ge1\)、\(|q'|\le\beta q^2\)、\(|q''|\le\beta^2q^3\)。原 `prop:continuousCE`（2672–2731）要求在原域的全部弱周期轨道上，对两个时间方向得到指数 \((3,1;3)\)，且常数先于 T。本批准确完成该证明中真实内域积分不等式之后的统一吸收、原梯度返回、时间反射及原 C² 权传递。

令固定外域 \(S=\{x:\forall i,\ b_i<\ell_i x\}\) 有界，W 是任意非空开集且 \(W\subset S\)，令
\[
S_n=\Bigl\{x:\sum_i e^{(n+1)(b_i-\ell_i x)}<\tfrac12\Bigr\}.
\]
最终 `halfspaceSmoothInner_uniform_interval_C2_heat_both_signs` 先选择 \(c\in W,\lambda\ge1,0<\beta\le1,q_c\ge1,C>0\)，再量化所有满足 \(c\in S_n\) 的 n、所有 \(T>0\)、原闭区间 qclass、\(\epsilon=\pm1\) 及全部全时空 C∞、T 周期、对所有时间在真实 \(\partial S_n\) 上为零的 u。对同一 \(\rho=e^{-\lambda|x-c|^2}-2\)、\(\theta=e^{q\rho}\)，实际结论是
\[
\int_{[0,T]\times S_n}q^3\theta^2u^2+
\int_{[0,T]\times S_n}q\theta^2|\nabla_xu|^2
\le C\left(
\int_{[0,T]\times S_n}|\theta(\epsilon\partial_tu-\Delta_xu)|^2+
\int_{[0,T]\times(S_n\cap W)}q^3\theta^2u^2\right).
\]
每项都是实际限制 Lebesgue 乘积测度积分；梯度、时间导数和 Laplacian 是同一 u 的真实微分。没有新定义等于目标估计的抽象能量。空间权全局 C∞ 且 \(-2<\rho\le-1\)，可取原负权阈值 1。

**范围仍有限制。** 状态仍是上述光滑 core，区域仍是实际 \(S_n\)；本批没有完成原弱周期图状态的密度及向原 S 的传递，不能据此宣布 P024 完成。W 无需包含于每个 \(S_n\)，也没有预设所有 n 含 c。唯一索引条件 \(c\in S_n\) 对穷竭的完整尾部成立：既有 `halfspaceSmoothInner_eventually_mem` 由每个严格半空间差为负、实际指数有限和趋于零推出；已直接核对该证明。辅助结论没有收紧原允许观察区，原相对紧包含的观察开集属于其范围。

## 十八项声明逐项核对

名称均在 `Carleman` 命名空间，路径前缀 `Carleman/Spatial/`，行号指 checked_sha。十二个积分工具、四个光滑估计、两个 C² 端点与固定登记、根导入及显式审计项一致，无遗漏。

| 模块 / 行 | 声明 | 实际核查与结论 |
|---|---|---|
| DomainTimeIntegralTools:12 | `domainTimeIntegral_const_mul` | **PASS**。实际 Bochner 积分常数倍身份，没有额外可积性误用。 |
| :17 | `domainTimeIntegral_mono_on` | **PASS**。有界可测空间域上连续函数真实可积，只需实际时间柱内部的序关系。 |
| :30 | `continuous_domain_observation_integrable` | **PASS**。由连续函数的真实柱可积性和可测 `Prod.snd ⁻¹' W` 得示性函数乘积可积，未声称 indicator 连续。 |
| :38 | `domainTimeIntegral_observation` | **PASS**。限制测度与 indicator 积分严格给空间域 \(S\cap W\)，不需要 W⊆S。 |
| :52 | `domainTimeIntegral_mono_on_integrable` | **PASS**。使用两边实际可积性和柱内序关系，合法处理含观察示性函数的吸收式。 |
| :64 | `domainTimeIntegral_add_integrable` | **PASS**。两项实际可积后使用积分可加性，没有以默认非可积积分值拆项。 |
| :71 | `domainTimeIntegral_nonneg_on` | **PASS**。真实限制柱内非负给积分非负；最终应用是实际平方与非负 q 的乘积。 |
| :80 | `domainHeatTimeReflection_measurePreserving` | **PASS**。真实仿射反射 \(t\mapsto T-t\) 保持 Lebesgue 测度，Icc 的精确原像相等，乘空间恒等映射保持实际乘积限制测度。 |
| :86 | `domainTimeIntegral_reflection` | **PASS**。由实际保测可测对合取得积分换元，域 S 与空间坐标不变。 |
| :93 | `domainTimeIntegral_tendsto_parameter` | **PASS**。参数有共同有限上界及逐点收敛；连续 F 在紧参数区间×紧时间区间×空间闭包有界，实际有限测度上的常数支配给 DCT。 |
| :115 | `domainTimeIntegral_observation_tendsto_parameter` | **PASS**。同一支配界加可测观察示性函数，按 W 内外逐点传极限；不要求观察区闭或其 indicator 连续。 |
| :147 | `domainTimeIntegral_congr_on` | **PASS**。实际乘积测度等于可测柱限制，柱内相等给 a.e. 相等再给真实积分相等，包括闭区间端点。 |
| UniformInnerHeat:11 | `halfspaceSmoothInner_uniform_heat_cross` | **PASS**。在固定外域先取误差常数，再量化全部 n；实际内域包含与 T262 曲面积分不等式给真实 heatcross，主势保留原带符号表达式，残差系数为 1/4。 |
| :86 | `halfspaceSmoothInner_uniform_heat_observation` | **PASS**。在外域/W 先取中心、Gaussian 参数、正势/梯度下界及吸收参数；同一余项真实相消，观察项是 \(S_n\cap W\)，无曲率或 n 依赖。 |
| :175 | `halfspaceSmoothInner_uniform_heat_estimate` | **PASS**。从同一 \(z=e^Lu\) 的真实乘积微分返回实际 u 梯度；真实正积分和既定系数供应统一 C，输出原 (3,1;3) 形状。 |
| :285 | `halfspaceSmoothInner_uniform_heat_both_signs` | **PASS**。负方向用真实 q/u 时间反射及保测换元，准确得到 \(-\partial_tu-\Delta u\)，观察项不变，沿用同一全部参数。 |
| UniformInnerC2Heat:11 | `halfspaceSmoothInner_uniform_C2_heat_both_signs` | **PASS**。最终 β=β₀/9 先于 n/T/q/u；真实周期平滑 q 序列供应原光滑预算，四个实际积分分别 DCT 后传同一估计和同一 C。 |
| :84 | `halfspaceSmoothInner_uniform_interval_C2_heat_both_signs` | **PASS**。真实周期 C² 延拓恢复整个 Icc 上 q/一阶/二阶 within 导数，内部供应前项全部前提；四积分精确换回原 q，不假设区间外 q 正则或周期。 |

完整展开类型位于固定 raw 的 45117–45470 行；十八项公理列表逐项核对，包括最后跨行的列表。空间维数参数没有人为限制；所有原正维数包含在内。最终 T>0 与原命题一致，通用积分工具及光滑阶段可允许 T=0，不在闭单点上错误使用 within 导数唯一性。

## 核心数学与统一量词

**实际非盒积分入口。** 已阅读全文核对 `SublevelHeatIdentity` 的 `halfspaceSmoothInner_smooth_heat_carleman_inequality`：同一真实热 bulk 的柱积分不大于实际 \(e^L(\partial_t-\Delta)u\) 的平方积分，系数 1。新代码内部构造光滑周期 Gaussian 相位 L 和实际 Ψ，u 的真实 frontier 零值、c∈Sₙ、λ≥0、q≥0 分别清偿原调用。这里使用 T262 的曲面通量与真实散度极限，不把某个盒上的 CE 套到一般内域。边界步骤没有遗留逐 n 的误差常数或曲率常数。

**外域选择与有符号主项。** `interiorGaussianHeat_bulk_lower_bound` 在固定有界外域选 K，之后才引入 n/T/q/β/u。内域点经实际 `halfspaceExpSum_le_half_mem` 落在外域，故全部点态系数界合法。真实主势系数为
\[
4q^3\lambda^3\phi^3|\nabla\psi|^2(\lambda|\nabla\psi|^2-6).
\]
积分时保留整个带符号项；没有把其可能为负的部分当作非负项丢弃。与上述系数 1 的 bulk 积分比较后除以 4，给真实残差系数 1/4 和 Ccross=K/4。常数 6 与原 heatcross 中独立于 λ 的阈值要求一致，余项允许依赖已固定 λ。

**原观察和吸收。** `exists_interior_heat_observation_coefficients` 从固定 W 内部取 c 和闭球，在固定外域选 λ、Gaussian 正下界 κ、a>0、m>0、Kobs>0，使 \(a\le\lambda\phi\)、\(m\le F+K_{\rm obs}1_W\)，其中 F 是同一真实热势。球外 λ|∇ψ|²≥12 给正势，球内的有界负部由观察项补偿。该逐点结论只需 x∈外域，不要求 W⊆Sₙ。

随后从 m 和 Ccross 选择 \(\beta_0=\min(1,m/(8C_{\rm cross}))\)、\(q_c=\max(1,4C_{\rm cross}/m)\)，内部证明每个 Q≥qc 有
\[
C_{\rm cross}\bigl(Q^2+(\beta_0+\beta_0^2)Q^3\bigr)\le(m/2)Q^3.
\]
乘真实非负 \(z^2\)，加梯度项，并用可积单调积分及实际加法，与 heatcross 的同一余项严格相消。得 \(A_1\int q|\nabla z|^2+A_0\int q^3z^2\le\frac14 R+K_{\rm obs}O\)，其中 \(A_1=a,A_0=m/2>0\)。所有参数在 n/T/q/u 之前；不存在把 qmax、时长、单层薄层宽度或状态界带入最终 C。

**真实梯度返回。** 已读实际 `InteriorHeatGradientReturn`：从同一指数乘积微分给 \(\theta D_i u=D_i z-D_iL\,z\)，完整空间方向平方和精确等于 Euclidean 真实 gradient 范数平方。相位空间能量在固定外域控制为 Jq²，故 H=3+2J 给返回界。令 D=1/A₁+1/A₀，使用 E/V/R/O 的实际非负性并取 C=HD(1+Kobs)，得到本报告显示的最终估计。返回不混入时间梯度，也没有维数范数等价或未清偿的可积性前提。

**两个真实符号。** ε=1 直接使用上述结论。ε=−1 对 q/u 作 \(t\mapsto T-t\)：一阶时间导数变号，二阶 q 导数不变，空间 Laplacian 不变。因此残差是原 \(\epsilon\partial_tu-\Delta u\)，不是误将整个热算子取负。真实周期性及全时间 frontier 零值在反射下保持。四项用真实限制乘积测度换元，空间 W indicator 不变；全部常数原样保留。

**C² 极限及端点。** 直接核对实际 `PeriodicC2Mollification`：归一化周期平滑、实际微分和 9β / 27β² 预算给同一原 q 的光滑序列；新最终参数 β=β₀/9 是先行选择的正常数，27(β₀/9)²≤β₀²。共同有限上界 B 可以依赖固定 q/T，但只用于极限的可积支配，不进入 CE 常数。内域索引 kidx 与平滑索引 n 分离。真实值、梯度、残差三个参数函数连续，第四项仅带可测 indicator；四次 DCT 后用 `le_of_tendsto_of_tendsto` 保留同一 C。未假定光滑 q 序列在导数上收敛来替代所需预算。

最终只输入闭区间 C² 和 0/1/2 阶端点匹配。已读真实 `PeriodicC2Extension`：将连续二阶 within 导数周期延拓，积分两次，用端点相等消除两次原函数周期漂移，得到真正全局 C² 周期 Q。其值和一二阶全导数在整个 Icc 上与原 q 的值/within 导数相等，端点也包括。新代码用这三个身份供应 qclass，再按柱内相等把四项实际积分换回 q。原 qmax 可由紧区间连续性取得，不是被遗漏的额外输入或隐藏常数依赖。

## 依赖版本与独立前置验收

本次三个新模块的完整 Carleman import 闭包为 **286** 个模块，其中 **283** 个旧模块与 mathematical_base 逐 Git blob 不变。特别比较以下实际入口的完整依赖闭包，而不只比较入口文件：

| 实际入口 | 已验收 proof | 闭包模块数 / 结果 |
|---|---|---|
| `SublevelHeatIdentity` | `49ca9a4344f0e015567fd8916e61a9a768358ba7` | 251 / 全不变 |
| `InteriorHeatBulkLowerBound` | `8e740040ffe3ce75cb89b5868d5998b5ad8cd74c` | 108 / 全不变 |
| `InteriorHeatPotential` | `86686ea4d106798727d898bf61abc238812a8cb8` | 94 / 全不变 |
| `InteriorHeatGradientReturn` | 同上 | 93 / 全不变 |
| `HeatTimeReflection` | `7a2da98bcead43801f48dc03ecffbc70adc7585e` | 91 / 全不变 |
| `PeriodicC2Mollification` | `abadce407f55be6c99212cbf92654e8fa44a7c2d` | 86 / 全不变 |
| `PeriodicC2Extension` | `b65d78fa150ea0cc5c0cd7d7b3342e7498b1bc50` | 2 / 全不变 |

已全文读取本批直接前置 T262 冻结报告，commit **`22c822ba948778b913bcd549884bff78d695083b`**，reviewed_at=`2026-10-20T11:17:46+00:00`，17/17 PASS；其 proof 精确等于本批 base。报告文件 12314 bytes，SHA256=`5807c6c4bc052d78f354c7f197534d71310fb6f34d4bf9febc507610567b3d2f`。该报告记录的是其历史 19/26 快照，本批固定登记已包含 T261，故此处保持 20/26，两批均不提升 P024。另重新读取 T152、T156 冻结报告的有关实际证明与边界说明，结合本次实际源码核对吸收和闭区间延拓；既有 T151/T154 验收按上述不变闭包复用。本批没有目标 CE、几何通量结论、W⊆Sₙ 或弱态密度作为隐藏前提。

## 固定本地执行与公理证据

实际读取 `/tmp/carleman-t263-local-evidence.json`：status=`PASS`、source=`local`、checked/source SHA 均为本报告 proof；`lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 均记录 exit 0，finished_at=`2026-10-20T11:15:05.111861+00:00`。以下是独立读取和摘要验证的固定产物；未声称审查者重新执行构建。

| 文件（前缀 `/tmp/carleman-t263`） | 实际核验 |
|---|---|
| `-local-source-manifest.txt` | **1064 条，115480 bytes**；固定 Git 全部 tracked Lean 源及工具链三配置的路径集合完全一致，逐文件内容 SHA256 全匹配；整体 **`e0151e5c7c9813ae9e7019b049aeb8e27647486b85ce573ddc50a626b0658ab1`**。 |
| `-target-build.log` | 三个新模块实际成功，**3491 jobs**；240 bytes；SHA256=`3a41cbda7144356719b72c09bffd8ce407bf2403ff1c418e4ece030ba413304b`。 |
| `-build.log` | 根目标 `Carleman` 成功，**4306 jobs**；80 bytes；SHA256=`aa14ce0166b12aa591883841d8e186ed49f282f800e8e441a256972dceecf989`。 |
| `-axioms.log` | **0 bytes stderr**，不是单独的审计 PASS 依据。 |
| `-uniform-inner-c2-heat-local-axioms.txt` | **3502615 bytes**；SHA256 **`7b675d14a16377e90f2a759dc798ddb0c96a45d1f42a470073d1f35efc5006ee`**；实际末行 **`Axiom audit passed for all 10358 Carleman declarations.`**。 |

raw 全部 **4186** 个有公理显式列表均仅含 `propext`、`Classical.choice`、`Quot.sound`，另 **10** 个声明无需公理。十八个新声明均有完整 `#check` / `#print axioms`，并已实际导入根目标。固定递归审计器使用 `privateToUserName` 覆盖全部 Carleman 常量、对每个常量递归 `collectAxioms`，只允许上述三项；未缩小审计范围，未发现 `sorryAx` 或新增数学公理。显式输出列表数与 10358 个全命名空间递归声明不是同一种计数。

Lean 4.35.0，编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；固定 lock 及本机实际干净 mathlib HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。原稿与前置版本逐字节不变，SHA256=`492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

## 签发决定

**18 / 18 PASS，无修复项。** T263/C279 的内域统一、双方向、原 interval-C² 权、真实观察/残差/梯度四项连接已经清偿，可以按此固定版本登记 REVIEWED / AUXILIARY。原弱周期图状态及向原域的传递仍待后续证明；**P024 不提升，20/26 不变**。仅提交本报告，冻结正文和 reviewed_at，不修改实现、台账、原稿或其他验收报告，不推送。
