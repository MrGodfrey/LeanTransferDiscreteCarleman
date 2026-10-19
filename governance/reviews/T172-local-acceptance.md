# T172 / C188 独立本机验收：真实互补 HUM 与 Cartesian 滤波控制

- checked_sha / source_sha: `113b2c6e318ce5cb48f1fda5696223646e0cd2b1`
- mathematical_base: `f6e35f26cc23e5ca84eb8e869a12864be70e7b27`
- reviewed_at: `2026-10-19T13:47:58+00:00`
- reviewer: 独立本机 Agent `/root/accept_spatial_lemma`，未参与本批数学实现。
- result: **PASS**；axiom_check: **PASS**；全部 **20/20** 显式声明通过。
- scope: **AUXILIARY**；C188 可在本批范围登记 REVIEWED。原文覆盖保持 **17/26**，不将盒 Cartesian 实例自动计作一般几何、P1 或整个原滤波控制命题的 PAPER 完成。

本报告直接读取固定 Git 对象中六模块的全部源码、二十项实际展开类型和证明、原稿及关键依赖，并独立查询同 SHA 的正式 GitHub CI、自行下载 result/raw。执行者说明、旧验收报告及编译通过未代替语义审查。后续 BoxP1LoadCarleman 等工作树和动态 `.ci/axioms.txt` 均排除；仅新增并单独提交本报告，不改实现、台账或原稿，不 push。

## 原文对应及依赖验收门槛

对照固定 `paper/main.tex:2135–2183` 的原 Rayleigh 上确界、Λ_{0}=0、K_F、两个滤波条件及“不要求 F 不变”；`2201–2215` 的 `cor:filtered-control`；`3089–3206` 的 `sec:filter-control-proof` 四步。另核对原 Section 7 的完整 N+1 节点正向/伴随系统及控制范数。原稿 SHA256 仍为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，与基线相同。

读取固定 T172 分析、MATH_SPEC 的 T170–T172 段和 C186–C188 台账。AGENTS、PROJECT_OPERATIONS、MILESTONES、state/README 的内容哈希与此前已读协议相同。最终范围是任意固定正维坐标盒、非空开 W⊆盒、开 ω 且 closure W⊆ω、固定步长可比界 ratio；不是把一般原命题的几何范围静默缩小。

签发前完整读取 [T170 正式报告](T170-local-acceptance.md)（提交 `da95f786af0ae582fcc4fa9ba22d0bd4b1f84b4c`，checked=`3a752bc986ef1a893825b6597211ccb519d8a292`，reviewed_at=`2026-10-19T13:36:55+00:00`，3/3 PASS），以及 [T171 正式报告](T171-local-acceptance.md)（提交 `f102d1571bad357dedf292a90d4ccc6b832db369`，checked=`f6e35f26cc23e5ca84eb8e869a12864be70e7b27`，reviewed_at=`2026-10-19T13:44:33+00:00`，3/3 PASS）。固定 T172 台账中的 C187 尚为 BUILT/PENDING；本次用该明确版本的冻结报告补齐验收门槛，没有将旧状态误读为已审查，也未修改总账。实际源码及完整依赖闭包另行核对如下。

## 二十项声明逐项核对

顺序与固定 C188/T172 及 `/tmp/carleman-t172-cartesian-filtered-control-declarations.json` 一致；源码位置相对于 `Carleman/Control/`，raw 行指完整类型起始行。

| # | 完整声明 | 固定源码位置；raw 行 | 独立结论 |
|---|---|---|---|
| 1 | `Carleman.Physical.complementaryHumOperator` | `ComplementaryHUM.lean:13`；33247 | PASS。实际 CLM 为 O*O+η²P(F⊥)，使用原 Hilbert adjoint 和正交投影。 |
| 2 | `Carleman.Physical.complementaryHumOperator_pairing` | 同文件:16；33255 | PASS。投影幂等与自伴给精确双线性配对，惩罚为 η²⟨Qx,Qy⟩。 |
| 3 | `Carleman.Physical.complementaryHumOperator_bijective` | 同文件:26；33261 | PASS。实际互补观测加 R 单射给零核，有限维性给满射；不假设 F 不变。 |
| 4 | `Carleman.Physical.complementary_hum_optimality` | 同文件:43；33269 | PASS。对任意 y 解真实 H z=R*y，得到对所有 v 的唯一 Euler 解。 |
| 5 | `Carleman.Physical.complementary_hum_control` | 同文件:62；33278 | PASS。构造 −Oz，精确残差 η²Qz 给 F 投影为零及完整残差界；零能量不除法。 |
| 6 | `Carleman.Physical.complementaryPenalty` | `ComplementaryObservation.lean:9`；33292 | PASS。实际 η=ε√(1+2L²K²)。 |
| 7 | `Carleman.Physical.complementaryPenalty_sq` | 同文件:11；33294 | PASS。根号内非负，精确平方身份无额外符号条件。 |
| 8 | `Carleman.Physical.complementaryPenalty_pos` | 同文件:15；33297 | PASS。ε>0 给 η>0，覆盖实际正指数 ε。 |
| 9 | `Carleman.Physical.complementary_terminal_bound` | 同文件:21；33299 | PASS。真实正交分解与仅 F 上的反向界给原 2K²、1+2L²K² 系数。 |
| 10 | `Carleman.Physical.complementary_observation_of_relaxed` | 同文件:45；33307 | PASS。明确 hobs 前提与 4C0ε²K²≤1 预算吸收，得到全空间互补观察、常数 2C0。 |
| 11 | `Carleman.Physical.physical_complementary_hum_control` | `PhysicalComplementaryHUM.lean:13`；33321 | PASS。实际流、sqrt(dt) 控制向量和对偶身份构造全部物理节点 Forward 解及精确初终态性质。 |
| 12 | `Carleman.Physical.filtered_control_of_relaxed` | `FilteredControl.lean:14`；33346 | PASS。由原反向界和两条件内部得到互补观察，实际输出完整 ForwardEquation 和成本/投影/终态界；hobs 明示。 |
| 13 | `Carleman.Physical.filterTerminalFactor` | `FilterPenaltyBound.lean:9`；33382 | PASS。额外因子只含 T、M，无网格或 F 数据。 |
| 14 | `Carleman.Physical.filterTerminalFactor_nonneg` | 同文件:12；33384 | PASS。真实根号与指数的非负性。 |
| 15 | `Carleman.Physical.filter_terminal_constant_budget` | 同文件:15；33386 | PASS。C0≥0、2factor²≤C0 精确推出 √(2C0)factor≤C0。 |
| 16 | `Carleman.Physical.filterRayleigh_nonneg` | 同文件:25；33391 | PASS。A 非负给真实 Rayleigh 上确界非负，F=⊥ 单独用定义零值清偿。 |
| 17 | `Carleman.Physical.filterConstant_ge_one` | 同文件:33；33395 | PASS。T、M、Λ 非负给原 K=exp(TΛ+MT+M²T²/2)≥1。 |
| 18 | `Carleman.Physical.complementaryPenalty_le` | 同文件:38；33398 | PASS。K≥1 以平方比较给 η≤ε√(1+2L²)K；无除以 K−1。 |
| 19 | `Carleman.Physical.filter_penalty_decay` | 同文件:47；33401 | PASS。原 TΛ≤θdS 精确给 exp(−(1−θ)dS) 衰减，剩余因子仅 T/M。 |
| 20 | `Carleman.Physical.box_cartesian_filtered_control` | `BoxCartesianFilteredControl.lean:15`；33410 | PASS。真实盒观测内部供应，原完整控制与正向轨道、同一统一 C0 和原两滤波条件、原尺度及指数终态结论成立。 |

## 正交互补观察与真实 HUM 算子

令 P=F.starProjection、Q=F⊥.starProjection。X 有限维保证所有子空间闭且正交投影实际存在；mathlib 使用的是映回 X 的真实连续线性正交投影。代码通过投影幂等和内积自伴身份得到 `⟨(O*O+η²Q)x,y⟩=⟨Ox,Oy⟩+η²⟨Qx,Qy⟩`，所以惩罚确为互补终端分量，未把它替换成全空间 η²I。

第 3 项若 Hx=0，则与 x 配对使观察和惩罚的整个平方和为零；明确的互补观察给 ‖Rx‖²≤0，故 Rx=0。R 单射随即给 x=0；有限维线性自映射从单射得到满射。此步不凭空假定目标算子可逆，也不从有限维性抽取可能依赖维数的统一估计常数。

第 4 项实际取 H 的原像来解 Hẑ=R*y，再通过所有 v 的内积身份给唯一 Euler 解。声明形式是唯一 Euler 方程解，没有另定义一个泛函并宣称已形式化通用极小值定理；这个直接线性构造足以实现原证明 Step 2 和后续控制。其二次型非负且零核，亦与原严格凸二次泛函的最优性身份一致。

第 5 项以 Qenergy=‖Oẑ‖²+ε²‖Qẑ‖²，实际 Euler 配对给 Qenergy=⟨y,Rẑ⟩。Cauchy–Schwarz 和互补观察给 Qenergy²≤C‖y‖²Qenergy，代码以非负性和反证推出 Qenergy≤C‖y‖²；Qenergy=0、y=0 均无除零。取 v=−Oẑ，实际 adjoint 内积身份对全部测试向量证明

`R*y+O*v = ε² Qẑ`。

因此 P(R*y+O*v)=0 精确成立，且 ‖v‖≤√C‖y‖、‖R*y+O*v‖≤ε√C‖y‖。符号为负控制，终态残差为正 ε²Qẑ；没有把终态投影后的范数冒充完整终态范数。

第 9 项用 z=Pz+Qz、Pythagoras 和 `R(Pz)=Rz−R(Qz)`。仅对 Pz∈F 使用反向界，再以 ‖R(Qz)‖≤L‖Qz‖ 得到 `‖Pz‖≤K(‖Rz‖+L‖Qz‖)`。平方后以真实交叉项界得到原 `‖z‖²≤2K²‖Rz‖²+(1+2L²K²)‖Qz‖²`。没有假设 RQz∈F⊥、RPz∈F、R 与投影交换，或任何算子/时间势保持 F。

第 10 项将该式代入明确保留的松弛观察，预算使左侧回流系数 `2C0ε²K²≤1/2`；得到 `‖Rz‖²≤2C0(‖Oz‖²+η²‖Qz‖²)`。η 的定义、平方及正性与原稿一致，全部完整 z 均被覆盖。不能把这个通用条件引理单独视为已证明原观测；完整盒入口确实另行供应它。

## 真实物理流、控制与全部正向方程

重新读取 `PhysicalFlow`、`PhysicalHUM`、`PhysicalSolutions`、`PhysicalEquations` 和 `PhysicalDuality`。R=initialMap 是从真实终态 z 沿实际逆步算子递推得到的 p[z]⁰；每步 `I+dt·L_i` 在原下界和 dt M≤1/2 下可逆，逆向有限迭代保证 R 单射。O=observationMap 的第 i 项为 `sqrt(dt)·B* p[z]ᶦ`，值域是实际 `PiLp 2`，不是未加时间质量的函数 sup 范数。

真实身份 `‖Oz‖²=dt Σᵢ‖B*p[z]ᶦ‖²`、`controlVector dt u=(sqrt(dt)uᵢ)ᵢ` 及 `‖controlVector dt u‖=controlNorm dt u` 已逐项核对。构造抽象控制 v 后取 uᵢ=(sqrt(dt))⁻¹vᵢ，dt>0 给严格非零除数，实际 `controlVector_unscale` 证明恰还原 v。因此最终控制就是原物理时间质量下的控制；若代入 v=−Oẑ，得到原 uⁿ=−B*p[ẑ]ⁿ⁻¹。

真实 `existsUnique_forward` 由逐步逆算子构造所有 N+1 节点 y，同时给 y⁰=y0。第 11 项输出的是乘过 dt 的原 `Forward`；其 dt>0 及已读 `forward_equation_iff` 使它与原差商方程等价。第 12、20 项实际类型直接输出 `ForwardEquation`：

`dt⁻¹(yᵢ₊₁−yᵢ)+(A+Vᵢ)yᵢ₊₁=B uᵢ`，对每个 i=0,…,N−1。

伴随使用实际 Hilbert adjoint `(A+Vᵢ).adjoint`，在已证对称性下等价于真实步递推。`control_duality` 的时间配对严格使用 pᶦ（论文 pⁿ⁻¹），不是 pᶦ₊₁。由该完整非周期对偶恒等式得到 `yᴺ=R*y0+O*v`，与 HUM 残差身份连接。输出包含完整原初态、全部正向方程、原控制范数、P_F yᴺ=0 和完整 ‖yᴺ‖ 界，没有只输出一个抽象终端向量，亦没有把原方程限制在 F 上。

`filtered_control_of_relaxed` 内部以 A 非负和 ‖Vᵢ‖≤M 证明真实 −M 下界，对称性由 A 与每个 Vᵢ 相加得到。R 的真实界为 L=exp(2MT)，K=exp(TΛ_F+MT+M²T²/2) 来自 `filter_reverse`，只将反向界应用于终态在 F 的轨道；其余状态在原全空间。原两条件经 `filter_condition_budget` 给 4C0 exp(−2dS)K²≤1，再供互补观察与 HUM，成本为 √(2C0)‖y0‖。

## Rayleigh、指数率和同一统一常数

`filterRayleigh A F` 对 F=⊥ 明确等于零，否则为非零 F 元素的真实商 ⟨Ax,x⟩/‖x‖² 的上确界。‖A‖ 仅用于证明集合有上界，不进入最终常数。第 16 项在 F≠⊥ 时取真实非零元素，利用 A 非负及其商≤上确界证明 Λ_F≥0；F=⊥ 分支不假设存在非零向量。因此 K≥1、惩罚放大和最终控制均包含 F=⊥。

惩罚比较先利用 K≥1 得 `η≤ε√(1+2L²)K`。取 ε=exp(−dS)、L=exp(2MT)，原 TΛ_F≤θdS 得

`η≤factor(T,M) exp(−(1−θ)dS)`，其中 `factor(T,M)=√(1+2exp(2MT)²) exp(MT+M²T²/2)`。

这一步没有把 F 的 K_F 留在统一终态前因子中，也没有增加网格相关常数；指数中 (1−θ)、d、S 的乘积和原值保持。第 15 项用非负平方比较严格证明：C0≥0、2factor²≤C0 时，`√(2C0)factor≤C0`。

完整盒入口先从 T170 取得真正网格统一的松弛观察常数 C(T,M)>0，然后选择

`C0=max(1,max(C(T,M),2factor(T,M)²))`。

整个观察右侧非负，故同一真实观察可将常数 C 单调放大到 C0；证明中实际构造了这个全轨道观察 ho。两个滤波条件使用的就是这个 C0，控制成本是 √(2C0)，终态界是 `C0 exp(−(1−θ)d0 Smax)‖y0‖`。不存在先用较小 C 的滤波预算、再在结论中偷偷放大到另一个 C0 的步骤。原文 C(T,M) 是可一次放大的存在常数；这里在选择任何网格或 F 前固定放大后的观察常数，使 C0=max(1,C(T,M)) 的原组织方式与终态前因子兼容。此结论不声称对任意调用者预先指定且更小的 C0 仍有相同终态前因子。

第 20 项量词次序为：固定维数、盒、W、ω、ratio；选择 qc、κ、h₀、Δ₀、Cb、d0；再给任意 T>0、M≥0，选择 C0；之后才量化所有 o、δ、N、h、g、节点势 b、θ、F、y0。故基础阈值先于 T/M，C0 可以依赖 T/M 但先于所有网格、势的具体值、θ 和 F。整个状态空间是原全部内部节点值配质量内积，控制是 ω 内节点同质量空间，B 为原零延拓；实际差分 Laplacian 和实节点乘子自伴/非负或同一 M 范数界均内部供应。

原 `Smax=κ min(h^(−4/5),dt^(−2/5))`、qb=Cb(qc+T⁻¹+M^(2/3))、16qb≤Smax≤qbT/(4dt)、dt M≤1/2、dt≤min(Δ₀,T/12) 以及原步长可比条件都原样保留。最终只有原两个滤波条件，没有额外 F 不变性、CE、观察界、频率投影方程或状态正规性假设。θ 在 Lean 中量化任意实数并保留预算，因此完整包含原 0<θ<1；F=⊥、y0=0 均未排除。

## 固定闭包、公理和构建证据

六模块递归 Carleman 导入闭包共 **768** 文件；除六新模块外 **762** 个旧文件与 mathematical_base 逐字节相同。以下关键入口的整个相关闭包又与已接受证明版本比较，均未变化；实际调用已重新读取，不只依赖旧报告。

| 依赖 | 接受版本 | 比较入口；闭包文件数 |
|---|---|---|
| C186 / [T170](T170-local-acceptance.md) | `3a752bc986ef1a893825b6597211ccb519d8a292` | `Control/BoxCartesianObservation`；756 |
| C187 / [T171](T171-local-acceptance.md) | `f6e35f26cc23e5ca84eb8e869a12864be70e7b27` | `Control/BoxCartesianFilteredObservation`；762 |
| C042 / [T026](T026-local-acceptance.md) | `549cde718bcf26f00b24f4a1493ee92b839f30b4` | `Control/PhysicalHUM`；10 |
| C041 / [T025](T025-local-acceptance.md) | `12d18c9c6548cc70165ad9e4c01314f4438dc5f1` | `Control/FilterReverse`；11 |
| C040 / [T024](T024-local-acceptance.md) | `1aa9b1f253dd759ccc18d92d151aa7c81646f51c` | `Control/PhysicalEquations`；6 |

固定根导入包含全部六模块，二十个声明均有实际 `#check @...` 或无参数版本 `#check ...` 以及 `#print axioms`。新源码无 sorry、admit、新 axiom 或 native_decide。实际检查器以 privateToUserName 覆盖全部 Carleman 常量，并对每项递归 collectAxioms，仅准许 propext、Classical.choice、Quot.sound。

固定 raw 中 **3082** 条有公理打印记录和 **9** 条无公理记录均正常；二十个新增声明各自仅依赖上述三项标准基础公理。末行明确为 `Axiom audit passed for all 8135 Carleman declarations.`，显式打印数不与递归总数混同。全部实际类型及隐藏实例前提均已读取，未发现额外目标估计或状态缩减。

实际定向日志 `/tmp/carleman-t173-box-filter-control-target.log` 的目标为 `Carleman.Control.BoxCartesianFilteredControl`，完成 **3998 jobs**；文件名保留早期草稿编号，不当作另一批证明。固定 `/tmp/carleman-t172-cartesian-filtered-control-build.log` 完成根目标 **4105 jobs**。同前缀 `-axioms.log` 是零字节 stderr，未以空日志代替审计结论。Lean pin 为 4.35.0、CI 编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib pin 与本机实际干净 HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。工具链、manifest、两份 CI workflow 和 tools/lean_ci.sh 均与基线相同。

## 独立同 SHA CI 与原始工件

本 Agent 自行查询 [run 39262538619 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39262538619/attempts/1)，确认 main / push、精确 head SHA。最终实际状态为 `completed / success`，updated_at=`2026-10-19T13:47:12Z`。曾观察到 lean 尚在收尾；随后实际查询全部三项终态成功，未以已可下载工件替代最终 CI 状态。

| job | 实际 ID | 最终状态及 completed_at |
|---|---|---|
| lean | `118093665904` | completed / success；`2026-10-19T13:47:00Z` |
| state-check | `118093666096` | completed / success；`2026-10-19T13:43:24Z` |
| dashboard / snapshot | `118095581546` | completed / success；`2026-10-19T13:47:11Z` |

本 Agent 自行以两次 `gh run download` 下载同 run 原始工件，均退出 0；未用 root 下载副本代替独立取证。两份工件 API 元数据未过期，其 workflow_run.id、main 分支和 head_sha 均精确绑定本次证明版本。

| 工件 | artifact ID；归档字节数 | 独立下载路径 |
|---|---|---|
| lean-ci-result | `12191662672`；493 | `/tmp/carleman-t172-cartesian-filtered-control-main-ci/result.json` |
| lean-declaration-evidence | `12191567836`；237014 | `/tmp/carleman-t172-cartesian-filtered-control-main-axioms/axioms.txt` |

实际 result.json 为 **537 bytes**，SHA256 `d8487f5c66350b3155c3ab94b8a7b82b444b5fc2b62df4b01799c1e7c2794220`。内容为 status=PASS、checked_sha=source_head_sha=`113b2c6e318ce5cb48f1fda5696223646e0cd2b1`、targets=[Carleman]、finished_at=`2026-10-19T13:45:49.317714+00:00`；ci_url 指向同一 run/attempt，Lean/mathlib 与固定 pin 一致。

独立下载的 raw 与 `/tmp/carleman-t172-cartesian-filtered-control-local-axioms.txt` 实际 **逐字节比较完全相同**，各 **2562137 bytes**，SHA256 均为 **`76e24372f62d67b3ac0cd66e5afd4501cd9b07913ec58f0939fad41d1080109f`**。实际完整类型、逐项公理和全部 8135 声明递归审计 PASS 一致；归档大小和解压后的 raw 大小分别记录。

## 签发

**20/20 PASS，未发现阻断缺陷。** 真实互补算子可逆性、唯一 Euler 解、正交互补观察、原物理 R/O 与时间质量、完整 ForwardEquation/初态/终态、F=⊥、无 F 不变性、原两滤波条件及统一 C0 均通过。C188 可登记 AUXILIARY/REVIEWED；本批给出完整盒 Cartesian 滤波控制实例，不自动完成 P1、一般几何或整条 PAPER 覆盖，保持 17/26。仅单文件提交本报告，不 push；通知后正文与 reviewed_at 冻结。
