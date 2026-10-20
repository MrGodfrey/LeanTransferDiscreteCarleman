# T268 / C284：原 Theorem 7.2、7.3 独立整体验收

- checked_sha / source_sha：`5458c11848a69d56199fb5e13d517b58eb38953b`
- mathematical_base：`0a1808091e23386fc8c06d4e2a3434d1fa9f2a34`
- reviewed_at：`2026-10-20T12:26:45+00:00`
- reviewer：独立数学验收 Agent `/root/accept_spatial_lemma`
- result / axiom_check：**PASS / PASS**；两项新增声明与两项既有 Cartesian 声明共 **4/4 PASS**。
- scope：**PAPER P014 / Theorem 7.2（prop:physicalO）及 P015 / Theorem 7.3（prop:physicalC）**。C284 可登记 REVIEWED，两项原命题可登记完成；不由本报告自动修改台账或提升其他命题。
- evidence_source：**local**。遵循现行简化协议，核对精确提交的实际本地构建、公理审计、源码清单及数学，不等待、查询或声称本批远端 CI 成功。

## 固定对象与原命题范围

直接读取固定 Git 对象中的两个新增模块、两个既有物理入口、完整 raw 类型、关键实际依赖，以及 T268 分析、MATH_SPEC、原稿相关段落。AGENTS、PROJECT_OPERATIONS、state/README 与此前已读版本哈希相同，沿用其固定版本规则。当前 T269 工作树、动态 `.ci`、执行者说明及台账状态没有替代数学审查。

原稿核对包括 Section 6 的原 P1/FD 空间、质量、刚度、载荷和控制定义，Section 7 的原势算子与 N+1 节点物理方程（约 1715–1753 行），Theorem 7.2 与三步证明（1827 行起）、Theorem 7.3 与真实 HUM 证明（2032 行起）。`paper/main.tex` 与基线逐字节不变，SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

原 P1 范围是 d=2,3 的有界凸多面体、完整一致 P1 空间及固定形状正则/局部分级界。新定理允许任意非空有界有限严格仿射半空间交，维数写成 `d+1 ≤ 3`，覆盖原两维并额外允许一维。非空由实际开观测区包含于域内部供应。原紧包含的非空开观测区满足这里较弱的开性和包含条件，没有添加边界正则、光滑状态、数值估计或原域 CE 前提。

原 FD 分支是任意正维坐标盒上的标准 Cartesian 网格，轴向步长互相可比。既有两个入口覆盖该完整范围，允许盒的平移，并以真实盒相等固定同一域。其 W 为原 Section 6 选定的非空开内观测区，`closure W ⊆ ω` 正是既有观测设置。这里不把未命名的伸缩张量网格推广 remark 另计为已完成定理，也不把 P1 分支的维数限制施加到 FD 分支。

## 全部四项声明

下表名字均在 `Carleman.Physical` 命名空间；源码位置为固定 `Carleman/Control/` 内的实际行号，raw 行来自本批完整公理产物。固定 C284/T268 声明列表与此四项完全一致。

| 声明 | 固定源码 / raw 起始行 | 独立结论 |
| --- | --- | --- |
| `finite_halfspace_p1_physical_load_carleman` | `FiniteHalfspaceP1LoadCarleman.lean:20` / 46166 | 从真实原域连续 CE、原 H² 正则性和完整 P1 N1–N5 内部构造载荷 CE；所有周期离散状态/载荷、原 h 与 dt 尺度，统一常数先于网格/时间权/状态。PASS。 |
| `finite_halfspace_p1_physical_observation_control` | `FiniteHalfspaceP1PhysicalControl.lean:17` / 46214 | 同一真实 Galerkin 算子、任意有界实势、真实 L²(ω) 控制上给出原全状态观测及全部初态的物理控制；原量词、条件及指数余项不变。PASS。 |
| `box_cartesian_physical_observability` | `BoxCartesianObservation.lean:17` / 32948 | 原质量加权节点 Hilbert 空间、标准 FD Laplacian 和实际 B* 的完整盒观测；没有另加 CE 或数值接口输入。PASS。 |
| `box_cartesian_physical_control` | `BoxCartesianControl.lean:15` / 33030 | 对原全部初态构造真实节点控制和整个 N+1 正向轨迹，实际方程、时间控制范数及指数终态均正确。PASS。 |

四项完整展开类型均已逐项读取；不是只检查名字、外层 `∃` 或执行者给出的结论摘要。

## P1 载荷接口确由原假设供应

`finite_halfspace_heat_continuous_data` 提供同一实际 Dirichlet 模型、Gaussian-minus-two 相位以及原 IntervalQClass 下的完整弱周期热估计，常数先于网格、T、时间权和状态。原域 H² 包含与正图估计分别调用实际 `finite_halfspace_dirichlet_domain_le_h2`、`finite_halfspace_dirichlet_graph_estimate`；内点取自所选 c∈ω。实际有限半空间 Lipschitz 域资格、相位的 SmoothOnClosure/C² 资格均在证明内部供应。最终类型没有留下 hD、hreg、抽象 A4 或光滑域替代原域的假设。

`dirichlet_allowed_family_uniform` 对同一相位和原算子给出实际允许权族。`full_p1_numericalData` 的应用保持完整
`X = M.conformingSpace (dirichletSubspace S)`，其值是原 L² 等价类；不是只取节点产生的较小状态子空间。FaceMatching、BoundaryFitted、实际内球、diameter、ℓ 与直径双向可比及所有共享顶点单元的分级条件，都是原一致形状正则网格及原 grading 的编码。`p1GradingLimit D = (sqrt(D+2)+1)/(sqrt(D+2)-1)` 与原阈值相同；反向邻居界由交换两个索引得到。

直接检查实际 `GalerkinStiffness`、`GalerkinNumericalData`、`ConformingRegionWeightedData` 和所调用的 full-P1 接口：质量是 L² 一致质量，R 为真实包含，J 为 L² 正交投影，G=id 是证明结论，刚度由真实能量形式定义且配对等于原梯度积分，刚度缺陷确为零。N3 已证的加权逼近以及 N4 的同一投影测试 Π_h(σ²z) 及实际时间导数从内部接口取得；不是把最终误差或测试估计当作调用者输入。误差为 `aE=Capp*h, a₀=Capp*h², ηA=0`；重构/载荷/观察常数为一。

本批传递取 τStar=2，证明中明确核对热指数所需 `max(dStar/2,bStar/2)=2`。底层 full-P1 定理仍对任意给定 τStar 供应全部允许幂和两个符号；这里选足以供热传递的子范围，不扩大允许族或漏掉传递所需权。原 Section 6 可先取 τStar=4 的设置并未成为本批新的限制。

实际 `GalerkinHeatData.toConforming` 重建的也是同一包含、投影、刚度、零缺陷与允许权族。其连续字段对全部原 PeriodicWeakTrajectory、两方向成立。`conforming_heat_load_uniform` 的应用使用已证完整传递和原热指数，不是假设所需的离散载荷不等式。

取 `κ=min(κtransfer,εnum)`，h≤h0≤1 且 qmax≥1。由原 `qmax≤κ*h^(-4/5)` 经真实尺度引理得到 `h*qmax≤κ≤εnum`；因此数值阈值内部成立。没有另外添加 h/dt 耦合。最终范围准确为

`qmax ≤ κ * min(h^(-4/5), dt^(-2/5))`，其中 h 是实际 `M.maxDiameter`。

`PhysicalLoadCarleman` 展开后量化所有 z、f，假设仅为真实周期 `D_- z + A_h z = Γf`，结论是原 q³ 加权状态平方和受实际载荷及实际观察平方和控制。P1 的 R 是包含，Γ 是正交投影；不存在任意线性载荷假设或预设目标 CE。

## 原势、真实 L²(ω) 控制及空间配对

P1 势为 `conformingPotential X b = Π_X ∘ b.map ∘ inclusion`。`BoundedMultiplier` 仅要求实际函数 a.e. 强可测和 a.e. 绝对值≤给定非负 bound，故覆盖原所有实 L∞ 势，没有连续代表或点值额外要求。逐步 bound≤M 直接供给同一 M 的算子范数界和自伴性；实际配对恰为 `∫_S b(x) y(x) z(x)`，投影没有被误与一般乘子交换。

`conformingRegionControl` 的控制空间是真正 `Lp ℝ 2 ((volume.restrict S).restrict ω)`，由 ω⊆S 与可测性即原 L²(ω)。B 是零延拓后投影，实际 Hilbert 伴随等于区域限制；区域零延拓为等距、投影为收缩，故 B 范数≤1。加权区域范数真实等于 `∫_ω |σ|² |v|²`，不是把环境 L² 观察冒充控制范数。

载荷 CE 和一般物理观察引理先用环境 cutoff 伴随；`conforming_region_observation_norm` 与实际区域伴随身份把两者范数精确识别。最终 `PhysicalObservationControl` 使用的是 `conformingRegionControl X ω` 本身，控制属于真正区域空间。没有把区域控制限制为有限维状态投影的一个未说明子空间。

## Cartesian 原实现同时覆盖

重新读取 `BoxCartesianHeatEstimate`、`BoxCartesianLoadCarleman`、实际物理空间、刚度及控制等距证明。其连续输入由原完整盒 CE 内部提供，H² 和允许权族由盒原解析实例内部供应，数值输入由 `cartesian_numericalData_on` 内部构造。最终两个物理入口不留这些前提。

完整状态空间是所有内部格点的数据，真实范数平方为 `(∏δ_j) Σ_a |z_a|²`。`cartesianPhysicalLaplacian` 的值公式恰是原 `(2d+1)` 点负 Laplacian，边界数据实际零延拓；离散分部求和与 Kuhn 梯度积分给其原刚度身份、对称和非负性。这里只用实际物理范数，未插入网格依赖的有限维范数等价常数。

计数 L² 载荷表示通过真实 `cartesianCountLpEquiv`，其值带 `sqrt(∏δ_j)`。R=I=该等距、Γ=其逆，所以质量和载荷比较都为一；不同类型上的同构没有被误作未证明的字面恒等。相位是 Gaussian 的实际节点值，bound=2、负性≤−1。`physical_observation_uniform_profiles` 先固定相位 bound 后再量化所有网格计数空间/相位，因此物理常数不含节点数。

实际控制索引是位于 ω 的内部格点，B 为真实零延拓，B* 为限制，`B*B=id` 和原质量配对给保范数。一般引理中的计数观察 `E B B*` 因这些身份恰有原控制范数 `‖B*p‖`。势是任意实节点乘子 `|b_i(a)|≤M`，实际自伴和算子界≤M；没有滤波、频率子空间或不变性条件。

## 原量词、完整时间方程及 HUM

两分支的固定域、观测区及原网格形状/分级/步长可比界在最前。随后选择 `qc,κ,h0,Δ0,Cb,d0`，全部在 T、M 之前；对每个 T>0、M≥0 再选 C(T,M)>0，且在网格、时间步、所有势的具体值、初态与轨迹之前。常数不会因具体网格、状态或 qmax 改变。

两分支准确使用

- `qb = Cb*(qc + T⁻¹ + M^(2/3))`；
- `Smax = κ*min(h^(-4/5),dt^(-2/5))`；
- h≤h0，dt≤Δ0，dt≤T/12，dt*M≤1/2；
- `16*qb ≤ Smax ≤ qb*T/(4*dt)`，g.period=T。

这些就是原 physicalconditions。TimeGrid 的正步长和真实 period/steps 关系保持；dt≤T/12 特别排除不合法的小节点数。M=0 包含在实幂非负分支中，没有除以 M 或 M>0 的附加假设。

实际物理参数选择引理内部构造 `q(t)=qb/sqrt(sin²(πt/T)+δ²)`、δ=qb/Smax，给原 PhysicalQClass；其到 IntervalQClass 的转换包含真实一二阶导数及端点身份。原 `qb³≥Cb³ M²` 内部给势吸收，真实 cutoff/过渡余项、初值恢复及统一相位常数给 exp 余项。仅证明中的 cutoff 轨迹周期化，最终任意 p 没有周期要求。

展开 `PhysicalObservationControl`、`PhysicalEquations` 与两个 Cartesian 入口：i=0,…,N−1 对应原 n=i+1，正向为

`dt⁻¹*(y(i+1)-y(i)) + (A_h+V_i)y(i+1) = B u_i`，

伴随为

`dt⁻¹*(p(i)-p(i+1)) + (A_h+V_i).adjoint p(i) = 0`。

观察量为 `dt*Σ_i ‖B*(p i.castSucc)‖²`，左侧是真实 p(0)，终端为 p(N)。最终输出
`‖p(0)‖² ≤ C*(dt Σ‖B*p(i)‖² + exp(-2*d0*Smax)‖p(N)‖²)`，覆盖任意整个 N+1 节点轨迹满足原方程；没有改用后层节点观察或对伴随测试施加额外端点条件。

控制部分重新检查 `RelaxedControl`、`PhysicalHUM`、`PenalizedHUM` 的实际调用。原自伴下界和 dt*M≤1/2 给每步可逆及真实全轨迹适定性；HUM 使用真实 `O*O+ε²Id`，ε=exp(−d0*Smax)>0，内积非负性给单射，有限维状态空间给满射。控制空间允许无限维完整 L²(ω)。最优性方程与原离散对偶恒等式把实际终态识别为 ε² 倍终端伴随，控制向量用 sqrt(dt) 缩放后还原真实 `controlNorm = sqrt(dt Σ‖u_i‖²)`。

对每个原 y0，输出实际 u 和整个 y，明确 y(0)=y0、ForwardEquation、控制范数≤sqrt(C)*‖y0‖、终态≤sqrt(C)*exp(−d0*Smax)*‖y0‖。sqrt(C)>0 只是原 Theorem 7.3 的 generic C(T,M) 的具体选择，统一性相同，且 d0 正是同一观测定理的 d0。没有仅给抽象终端向量，亦没有预设可控性或非原初态子空间。

## 依赖版本与固定本地证据

四入口的实际 Carleman 导入闭包共 **863** 模块：两个新增模块，**861** 旧模块逐 Git blob 与数学基线相同。又单独核对：

- `FiniteHalfspaceHeatContinuous` 的 **450** 模块闭包全部与 T267 proof `0a1808091e23386fc8c06d4e2a3434d1fa9f2a34` 相同；
- 两个 Cartesian 物理入口的 **757** 模块闭包全部与 T170 接受版本 `3a752bc986ef1a893825b6597211ccb519d8a292` 相同。

已全文读取 [T267 冻结报告](T267-local-acceptance.md)，独立校验报告提交 `f9c4dc5fb4770e0075bc857beae0900dc01c5edc` 中的 15,035 bytes、SHA256 `fac07126fb063b62952a3a687729a6551bb59f699816e77828afc8b0afc578c4`，reviewed_at=`2026-10-20T12:15:19+00:00`，16/16 PAPER PASS/P024。报告晚于本 proof，作为分离固定验收证据使用；实际数学闭包与接受版本完全一致，未把尚未签发的旧台账状态当成验收。也完整读取 T170 既有报告，并重新核对以上实际空间/算子/载荷/控制证明，而非仅复述其 PASS。

本地证据 `/tmp/carleman-t268-local-evidence.json` 的 status=PASS、source=local、checked_sha/source_head_sha 均为本报告 proof；实际根构建和全命名空间递归审计退出码均为 0，finished_at=`2026-10-20T12:15:58.535596+00:00`。独立重新计算并逐项绑定如下：

| 固定产物 | 独立验证结果 |
| --- | --- |
| `/tmp/carleman-t268-local-source-manifest.txt` | 1,082 项，117,456 bytes；路径集合准确等于固定提交全部 tracked `.lean` 及三个 Lean 配置文件。每项内容 SHA256 与 Git blob 一一相同。清单 SHA256 `f19b2df8dd9cb5f7925db71c337b729681e272305aeee92c4bdf9711fdfffc94`。 |
| `/tmp/carleman-t268-physical-control-local-axioms.txt` | 3,568,544 bytes；SHA256 `2ed5d8a79fb0aa867dd76676377473a80099bbba60d9dc68a1671ae0d9d6795d`；最终行明确为全部 **10,583** Carleman declarations 审计通过。 |
| `/tmp/carleman-t268-load-build.log` | 实际载荷模块 3,984 jobs 成功；117 bytes，SHA256 `17473a776924f5f0f36c98b81da590da279a27d2634d2a0e872a905a7451f1ec`。 |
| `/tmp/carleman-t268-target-build.log` | 正式物理控制目标 3,987 jobs 成功；121 bytes，SHA256 `8674ca65311632f27604ca3938f59608eada165070344628113f880b535dea98`。 |
| `/tmp/carleman-t268-root-build.log` | 根模块 4,324 jobs 成功；80 bytes，SHA256 `6dee1c8870f88fbc7da9d53fd7366b0adb4d4b2858e0c4d22bdc33d08bfc8dfd`。 |

另发现同前缀 `control-build.log` 是较早的 `letI` 风格 linter 失败记录，不能用作成功证据。固定最终源码相应局部实例已用 `let`；上述正式 target/root 日志及固定类型审计成功替代该早期失败。这不是未处理的数学或构建缺陷。

根模块明确导入两个新模块和两个既有入口。CheckAxioms 对四个完整名字执行 `#check` 与 `#print axioms`，其环境递归扫描逻辑与基线不变。独立解析 raw 的 4,249 个公理集合与 10 个无公理记录，未发现白名单外依赖；四个所审定理都仅依赖 `propext, Classical.choice, Quot.sound`。无 sorryAx、额外分析公理或假设目标结论。

Lean 固定 `leanprover/lean4:v4.35.0`，实际本地证据编译器 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`。固定锁文件及实际干净 mathlib checkout 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。本报告核验已实际执行的本地日志及精确源码绑定，没有声称重跑全库或远端 CI。

## 最终判定

**4/4 PASS，无阻断缺陷；可按 PAPER 完成 P014 和 P015。** 一般凸多面体完整 P1 与原 Cartesian 盒分支合起来覆盖两条原命题的域、维数和离散实现范围，原假设、全状态、真实控制、常数顺序及指数精度均保留。此前独立接受的 P024 是实际已清偿依赖，当前结果已不再是条件于 CE 的辅助物理推论。

本报告仅新增并单独提交本文件，不修改数学、总台账或原稿，不 push；签发后正文及 reviewed_at 冻结。原后续滤波/极限命题不由本验收自动提升。
