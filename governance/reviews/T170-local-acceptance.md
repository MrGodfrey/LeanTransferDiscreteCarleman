# T170 / C186 独立本机验收：盒 Cartesian 物理观测与真实 HUM 控制

- checked_sha / source_sha: `3a752bc986ef1a893825b6597211ccb519d8a292`
- mathematical_base: `7d1cc86d3c0a01b524f099ba90baaf59784f159d`
- reviewed_at: `2026-10-19T13:36:55+00:00`
- reviewer: 独立本机数学验收 Agent `/root/accept_section3`
- result / axiom_check: **PASS / PASS**，3/3 显式声明通过。
- scope: **AUXILIARY**；C186 可在完整盒 Cartesian 实例范围登记 REVIEWED。原文覆盖保持 **17/26**，不提升 P014/P015，也不将本实例计作一般几何或 P1 的完整原文覆盖。

## 固定版本与原文范围

独立读取上述 Git 对象中的三个新模块及完整展开类型、实际调用的关键证明、`AGENTS.md`、`governance/PROJECT_OPERATIONS.md`、`state/README.md`、T170 分析和 `MATH_SPEC`。既有 MILESTONES/PAPER_COVERAGE 协议沿用；本批没有修改其内容。后续 T171/T172 工作树、动态根导入和动态 `.ci/axioms.txt` 均未用作本批证据。

原稿对照包括 Section 7 的原物理正向/伴随方程（约 1720–1770 行）、`prop:physicalO`/`eq:physicalconditions`/`eq:mainO`（1828 行起）及三步证明、`prop:physicalC`/`eq:mainC`/`eq:main-terminal`（2028 行起）及 penalized HUM 证明。固定 `paper/main.tex` SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

本批给出两项原结果在正维坐标盒、原 Cartesian 差分实现上的完整实例。固定盒、非空开观测内集 W、开集 ω、`closure W ⊆ ω` 和步长可比界 ratio 是选择参数前的几何数据。没有把整个原论文的 P1/一般几何范围缩成盒后登记为 PAPER。最终接口不再要求调用者提供 Carleman 估计、椭圆正则、数值测试、Laplacian 自伴性或频率过滤条件。

## 全部声明与逐项判定

顺序与固定 `/tmp/carleman-t170-cartesian-observation-control-declarations.json` 及 C186 一致；源码位置相对于 `Carleman/Control/`，raw 行是固定完整类型的起始行。

| 声明 | 固定源码 / raw 行 | 数学结论及判定 |
| --- | --- | --- |
| `Carleman.Physical.physical_observation_uniform_profiles` | `PhysicalObservationUniformProfiles.lean:11` / 32884 | 按固定相位界和负性阈值，在全部空间类型、测度、相位及离散数据之前选择同一观测常数；实际一般载荷接口和原伴随方程保留。PASS。 |
| `Carleman.Physical.box_cartesian_physical_observability` | `BoxCartesianObservation.lean:17` / 32952 | 从真实盒 Cartesian 载荷 CE、物理质量等距和节点势内部构造一般接口，对任意原非周期伴随解得到真实控制 Hilbert 空间中的 B* 观察及原指数余项。PASS。 |
| `Carleman.Physical.box_cartesian_physical_control` | `BoxCartesianControl.lean:15` / 33034 | 对全部原初态构造实际节点控制及整个正向解，精确满足原 ForwardEquation、物理时间控制范数和指数终态界。PASS。 |

## 量词、相位与物理观测

一般引理先固定 `Rbound, β, qc, CI, CCE, Cmass, rstar`，实际前提为 β>0、qc≥1、CI/CCE≥0、Cmass/rstar>0。先有 `∃ Cb d0>0`，再有 `∀ T>0, M≥0, ∃ C>0`，之后才量化 Ω、ν、值空间 E、相位 ρ、状态 Hilbert 空间 X 和全部网格/算子/轨道。不是先对每个网格分别选择 C 再声称统一。

证明直接选择 `Cb ≥ max 2 (32*CCE)`、`d0 = physicalEndpointRate rstar / 4`，并在引入 ρ 之前取显式 `physicalObservationConstant Rbound T M qb Cmass CI CCE rstar`。重新读取该常数、原物理权构造、端点余项和初态恢复证明：其相位依赖只经 `ρ.bound`，故 `ρ.bound = Rbound` 的替换合法。`physicalEndpointRate rstar = 2*rstar/sqrt(1+9*π²)` 为正，精确代数给余项 `exp(-2*d0*S)`；没有丢失乘在指数前的 S 而不吸收。

`qb = Cb*(qc+T⁻¹+M^(2/3))`，原 `qb*T ≥ Cb` 和 `qb³ ≥ Cb³*M²` 内部给导数预算和势吸收。实际选择的周期光滑权最大值为 S，并满足 PhysicalQClass；潜在项预算为 `2*CCE*M² ≤ q(t_i)³/2`。M=0 包含在实幂非负分支中，没有额外 M>0 或除以 M 的步骤。只在证明中周期化 cutoff 状态，最终 p 未附加周期条件。

盒实例以固定 Gaussian 节点相位 `cartesianInteriorCountProfile` 实现 Rbound=2、rstar=1。逐节点负性是真实相位值的 `≤ -1`，并非仅形式参数。重新检查 T169 的 `PhysicalLoadCarleman` 供给：原 q³ 状态范数由完整节点能量的非负梯度项推出，真实逆等距载荷及实际控制观察精确识别；原 PhysicalQClass 到 IntervalQClass 保留 β、qc、T、端点及一二阶导数预算。没有外置额外权类或目标 CE 前提。

真实有限物理 Hilbert 状态具有 `‖f‖² = (∏δ_j) * Σ_a f(a)²`。`E = cartesianCountLpEquiv` 把 f 送到实际计数 L² 类 `sqrt(∏δ_j)*f`，是满射线性等距。这里 R=I=E，Γ=E⁻¹；并非误将不同类型的映射写成字面恒等。两方向质量比较及载荷权比较常数都严格为 1，ΓI=id 精确成立。

任意实节点势 b_i(a) 仅要求 `|b_i(a)|≤M`。实际乘子对物理质量内积自伴，算子范数≤同一个 M，且 `Γ (b_i.map (E x)) = V_i x` 由真实 Lp 代表与逆映射身份供给。原标准 (2d+1) 点 Laplacian 的实际对称性/非负性来自原刚度与梯度积分身份。没有采用任意有限维范数等价，亦没有含节点数、最大特征值或网格相关范数转换因子。

一般引理中的 Bstar 以 `O = E ∘ B ∘ B.adjoint` 实现。B 是 ω 内节点到全部内部节点的真实零延拓；B* 是物理 Hilbert 伴随限制。原质量内积给 `B*B=id` 和 `‖Bv‖=‖v‖`，因此 `‖O x‖ = ‖B* x‖`，最后的 `simpa` 确实得到 U_h 范数中的原观察量。没有把全状态范数或连续 L² 观察冒充节点控制范数。

最终选取 qc、κ、h0、Δ0、Cb、d0 的次序都在 T/M 之前；C(T,M) 又先于 o、δ、N、h、g、节点势和全部状态。原 `S = κ*min(h^(-4/5),dt^(-2/5))` 保留，两侧 `16*qb≤S≤qb*T/(4*dt)`、`dt*M≤1/2`、`dt≤min(Δ0,T/12)` 和原可比步长条件完整保留。N 为每轴的全部有限节点参数；域相等和正步长是真实网格条件，不增加低频、状态光滑性或额外频率选择。

## 非周期方程、所有解与实际 HUM

逐一展开 `PhysicalEquations`：索引 i 对应论文 n=i+1，正向为 `dt⁻¹*(y(i+1)-y(i)) + (A+V_i)y(i+1) = B u_i`，伴随为 `dt⁻¹*(p(i)-p(i+1)) + (A+V_i).adjoint p(i) = 0`。最终观察求和恰为 i=0,…,N−1 的 B*p(i)，终值恰为 p(N)。真实 Hilbert adjoint 未被未经证明的转置或同名形式代替。

观测声明量化任意 `p : Fin (steps+1) → X_h` 满足该方程，覆盖所有原非周期解。重读 PhysicalFlow/PhysicalLemma 的 step 可逆性与前后向递推，`dt*M≤1/2` 由对称下界给每步可逆性；全部终态的伴随和全部初态/控制的正向解存在唯一，不依赖循环假定目标观测成立。

控制声明调用已证 `relaxed_control_of_observation`，其内部真实 HUM 使用 `ε = exp(-d0*S)>0`、`ε² = exp(-2*d0*S)`，实际 `O*O+ε²I` 的可逆性来自平方能量。`PiLp 2` 中的控制向量带 `sqrt(dt)`，解缩放后 `controlNorm dt u = sqrt(dt*Σ‖u_i‖²)`，没有遗漏物理时间步长。

HUM 内部给真实控制 u 后以 `existsUnique_forward` 构造完整 y，精确对偶恒等式给终态身份。最终定理实际输出 `y 0 = y0` 与整个 ForwardEquation，而不只是抽象终端向量或存在的最优性方程。对任意 y0，成本为 `sqrt(C)*‖y0‖`，终态为 `sqrt(C)*exp(-d0*S)*‖y0‖`；这是原 `C(T,M)` 成本结论的显式选择，C 与网格、势的具体取值及 y0 无关。不存在频率子空间、不变性或原方程以外的状态限制。

## 依赖版本与递归公理

从三个模块递归解析实际 `Carleman.*` 导入，共 757 个模块；除三个新增模块外，754 个旧模块逐文件与数学基线相同。对下列已验收入口又独立比较其整个导入闭包；均未变化：

| 依赖入口 / 既有验收 | 固定接受版本 | 闭包模块数 |
| --- | --- | --- |
| BoxCartesianLoadCarleman / [T169](T169-local-acceptance.md) | `7d1cc86d3c0a01b524f099ba90baaf59784f159d` | 752 |
| PhysicalFiniteWeights / [T168](T168-local-acceptance.md) | `30a03e32af45ef82baacbbfe6917cd7ceff234f3` | 44 |
| PhysicalObservationUniform / [T029](T029-local-acceptance.md) | `f84745210c4ee35c2dd924f9c6ff04788047c28d` | 42 |
| RelaxedControl / [T026](T026-local-acceptance.md) | `549cde718bcf26f00b24f4a1493ee92b839f30b4` | 11 |
| BoxCartesianHeatEstimate / [T167](T167-local-acceptance.md) | `d4b7f2d6d6894520fc5db06dc3a230be27518297` | 746 |

T170 固定台账中的 C185 当时仍为 BUILT；签发前已读取独立 T169 正式 PASS 报告，报告提交 `cf033f11dc66ebab3c8a083ed3db516cb1d78183`、checked SHA 与上述 C185 版本完全相同。这是明确版本的后续验收证据，没有将旧 BUILT 标记解释成已审查，也未代主线程修改台账。上述闭包比较及关键证明阅读是本次独立核对，不只依赖旧执行者总结。

固定根导入包括全部三个新模块，CheckAxioms 对三个完整名字分别执行 `#check` 和 `#print axioms`。实际末尾审计遍历环境中所有经 `privateToUserName` 还原后属 Carleman 的声明，并对每项执行 `collectAxioms`。原始输出末行为 `Axiom audit passed for all 8096 Carleman declarations.`；另独立解析 3059 项显式公理记录和 9 项无公理记录，未发现白名单外依赖。三个新定理均仅依赖 `propext, Classical.choice, Quot.sound`。新增源码无 sorry/admit/axiom/native_decide；没有把空 stderr 当作审计 PASS。

Lean 固定为 `leanprover/lean4:v4.35.0`，CI 实际编译器 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib 固定及实际本机干净 HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。CI 工作流固定检出 github.sha，执行真实根构建及递归审计，result 记录实际源码版本。独立读取本机定向日志的 3068、3986、3987 jobs 成功与固定全库 4097 jobs 成功；正式构建依据同时包含下列同 SHA 远端成功记录。

## 独立远端证据

本验收 Agent 自行读取 GitHub 实际 API，并自行以 `gh run download` 下载同次两个原始工件，两个命令均 exit 0；没有使用主执行者下载副本代替独立下载。

- run: [39260278276 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39260278276/attempts/1)，event=push，branch=main，head_sha 为本报告 checked SHA，最终 completed/success，API updated_at=`2026-10-19T13:30:52Z`。
- 三项实际 jobs：lean **118085804724**、state-check **118085805457**、dashboard / snapshot **118087485424**；均 completed/success。Lean 的 proof build、结果记录及两个上传步骤也均 success。
- `lean-ci-result` artifact **12191290455**，ZIP 492 bytes，API digest `sha256:05505dd59040630a81fd9808fbbedc76cc8c654f164121bef6ee42ab8cc38bf8`。
- `lean-declaration-evidence` artifact **12191305431**，ZIP 234882 bytes，API digest `sha256:bf867cbfc7430819fcb34aa299125a87060810f1062f1fbd9b896176778d8982`。
- 两工件 workflow_run 均绑定同一 main、同一 run 和同一 checked SHA；ZIP digest 与解包后的 raw digest 分别记录，未混为一物。

独立下载路径为 `/tmp/carleman-t170-cartesian-observation-control-main-ci/result.json` 和 `/tmp/carleman-t170-cartesian-observation-control-main-axioms/axioms.txt`。实际 result 为 537 bytes，SHA256 `0329c420627b97191e67b68d0313099e26041878f602a2eb9bfb9d1c36b98d49`；内容 status=PASS、checked_sha=source_head_sha=`3a752bc986ef1a893825b6597211ccb519d8a292`、targets=[Carleman]、finished_at=`2026-10-19T13:29:28.957843+00:00`，ci_url 指向上述同次 run/attempt，Lean/mathlib 字段与固定 pin 一致。

独立逐字节比对远端 raw 与 `/tmp/carleman-t170-cartesian-observation-control-local-axioms.txt`，结果完全一致：**2529676 bytes**，SHA256 **`4898f0fd311b42c290e7317371fb9e7d7f3b0b76c0e2864fab66a8f63b8ce174`**。完整类型、公理集合及最终 8096 项递归成功记录均来自该固定 raw。

## 最终结论与保留范围

**3/3 PASS；C186 可在 AUXILIARY 范围登记 REVIEWED。** 未发现阻断数学或对象身份缺陷。原 physicalO/physicalC 的盒 Cartesian 实例确已给出全状态、任意有界实节点势、真实非周期方程与控制、原网格尺度两侧条件及网格统一的参数次序。一般几何、P1 和整个 P014/P015 不由本实例自动完成，原文覆盖维持 **17/26**。本报告仅单独提交，不 push，不修改数学、原稿或总台账；通知后正文和 reviewed_at 冻结。
