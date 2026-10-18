# T033 / C049 — 原投影加权测试与统一时间界独立验收

- checked_sha: `d999e5b3779aa82efee2da8e162b86148dc1f715`
- base_commit: `1cf3071913d460625411022e4ea16c8336399bf8`
- reviewed_at: `2026-10-18T17:12:17+00:00`（UTC）
- reviewer: 独立数学验收 Agent `/root/accept_spatial_lemma`，非本阶段执行者
- target: 五个 Control 模块，全部 20 项显式声明
- result: **PASS**；独立数学语义及同 SHA 正式构建门槛通过
- axiom_check: **PASS**；同 SHA 远端 3848 声明递归审计与本批 20 项检查
- scope: **CONDITIONAL**
- extra_hypotheses: `["具体P1网格的N3与空间超逼近、原连续热CE及Dirichlet实例仍待供应"]`

独立用 `git show <checked_sha>:<path>` 读取五个新增模块的全部证明、20 项实际展开类型及相关依赖，对照原稿 N4（453–464 行）、Section 6 Step 3（1569–1616 行）、原热尺度和 Theorems 7.2–7.3。另核对固定 MATH_SPEC、`governance/analysis/T033-projected-weighted-test.md`、C049/T033 状态记录，并沿用没有改变的根 AGENTS、治理和证据协议。未审核后续未提交数学代码。

## 结论和范围

本批真实构造原投影测试 `Π_X(σ²z)`，证明准确加权配对、能量等式、对称非负、周期端点、N4 所需的闭区间二次型真导数及统一时间界；从特定测试的原空间超逼近构造 N4 数据，最后接入实际 Galerkin 观测控制链。未发现所声明结果的数学缺陷、额外隐藏估计或常数量词错误。同 SHA 正式构建门槛已通过，C049 可升为 `REVIEWED/CONDITIONAL`。

本次不完成 P011 / Proposition 6.1、P014 / Theorem 7.2 或 P015 / Theorem 7.3。具体网格的 N3 和空间超逼近、原 Dirichlet 梯度形式/算子及连续热 Carleman 供应仍未建立。与较早仅假设周期 CE 的接口不同，本次最终入口沿用已验收 T031/T032 的原 transfer，**周期离散 CE 在条件数据给定后由原 Corollary 2.3 内部推导**；剩余显式 CE 是原连续 A4，不能将两者混同。

## 原投影测试的准确身份

对真实完备 L² 子空间 X，包含 R 采用其诱导 L² 内积，定义

`F(t)=ρ.weightCLM w τ t ∘ R`，`T(t)=F(t).adjoint ∘ F(t)`。

`weightCLM_apply` 把该有界算子识别为实际允许权 `σ=q^τ exp(qρ)` 的 Lp 乘法；不是另给的抽象权算子。`galerkinWeightedTest_pairing` 用真实 Hilbert 伴随公式证明任意 x,z 的 `⟨x,Tz⟩=⟨σRx,σRz⟩`。再利用原实乘法算子的对称性和正交投影配对性质，`galerkinWeightedTest_apply` 得到

`T(t)z = X.orthogonalProjectionOnto (σ.map (σ.map (Rz)))`。

两次乘法在真实 a.e. Lp 类上进行，故恰为原 `Π_h(σ²z)`；并未把 `ΠσΠσ` 错当成 `Πσ²`，也没有要求 σX⊆X。`galerkinWeightedTest_energy` 是准确等式 `⟨z,Tz⟩=‖σRz‖²`，因此原 test-norm 的比较常数为 1。对称性和非负性直接来自此配对。原正定性没有因接口只列 nonneg 而丢失：已证 `SpatialProfile.seminorm_definite` 给允许权 seminorm 为零当且仅当 Rz=0，而 R 是包含；所以 z≠0 时右侧严格正。这是现有等式及既有定理的直接后果，本批未另列名为 positive_definite 的声明。

端点证明实际使用 `TimeWeightRegularity.endpoint` 的 q(0)=q(T)，经真实 weightCLM 的端点相等得到整个 T 算子相等，随后转为 N4 的 LinearMap 端点等式。结论在一个闭周期的两端成立；未把仅端点匹配误说成已证明任意实时间平移周期，也不需要物理伴随轨迹周期化。

## 真导数、闭区间与统一时间常数

已直接复核 `TemporalMultiplier` 的 `hasDerivWithinAt_weightCLM`：它对 `exp(τ log q)` 和真实指数乘法算子作链式/乘积求导，导数是在连续线性算子空间的算子范数中，而不是仅逐点的空间导数符号。`TimeWeightRegularity` 的 derivative 本身有 `HasDerivWithinAt q derivative (Icc 0 T)` 证明，并有原 `|q'|≤βq²`；q≥1 排除 log 和倒数的问题。

本批 `weightedInclusionDerivative=weightDerivativeCLM∘R`，并定义

`Tderiv=D.adjoint∘F+F.adjoint∘D`。

其配对精确为 `⟨Dx,Fz⟩+⟨Fx,Dz⟩`。`galerkinWeightedTest_hasDeriv` 将实际算子范数导数作用到固定 z，再用 Hilbert 内积的导数规则，证明每个 z 和每个 t∈[0,T] 上

`HasDerivWithinAt (s ↦ ⟨z,T(s)z⟩) ⟨z,Tderiv(t)z⟩ (Icc 0 T) t`。

闭区间包括 0、T；没有缩成开区间、a.e. 时间或只在节点求导。没有要求状态随时间更光滑，也没有不当交换空间积分和导数。本批正式提供的是原 Section 4 使用的**二次型导数结论**，不是另一个已经列名证明的 T 的算子范数导数定理；前置 weightCLM 的算子范数真导数保证此推导不是给形式导数改名。原 Step 3 的积分导数身份通过这些真实 L² 内积与乘子表达实现，其在 N4 中需要的内容均实际提供。

相对导数证明使用真实对数导数作用

`D(t)z = (τq'(t)/q(t)+ρq'(t)) · (σ(t)Rz)`，

其有界乘子范数≤`β(|τ|+ρ.bound)q(t)²`。`weightedInclusionDerivative_bound` 正是将此界作用于**已加权**状态 Fz。随后 Cauchy–Schwarz 和绝对值三角不等式给

`|⟨z,Tderiv z⟩| ≤ 2‖Fz‖‖Dz‖ ≤ 2β(|τ|+ρ.bound)(q‖σRz‖)²`。

对全部 |τ|≤τStar，最终 Ctime 精确为 `2β(τStar+ρ.bound)`。这个常数不含 T、X、维数、mesh、dt、qmax、z 或时刻。已有绝对算子导数上界中的 qmax 与指数上包络没有传入该相对时间界。证明不使用加权正交投影稳定性，也不把一个依赖 X 的范数当作统一常数。

`ρ.signed e` 的负号分支是 ρ.neg，其 bound 与 ρ.bound 定义上相同；逆权同时变换 ρ 和 τ。`toGalerkin` 对两个 Bool 分支分别构造测试，输出同一个 Ctime，没有取错 −ρ.bound、丢失负号族或只检查 τ=0。上述辅助引理中 |τ|≤τStar 已隐含 τStar≥0；最终入口还显式假设非负 τStar 和正 β。

## 空间超逼近及 N4 的实际组装

`GalerkinSuperapprox` 的左侧是实际 V 中的

`N_(σ⁻¹)( inclusion(Tz) − σ(σ(inclusion z)) )`，

右侧为原 `Csuper*mesh*w.max*N_σ(inclusion z)`。`conformingWeight` 是由原 A2 保持性见证得到的 V→V 乘法；双乘法共用的见证适用于所有 V，故第二次应用合法。逆权为 `ρ.neg.multiplier w (-τ)`，准确对应 σ⁻¹。所用参数范数来自真实唯一弱 Sobolev 导数，而非任意给定函数。

超逼近量化整个闭时间区间、全部 z∈X、每个 V 保持性见证。该条件在孤立辅助定义中是一个条件命题，但在最终数据中并不靠“没有保持性见证”而空真：`ProjectedHeatData.allowed.data` 的原 `AllowedWeightData.form_preserving` 正为每个符号、指数和时刻提供该见证。没有要求权乘法保持 X，也未增加 h²qmax²、最终误差或投影稳定性等替代前提。

`galerkinWeightedTestData` 为既有 `Section4.WeightedTest` 的每一个字段供应实际内容：op、derivative、endpoint、hasDeriv、symmetric、nonneg、time_bound；唯一从 hs 传入的字段是上述特定测试的空间 superapprox。r 为真实 conformingReconstruction，r.RH 与 L² 包含定义一致，所以时间界和空间界使用同一状态。没有偷偷保留任意测试算子的选择或独立时间常数输入。

`ProjectedHeatData` 四字段仅为原 AllowedFamily、两符号/全部 |τ|≤τStar 的 N3、同样权族的特定空间超逼近，以及全部 Orientation/真实 PeriodicWeakTrajectory 的连续 A4。其实际展开类型不含 β；β 在 `toGalerkin` 中由真实 TimeWeightRegularity 带入。这是正确的参数分离，并非数据丢失。N3、原解析估计和连续 A4 原样转交，N4 由新构造填入，未把任何目标离散 CE、物理观测或控制存在性塞入结构。

## 最终物理量词和剩余实例义务

`projected_heat_observation_control_uniform` 在调用已验收的 Galerkin 入口之前，将 Ctime 固定为 `2β(τStar+ρ.bound)` 并证明其非负。随后选取 κ、h0、Δ0、Cb、d0；在这些常数之后才量化 T>0、M≥0 并选正 Cphys(T,M)。X、有限维实例、g、mesh、errors、完整权族数据、势 b、全伴随轨迹及任意初值均在 Cphys 之后。没有把 T 或数据先固定再选择统一常数。

实际尺度仍为 `κ min(mesh^(-4/5),dt^(-2/5))`，qb 仍为 `Cb(qc+T⁻¹+M^(2/3))`。原 h≤h0、dt≤Δ0、dt≤T/12、dt*M≤1/2、16qb≤Smax≤qbT/(4dt)，以及误差阶 aE≤Cap*h、a₀+ηA≤Cap*h² 全部保留。调用对完整 PhysicalQClass 且 w.max≤Smax 的每个权使用 `hw.toRegularity` 构造测试，未削减 qclass、正负空间权或时间方向。

刚度仍为从原形式实际构造的 galerkinStiffness，势为真实投影乘法势；观测适用于全部 N+1 节点、满足真实 Hilbert 伴随方程的 p，观察位置为 p^(n−1)，终端余项为 `exp(−2d0 Smax)‖p^N‖²`。控制结论给任意 y0 的真实区域 L²(obs) 控制与全部 N+1 前向节点，满足原 Euler 方程、`controlNorm≤sqrt(Cphys)‖y0‖` 和实际终值界 `‖y^N‖≤sqrt(Cphys)exp(−d0 Smax)‖y0‖`。没有滤波子空间、周期物理轨迹或初值限制。

OriginalForm、域正则性 hD、椭圆估计 hell、SmoothOnClosure ρ、AllowedFamily、N3、空间超逼近与连续 A4 仍需具体热/P1 实例供应。这里只减少了可任意输入的测试数据，未证明原网格分级、加权投影稳定性、插值/逆估计或具体连续 Dirichlet 热 CE，故范围必须保持 CONDITIONAL。

## 全部 20 项声明

名称与 `/tmp/carleman-projected-test-declarations.json` 一一对应；每项均核对固定源码、实际类型和递归公理。

| # | 完整声明 | 独立结论 |
| --- | --- | --- |
| 1 | `Carleman.Physical.weightedInclusion` | PASS；真实乘法算子复合 L² 包含 F。 |
| 2 | `Carleman.Physical.galerkinWeightedTest` | PASS；真实 Hilbert F*F。 |
| 3 | `Carleman.Physical.galerkinWeightedTest_pairing` | PASS；全部 x,z 的准确加权配对。 |
| 4 | `Carleman.Physical.galerkinWeightedTest_apply` | PASS；恰为 Π_X(σ²z)，不是两次投影。 |
| 5 | `Carleman.Physical.galerkinWeightedTest_symmetric` | PASS；真实内积中的对称性。 |
| 6 | `Carleman.Physical.galerkinWeightedTest_energy` | PASS；原 test-norm 准确等式。 |
| 7 | `Carleman.Physical.galerkinWeightedTest_nonneg` | PASS；由实际平方范数得到。 |
| 8 | `Carleman.Physical.weightedInclusionDerivative` | PASS；已证真乘法导数复合包含。 |
| 9 | `Carleman.Physical.galerkinWeightedTestDerivative` | PASS；D*F+F*D 的实际算子表达。 |
| 10 | `Carleman.Physical.galerkinWeightedTestDerivative_pairing` | PASS；两项内积配对，无漏因子。 |
| 11 | `Carleman.Physical.galerkinWeightedTest_endpoint` | PASS；真实 q 周期端点给整个测试算子端点相等。 |
| 12 | `Carleman.Physical.galerkinWeightedTest_hasDeriv` | PASS；闭区间每点的二次型 HasDerivWithinAt。 |
| 13 | `Carleman.Physical.weightedInclusionDerivative_bound` | PASS；相对已加权状态的真实导数界。 |
| 14 | `Carleman.Physical.galerkinWeightedTest_time_bound` | PASS；准确 2β(|τ|+ρ.bound) 和 q² 因子。 |
| 15 | `Carleman.Physical.galerkinWeightedTest_time_bound_uniform` | PASS；全部允许 τ 共用 Ctime，常数无 T/qmax/X。 |
| 16 | `Carleman.Physical.GalerkinSuperapprox` | PASS / 条件接口；原特定测试、V 双乘法、逆权和 h*qmax。 |
| 17 | `Carleman.Physical.galerkinWeightedTestData` | PASS；空间超逼近之外的 N4 字段内部证明。 |
| 18 | `Carleman.Physical.ProjectedHeatData` | PASS / CONDITIONAL；仅剩原解析、N3、空间超逼近和连续 A4 数据。 |
| 19 | `Carleman.Physical.ProjectedHeatData.toGalerkin` | PASS；两符号、全部 τ、同一 Ctime 的实际 N4 组装。 |
| 20 | `Carleman.Physical.projected_heat_observation_control_uniform` | PASS / CONDITIONAL；内部固定测试与时间常数，保留原尺度、量词与全物理结论。 |

## 依赖、版本与公理证据

已读取 [T032 / C048 独立验收](T032-local-acceptance.md)，并直接复核 GalerkinHeatData、GalerkinNumericalData、GalerkinHeatControl 的实际调用和物理尺度。本批基线即该验收 SHA；基线至固定 SHA 没有修改既有 Carleman 数学文件，只新增本批五模块。另直接复核 TemporalMultiplier、TemporalDerivatives、TemporalPerturbation、AllowedWeight、AllowedFamily、AllowedWeightData、SignedUniform、ShiftedFormBounds 和 Section4.TestData 的实际接口，未仅凭既有验收报告认可新的调用。

五模块全部由固定 `Carleman.lean` 显式导入。固定工具链、mathlib、原稿、治理协议和 CI 工作流未变。`CheckAxioms.lean` 对 20 项逐项检查类型/公理，并对所有经 privateToUserName 归属 Carleman 的公开/私有声明递归 collectAxioms，仅允许 `propext`、`Classical.choice`、`Quot.sound`。

本机 `/tmp/carleman-projected-test-full.log` 记录 `Build completed successfully (3518 jobs).`。固定 `/tmp/carleman-projected-test-local-axioms.txt` 为 1128481 字节，SHA-256 为 `59966cdcae6ad88230f1ae7f0e5d025c9e3811e84a747f44d7ad3cded03abaec`。20/20 项均有完整实际类型和公理输出，各项恰为三项标准基础公理；全局末行 `Axiom audit passed for all 3848 Carleman declarations.`。无 sorryAx 或未批准数学公理。

已通过 GitHub connector 独立读取 [main CI 39148036906 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39148036906/attempts/1)，确认 head SHA 为本次固定 SHA，head_branch=main、event=push、status=completed、conclusion=success。三个实际 jobs 均完成且成功：state-check（117735790865）、lean（117735791040）、dashboard / snapshot（117736471958）。同次 artifact 元数据中 `lean-ci-result`（12144311364）和 `lean-declaration-evidence`（12144276557）均绑定此 run 和固定 head SHA。

原始 `/tmp/carleman-projected-test-main-ci/result.json` 为 537 字节，SHA-256 为 `b6aa6b904ca882fbd51bd9162dae7135e7b056153ef272f2ffb1c2d276dc3659`。实际内容为 PASS，checked_sha=source_head_sha=`d999e5b3779aa82efee2da8e162b86148dc1f715`，target=Carleman，finished_at=`2026-10-18T17:08:30.389992+00:00`，Lean 4.35.0（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`），mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`，与固定源码 pin 一致。

正式远端公理产物 `/tmp/carleman-projected-test-main-axioms/axioms.txt` 为 1128481 字节，SHA-256 为 `59966cdcae6ad88230f1ae7f0e5d025c9e3811e84a747f44d7ad3cded03abaec`，已实际逐字节比较确认与固定本机副本相同。再次针对远端原始文件核对 20/20 项完整类型及三项标准基础公理，确认全局 3848 声明审计 PASS。没有用后续 T034 草稿或其它提交的产物替代本次证据。

本次只写本报告，未修改数学源码、原稿、根导入、台账或覆盖表，未 commit/push。
