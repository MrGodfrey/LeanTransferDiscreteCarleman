# T030 — 真实 L² 子空间与 L²(ω) 观测控制接口独立验收

- checked_sha: `31d5e165a595849bc1c882523838aad69576b594`
- base_commit: `f84745210c4ee35c2dd924f9c6ff04788047c28d`
- reviewed_at: `2026-10-18T16:39:45+00:00`（UTC）
- reviewer: 独立数学验收 Agent `/root/accept_spatial_lemma`，非本阶段执行者
- target: C046；五模块、全部 32 项显式声明
- result: **PASS**
- axiom_check: **PASS**；同 SHA 远端 3597 声明递归审计及本批逐项检查
- scope: **CONDITIONAL**
- extra_hypotheses: `["具体P1/FD及其统一周期载荷Carleman估计仍须供应"]`

本次用 `git show <checked_sha>:<path>` 独立读取五模块全部定义、声明和证明，逐项核对实际 elaborated 类型；回查原稿 Section 6 的 P1 载荷/控制定义（1485–1493）、Section 7 的势和物理方程（1715–1749）、原 Theorem 7.2（1827–1851）及 Theorem 7.3 与 HUM 证明（2032–2103）。另读根 AGENTS、治理和状态证据协议、MATH_SPEC T030，以及固定 C046/T030/P014/P015 记录。执行者说明及后续工作树源码不替代固定版本证据。

## 验收结论与原文边界

32 项实际完成真实 L² 子空间的质量、正交载荷右逆、乘法势、区域限制与零延拓、真实 Hilbert 控制伴随，并将其接入已验收的周期载荷 CE→物理观测条件桥及物理 HUM。未发现需要修正的数学缺陷、隐藏目标估计前提、错误边界条件或量词交换。C046 可升为 `REVIEWED`，范围必须保留 `CONDITIONAL`。

**P014 / Theorem 7.2 与 P015 / Theorem 7.3 不得因此提升为原文完成。** 当前 X 是任意真实 L² 子空间，A 仍为输入的非负自伴有界算子；没有构造具体 P1 网格、Dirichlet 刚度或 FD 对角质量/节点势，也没有从完整离散 Carleman 能量供应本次 `PhysicalLoadCarleman`。原 h、h0、Δ0、κ 和 S_(h,dt) 的具体实现仍待连接。当前通过的是清偿上述算子接口后的条件蕴含，不能把泛化空间中的有效定理当作具体离散实现已经完成。

## 真实正交质量、载荷与势

X 是 `Submodule ℝ (Lp E 2 ν)`，采用真实诱导内积；R=I 为包含，Γ 为 mathlib 的 `X.orthogonalProjectionOnto`，并非未指定线性映射。完备 X 足以提供正交投影，控制入口的有限维 X 自动满足完备性。`conforming_load_right_inverse` 证明 ΓI=Id；`conforming_mass_norm` 是包含的准确等距性。最终观测证明实际以 R=I、Cmass=CI=1 调用上游，双向质量平方界和所有允许权下的 I 稳定性由相同 Lp 元素的等式内部清偿。没有额外假设加权正交投影收缩；这里需要的是 I=R 的加权恒等式。

`BoundedMultiplier` 提供实函数 b、a.e. 强可测性和 a.e. 的 `|b|≤b.bound`。其 map 先证明乘积属于 MemLp，再构造实际 Lp 类；代表恒等式只作 a.e. 使用。新 `multiplier_clm_norm` 调用真实 seminorm 界，`multiplier_clm_symmetric` 逐点对实标量移动内积两侧后以 a.e. 积分相等证明对称性。

`conformingPotential X b = Γ ∘ multiplication(b) ∘ R`。正交投影的内积性质给

`⟨V_b x,y⟩_X = ∫ b(t)⟨Rx(t),Ry(t)⟩ dν`，

以及 V_b 对称；在完备 X 上即实际 Hilbert 自伴。取 E=ℝ 时这恰为原 Section 7 的 P1 势积分，向量值版本只是有效推广。投影收缩及乘法界给 `‖V_b‖≤b.bound≤M`，不需要 b≥0，也不要求乘法保持 X。真实兼容 `Γ(b.map(Rx))=V_b x` 由定义给出，最终入口用 `rfl` 供应。原 L∞ 实势可用具有该 a.e. 界的代表描述；本结果不假设点态连续性或额外 Sobolev 正则性。

## L²(ω) 的 a.e. 类、零延拓与真实伴随

区域控制空间明确为 `Lp E 2 (ν.restrict ω)`；它用 Ω 上的限制测度表达 L²(ω)，区域外值不属于可观察数据。`restrictRegionLp` 从 `Measure.restrict_le_self` 降低测度，实际构造限制后的 Lp 类。线性证明将原 Lp 加法/数乘的 a.e. 恒等式降到限制测度；范数收缩使用真实 eLpNorm 单调性及有限性，随后包装为连续线性映射。没有把任意代表的逐点相等误当作 Lp 类相等。

已直接复核 `ZeroExtensionLp`：零延拓是 indicator 乘代表后的 MemLp.toLp，ν-a.e. 等于该 indicator，并以 `eLpNorm_indicator_eq_eLpNorm_restrict` 证明准确等距。它只涉及 L²，不声称跨区域边界保留弱导数。新 `integral_inner_zeroExtend` 由 indicator 积分恒等式给出区域配对；其任意 v 版本使用 mathlib 的总化积分，而实际伴随与控制配对中的测试量都是 L² 元素，相关内积积函数可积。

`restrictRegion_adjoint` 对每个环境 L² 测试向量比较真实内积，证明限制映射的 Hilbert 伴随就是上述零延拓。`zeroExtend_restrictRegion` 用 `ae_restrict_iff'` 证明限制后延拓等于真实 cutoff 乘法；等距性继而给区域范数等于环境 indicator 范数。所有需要 indicator 识别的地方都保留 `MeasurableSet ω`。无需正测度、有限测度、非空或额外 σ-有限性假设；ω 为空或 ν(ω)=0 时区域 L² 为零范数商空间，上述等式和收缩仍成立。

`conformingRegionControl X ω = Γ ∘ restriction.adjoint`，所以对可测 ω 实际为 `B u=Γ(zeroExtend u)`，并有

`B.adjoint = restriction ∘ R`，

`⟨Bu,x⟩_X = ∫_ω ⟨u,Rx⟩ dν`，`‖B‖≤1`。

这与原 P1 控制定义及 B_h* 的限制完全对应。证明使用真实连续线性算子的 `.adjoint`、复合伴随公式、双伴随和投影的伴随，不是给线性映射命名为 Bstar 后直接宣称它是伴随。`conformingRegionControl` 定义本身不依赖可测性证明，可测性用于与零延拓/区域积分的具体识别，属于一致的 Lean 参数省略，并非遗漏条件。

中间 `conformingAmbientControl=Γ∘indicator` 的伴随为 indicator∘R；`conforming_observation_integral` 给其范数平方等于真实区域积分。`conforming_region_observation_norm` 再给每个 x 的区域 B* 范数与该环境伴随范数严格相等，最终入口确实以此改写观测项。显式周期 CE 仍采用环境 indicator 表述；已有 `observation_sq_integral` 将这种加权 seminorm 识别为区域加权积分。这里没有以仅有的未加权范数等式擅自推出任意加权范数相等；最终物理观测转接所需的恰是已证的未加权范数恒等式。

零测度区域没有被排除，也没有被宣称无条件可观测：对于非平凡状态空间，周期 CE 可能无法供应。当前定理仍以该 CE 为明确前提，故包含退化区域并不制造虚假的无条件控制结论。

## 统一物理观测与真实 HUM 控制

实际类型先固定 Ω、E、ν、ρ、ω、β、qc、CCE、rstar 与相应可测性/符号条件；然后存在 Cb、d0；随后对所有 T>0、M≥0 存在正 C；最后才量化 X、g、S、A、全部 b_i、周期 CE、p 和 y0。因此 Cb/d0 不依赖 T/M，C 可依赖固定数据和 T/M，但不依赖 X、维数、网格、S、具体 A/b、轨迹或初值。CCE 固定在这些常数之前，不能为每个网格任意改变后仍宣称统一。

qb 仍为原 `Cb(qc+T⁻¹+M^(2/3))`，入口保留 `16qb≤S≤qbT/(4dt)`、dt*M≤1/2、dt≤T/12 和 g.period=T。g.period 定义为 N*dt，dt>0、N>0 均来自真实 TimeGrid；由 dt≤T/12 已含原 N≥2 的要求。上游 `physical_qclass_uniform` 实际构造完整 qclass；本次没有退回仅有一阶正则性的接口。

CE 输入完整全称量化所有 `PhysicalQClass w g.period β qc` 且 w.max≤S 的 w，并在 `PhysicalLoadCarleman` 内全称量化全部周期状态 z 和实际 Lp 载荷 f，要求原 `D_-z+Az=Γf` 下的实际 q³ 能量界。它不是最终物理观测估计，未假设目标结论；但也不是本批已经证明的输入。`conforming_physical_observation_uniform` 正确调用 C045：内部供应势自伴/范数、Γ 兼容、ΓI=Id、双质量界和加权 I 界，只留下这条统一载荷 CE。

观测输出作用于所有 `p : Fin (N+1) → X`，前提是实际

`dt⁻¹(p^i−p^(i+1))+(A+V_i).adjoint p^i=0`。

观察 i.castSucc 对应原 p^(n−1)，末项是实际 p^N；没有要求 p 周期、低频、取于其它空间或仅为某个指定构造解。最终区域版本由真实 B.adjoint 范数改写而来，余项保持 `exp(−2d0 S)‖p^N‖²`。

`conforming_observation_control_uniform` 在有限维 X 下实际调用 `relaxed_control_of_observation`，给每个 y0 构造 `u : Fin N → Lp E 2 (ν.restrict ω)` 及完整 y:Fin(N+1)→X，满足 y⁰=y0 和

`dt⁻¹(y^(i+1)−y^i)+(A+V_i)y^(i+1)=B(u_i)`。

已复核该调用的物理 HUM 依赖：终值到伴随解的真实步逆、sqrt(dt) 控制嵌入、p^(n−1) 配对、真实前向解的终值表示均参与证明。`controlNorm` 是 `sqrt(dt∑‖u_i‖²)`；最终预算为 `‖u‖≤sqrt(C)‖y0‖` 和 `‖y^N‖≤sqrt(C)exp(−d0 S)‖y0‖`，与原可重命名的正 C(T,M) 一致。控制空间 U 不要求有限维；有限维只施于原离散状态 X，所以没有把真实 L²(ω) 错限为有限维。既有适定性还保证此 y 是对应初值和控制的真实唯一物理解。

## 32 项逐项核查

下表顺序与交付名单及固定 C046/T030 记录完全一致；每项都核对实际类型、证明体和递归公理。模块均在 `Carleman/Control/`。

| # | 完整声明 | 独立结论 |
| --- | --- | --- |
| 1 | `Carleman.Physical.multiplier_clm_norm` | PASS；真实乘法连续线性算子范数≤a.e. 界。 |
| 2 | `Carleman.Physical.multiplier_clm_symmetric` | PASS；实乘法在 L² 内积中对称。 |
| 3 | `Carleman.Physical.conformingPotential` | PASS；Γ b R 的实际构造。 |
| 4 | `Carleman.Physical.conformingPotential_apply` | PASS；对实际正交投影和 Lp 乘法的展开。 |
| 5 | `Carleman.Physical.conformingPotential_symmetric` | PASS；投影配对移除后使用乘法对称性。 |
| 6 | `Carleman.Physical.conformingPotential_norm` | PASS；投影收缩给准确 bound，未假定乘法保持 X。 |
| 7 | `Carleman.Physical.conformingPotential_form` | PASS；原势双线性积分形式。 |
| 8 | `Carleman.Physical.conforming_load_right_inverse` | PASS；真实 ΓI=Id。 |
| 9 | `Carleman.Physical.conforming_mass_norm` | PASS；包含映射等距，无完备性额外需求。 |
| 10 | `Carleman.Physical.conformingAmbientControl` | PASS；环境 L² indicator 后真实投影。 |
| 11 | `Carleman.Physical.conformingAmbientControl_norm` | PASS；实际算子收缩。 |
| 12 | `Carleman.Physical.conformingAmbientControl_adjoint` | PASS；实际伴随等于 indicator∘R。 |
| 13 | `Carleman.Physical.conforming_observation_integral` | PASS；实际环境伴随范数平方等于区域积分。 |
| 14 | `Carleman.Physical.restrictRegionLp` | PASS；限制测度下的真实 a.e. Lp 类。 |
| 15 | `Carleman.Physical.restrictRegionLp_ae` | PASS；代表识别只在限制测度 a.e. 进行。 |
| 16 | `Carleman.Physical.restrictRegionLp_norm_le` | PASS；真实限制范数收缩。 |
| 17 | `Carleman.Physical.restrictRegionLinear` | PASS；a.e. 商上的加法与数乘保持。 |
| 18 | `Carleman.Physical.restrictRegionCLM` | PASS；由常数 1 界构造连续线性限制。 |
| 19 | `Carleman.Physical.integral_inner_zeroExtend` | PASS；真实零延拓的区域配对恒等式。 |
| 20 | `Carleman.Physical.restrictRegion_adjoint` | PASS；限制的真实 Hilbert 伴随等于零延拓。 |
| 21 | `Carleman.Physical.zeroExtend_restrictRegion` | PASS；限制后零延拓恰为 indicator 乘法。 |
| 22 | `Carleman.Physical.restrictRegion_norm_eq_cutoff` | PASS；由真实等距性转为范数恒等式。 |
| 23 | `Carleman.Physical.restrictRegionCLM_norm` | PASS；限制算子范数≤1，允许零区域。 |
| 24 | `Carleman.Physical.conformingRegionControl` | PASS；实际区域 L²→X 控制算子。 |
| 25 | `Carleman.Physical.conformingRegionControl_apply` | PASS；实际 B=Γ∘zeroExtend。 |
| 26 | `Carleman.Physical.conformingRegionControl_adjoint` | PASS；真实 B*=restriction∘R。 |
| 27 | `Carleman.Physical.conformingRegionControl_adjoint_apply` | PASS；任意 x 的实际区域限制。 |
| 28 | `Carleman.Physical.conformingRegionControl_norm` | PASS；原 B 收缩条件内部证明。 |
| 29 | `Carleman.Physical.conforming_region_observation_norm` | PASS；真实区域和环境伴随范数严格一致。 |
| 30 | `Carleman.Physical.conformingRegionControl_pairing` | PASS；原区域控制双线性积分定义。 |
| 31 | `Carleman.Physical.conforming_physical_observation_uniform` | PASS / CONDITIONAL；内部清偿质量/势/右逆，保留统一周期 CE。 |
| 32 | `Carleman.Physical.conforming_observation_control_uniform` | PASS / CONDITIONAL；原量词、全物理轨迹及真实 L²(ω) HUM 控制。 |

## 依赖、版本和正式构建证据

已读取 [T029 / C045 条件观测桥独立验收](T029-local-acceptance.md) 与 [T026 / C042 物理 HUM 独立验收](T026-local-acceptance.md)。本次进一步直接读取其实际主入口、PhysicalObservationAssembly、PhysicalLoadCarleman、PhysicalHUM、PhysicalEquations，以及真实乘法、观察积分、零延拓和 TimeGrid 定义，检查上述本次实参是否满足接口。C045 的依赖相对基线没有数学变更；C042 的四模块相对其验收 SHA `549cde718bcf26f00b24f4a1493ee92b839f30b4` 也没有变更。此前两个条件性证明被组合使用，并未借此消除其尚未供应的周期 CE/具体实现义务。

基线至本次固定提交的数学变更只有上述五个新增模块及根导入；原稿、既有数学依赖、工具链、mathlib pin 和 CI 工作流没有改变。固定 `Carleman.lean` 显式导入全部五模块，`CheckAxioms.lean` 对全部 32 项执行实际 `#check` 和 `#print axioms`，并递归 `collectAxioms` 检查环境中还原私有名后的全部 Carleman 声明，只允许 `propext`、`Classical.choice`、`Quot.sound`。

固定本机日志 `/tmp/carleman-conforming-physical-full.log` 包含 `Build completed successfully (3505 jobs).`。本机公理副本 `/tmp/carleman-conforming-physical-local-axioms.txt` 为 1033532 字节，SHA-256 为 `b9e082f122c1915770027940160e775cc7f8fe75e4134a0ad315e769ff054f93`，32/32 项实际类型和公理输出完整；全局末行是 `Axiom audit passed for all 3597 Carleman declarations.`。没有未批准公理或 sorryAx。

通过 GitHub connector 独立读取 [main CI 39145512377 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39145512377/attempts/1)，确认 `head_sha=31d5e165a595849bc1c882523838aad69576b594`、`head_branch=main`、`event=push`、`status=completed`、`conclusion=success`。三个实际 jobs 均完成且成功：state-check（117728414081）、lean（117728414276）、dashboard / snapshot（117729211355）。实际 proof target、checked source 记录与两项证据上传步骤均成功。

同次 artifact 元数据中，`lean-ci-result`（12143680282）和 `lean-declaration-evidence`（12142982179）均绑定上述 head SHA。原始 `/tmp/carleman-conforming-physical-main-ci/result.json` 为 537 字节，SHA-256 为 `a49fd047829ed5356f7bb4a9797b13cfd1a20a50d8f40decc3e89e97d0b070ce`；实际内容为 PASS，`checked_sha=source_head_sha=31d5e165a595849bc1c882523838aad69576b594`，目标 Carleman，`finished_at=2026-10-18T16:35:30.206799+00:00`，Lean 4.35.0（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`），mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`。

正式远端公理文件 `/tmp/carleman-conforming-physical-main-axioms/axioms.txt` 同为 1033532 字节，SHA-256 为 `b9e082f122c1915770027940160e775cc7f8fe75e4134a0ad315e769ff054f93`。已实际逐字节比较确认与固定本机副本相同，并再次逐项核对 32 项类型、每项恰为三项标准基础公理、全局 3597 声明审计 PASS。未把其它 SHA 或后续源码的结果当作本次正式证据。

本次只写本验收报告，未修改数学源码、根导入、原稿、台账或覆盖表，未 commit/push。
