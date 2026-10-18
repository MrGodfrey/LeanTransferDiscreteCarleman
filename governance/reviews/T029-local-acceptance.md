# T029 — 实际周期载荷 CE 到物理观测条件桥独立本机验收

- `checked_sha`：`f84745210c4ee35c2dd924f9c6ff04788047c28d`
- `base_commit`：`fba691ef4acce0af1d303f19cae7ceaccfe7eb20`
- `reviewed_at`：`2026-10-18T16:27:21+00:00`（UTC）。
- reviewer：独立本机验收 Agent `/root/accept_spatial_foundations`，非 T029 执行者。
- target：C045；五个新模块、全部 20 项显式声明；原 Theorem 7.2 `prop:physicalO` 的实际载荷、势吸收和观测组装条件桥。
- `result`：**PASS**（实际载荷 CE 到物理观测的完整条件桥）。
- `axiom_check`：**PASS**（同 SHA 真实 CI，3524 项递归审计）。
- scope：**CONDITIONAL**。
- `extra_hypotheses`：`["实际Lp重构上的统一周期载荷Carleman估计及具体质量/载荷/观测接口仍须由原实现供应"]`。

独立读取固定提交导出树 `/tmp/carleman-observation-review-f847` 的五个模块全部证明、实际 elaborated 类型和关键依赖；对照原 `paper/main.tex` Theorem 7.2（1827 行起）和证明 Steps 1–3（1855–2021 行）。同时核对固定 MATH_SPEC T029 的条件范围。执行者说明不替代源码、原文或依赖审查；本报告不审核后续工作树代码。

## 条件结论与原文范围

最终 `physical_observation_uniform_of_load_carleman` 在真实物理 `AdjointEquation`、非负自伴 A、自伴且算子范数≤M 的 V_i 下，对所有完整 N+1 节点伴随轨迹 p 给出

\[
\|p^0\|_X^2\le C(T,M)\left(dt\sum_{i=0}^{N-1}\|Bstar(p^i)\|_{L^2}^2+
 e^{-2d_0S}\|p^N\|_X^2\right).
\]

它真实构造原正弦权与具体截断，证明势吸收、观测去权、端点余项和初值恢复，未把目标物理观测不等式作为输入。p 为任意满足原真实 Hilbert 伴随方程的全轨迹，没有子空间、低频、指定构造解或周期轨迹限制。X 只要求完备实 Hilbert 空间，包含原有限维 X_h；本层不使用新的适定性结论。

显式未清偿的输入是：整个周期状态/实际 Lp 载荷空间上的 `PhysicalLoadCarleman`；R 的双向质量比较；ΓI=Id；Γ 与乘法势的兼容；所有允许权下 I 的统一加权稳定性。这里 R、I、Γ 均为明确线性映射，具体原数值数据是否实现这些类型和恒等式仍须另行供应。

**Bstar 目前只是 `X →ₗ[ℝ] Lp E 2 ν` 的显式线性观测映射。它没有被证明等于某个实际控制算子的 Hilbert 伴随。** 新结论的观测范数正是这个 Lp 像的范数；要得到原 `‖B_h^*p‖_(U_h)`，还需真实数值观测的等距或有界识别，及其常数统一性。S 在本桥中是满足原双边约束的抽象允许尺度，原 h、dt 产生的 S_(h,dt) 与周期 CE 的供应也仍属后续实例工作。因此只能将 C045 升为 `REVIEWED/CONDITIONAL`，P014 不得因此提升。

## 真实乘法势、截断 r 与载荷负号

`weighted_potential_bound` 在 mathlib 的 a.e. 商空间 `Lp E 2 ν` 上证明 `‖σ(bu)‖≤M‖σu‖`。所用 `BoundedMultiplier.map` 先证明乘积属于 MemLp，再形成实际 Lp 元素；`mul_map` 用 Lp.ext 和 a.e. 代表恒等式证明复合乘法。新增证明从 `|b|≤b.bound≤M` 得 `|σb|≤M|σ|`，调用真实加权 seminorm 比较。没有对 Lp 等价类进行不合法逐点识别，也没有将未证明的势加权界藏在输入中。`b.bound≥0` 且 `b.bound≤M` 已保证这个辅助引理的 M 非负；最终入口仍显式要求 M≥0。

实际周期状态为 `z_i=χ_i p^i`，实际余项为

`r_i=((χ_(i+1)−χ_i)/dt) • p^(i+1)`。

`physicalCutoffLoad` 精确定义 `f_i=−b_i.map(R z_i)−I r_i`。利用 Γ 线性、`Γ(b_i.map(Rx))=V_i x` 和 `Γ(Ix)=x`，其 Γ 像严格为 `−V_i z_i−r_i`。`physical_cutoff_load_equation` 接到既有 `concrete_cutoff_residual`，得到原 `D_-z_i+A z_i=Γf_i`，两个负号均正确。

直接复核上游截断接口：i.castSucc 对应原 p^(n−1)，i.succ 对应 p^n；末格余项使用真实 p^N。只有 χp 的两端先证明为零后才使用周期 next；原 p 本身并未周期化。`AdjointEquation` 保留实际 `.adjoint`，通过 A+V_i 的自伴性识别原反向递推。

`physical_cutoff_load_bound` 用实际 seminorm 三角不等式、势乘法界及显式右逆加权界，再以 `(a+b)²≤2a²+2b²` 得

`‖θ_i f_i‖² ≤ 2M²‖θ_i Rz_i‖²+2CI²‖θ_i Rr_i‖²`。

它保留所有交叉项所需系数，余项 p^(i+1) 使用原 θ_i，未错移时间权。

## 真实周期 CE、32CCE 预算与观测去权

`physicalWeightedSq` 是 `dt∑‖θ_i v_i‖²`，`physicalWeightedCubeSq` 是 `dt∑q_i³‖θ_i v_i‖²`，其中 θ_i 是实际 `ρ.multiplier w 0`。`PhysicalLoadCarleman` 全称量化任意周期状态 z 和任意 Lp 载荷 f，仅在实际 `D_-z+Az=Γf` 下输出 Rz 的 q³ 加权 L² 能量界。它是本桥实际需要的质量项估计，**不是已经由本阶段从原完整 Carleman 能量推导出来的结果**；作为明确的输入，范围记录准确。

`physicalWeight_lower_half` 从 δ∈(0,1/16] 得 `sqrt(1+δ²)≤2`，故原真实正弦权 q≥qb/2。`physical_potential_budget` 使用原 `qb=Cb(qc+T⁻¹+M^(2/3))` 及已证 `qb³≥Cb³M²`。由 Cb≥1 和 Cb≥32CCE，

`Cb³≥Cb≥32CCE`，`q³≥qb³/8≥4CCE M²`，

因此 `2CCE M²≤q³/2`。常数 32 的作用完整可追踪；没有把 Cb³ 与 Cb 或 q 的立方系数误换。证明从未除以 M 或 CCE，M=0 和 CCE=0 均被覆盖；原非负 M 的 2/3 实幂在零处也由上游真实 rpow 恒等式处理。

`cutoff_carleman_absorb` 将上面实际构造的 (z,f) 代入显式周期 CE，再把载荷平方预算按 dt 求和。节点半能量条件给 `2CCE M²‖θRz‖²_(l²_dt)≤E/2`；移项后精确得到

`E ≤ 4CCE CI²‖θRr‖²_(l²_dt)+2CCE‖q^(3/2)θBstar z‖²_(l²_dt)`。

其中 E 就是同一个 Rz 的真实 q³ 加权能量。目标预算和吸收后的能量界没有在最终入口额外假设；最终由前置 Cb 的选择内部供应。

`cutoff_observation_budget` 对真实线性 Bstar 使用 `Bstar(χ_i p^i)=χ_i Bstar(p^i)` 和已证 0≤χ≤1，先给未加权范数缩小。然后用实际空间权上包络及 `q³ exp(−2rstar q)≤6/rstar³`，得到

`‖q^(3/2)θBstar z‖²_(l²_dt) ≤ (6/rstar³) dt∑‖Bstar(p^i)‖²`。

观测位置为原 p^(n−1)，常数不含 S、节点数、T 或额外 dt；Bstar 的线性性质真实使用，但尚未建立其控制伴随身份。

## 正常数、质量界方向与余项指数

令 `c_end=physicalEndpointRate rstar=2rstar/sqrt(1+9π²)>0`，定义

`K=exp(−4ρ.bound qb)(T/6)exp(−4MT)>0`，

`Krem=10Cmass/(c_end qb T) exp(4MT)≥0`。

实际端点余项调用上质量界 `‖Rx‖²≤Cmass‖x‖²`；初值恢复调用相反的下质量界 `‖x‖²≤Cmass‖Rx‖²`，方向正确。既有加权预算的实际输入均为同一 p、L_i=A+V_i、q 和截断宽度 a=(qb/S)T。原真实伴随能量在内部使用，没有将能量稳定性或目标初值恢复作新的外部假设。

所接的已证结果是

`‖θRr‖²_(l²_dt)≤Krem exp(−c_end S/2)‖p^N‖²`，

`K‖p^0‖²≤Cmass E`。

端点系数 10 来自已验收的安全过渡窗口常数 5 与真实多项式指数吸收系数 2/c_end；它只放大固定前因子。初值恢复以 q³≥1 使用比原中间展示式更保守的下界，省去 qb³ 仍保留正的、与网格和 S 无关的恢复因子。

`physical_observation_of_load_carleman` 合成这些实际预算，选

`C=(Cmass/K)(4CCE CI² Krem+2CCE(6/rstar³)+1)`。

T>0、qb≥2、rstar>0、Cmass>0 给所有分母严格正。最后 +1 保证 C>0，包括 CCE=0；CI²≥0，不需要除以 CI。非负的观测项和终端项允许将两系数合并到此共同常数。没有遗漏第二次质量系数，也没有引入隐藏的节点数、S 或维数依赖。

`d0=c_end/4>0` 先行选择，最终用准确代数恒等式 `−2d0 S=−(c_end/2)S` 改写为原要求的 `exp(−2d0 S)`。这个选择满足原 `2d0<c_end`；余项中的 S 已在上游真实指数预算中吸收，不是直接丢弃。

## 量词顺序和剩余实例义务

最终实际类型 先固定 Ω、E、ν、ρ 及 β、qc、CI、CCE、Cmass、rstar 的统一原始数据和界；随后存在 Cb、d0；然后对任意 T>0、M≥0 存在正 C；最后才量化 X、g、S、A、V、R/I/Bstar/Γ、乘法势 b、所有数据兼容和所有 p。因此 Cb/d0 不依赖 T、M、h、dt、S；C 可依赖 T、M 和固定界，但不依赖 X、网格、S、具体算子/映射/势或轨迹。

Cb 由 `physical_qclass_uniform β qc (max 2 (32CCE))` 取得，故同时满足 Cb≥2、Cb≥32CCE、Cb≥2π/β。它内部构造准确 `qmax=S` 的原正弦权与完整 qclass：真实导数、二阶导数及三个阶次端点匹配。输入的统一 CE/右逆包要求对所有满足这一 qclass 且 w.max≤S 的 w 成立，证明仅在构造的实际 w 上调用。没有索取额外最终观测条件，也没有扩大数值实例义务后声称已经清偿。

原几何限制 `16qb≤S≤qb T/(4dt)`、dt*M≤1/2、dt≤T/12 均明确保留。S 正、δ∈(0,1/16]、a>0 和 dt≤a/4 由这些条件内部推出。原正弦权、势二次型下界和半能量预算都由实际 A/V 和参数输入生成。完整原定理所需的热连续 CE、P1/FD、h0/Δ0/热尺度、质量/右逆及实际观测对应关系仍需后续验收；本桥没有声明对 T 统一的原物理常数，C(T,M) 对 T 的依赖是原文允许的。

## 全部 20 项显式声明

模块路径相对于 `Carleman/Control/`。每项均核查固定源码、实际 elaborated 类型、原文用途与递归公理。

| # | 完整声明 | 固定模块及行 | 独立核查结论 |
| --- | --- | --- | --- |
| 1 | `Carleman.Physical.weighted_potential_bound` | `PhysicalPotentialLoad.lean:12` | PASS；真实 a.e. Lp 乘法势的加权 M 界。 |
| 2 | `Carleman.Physical.physicalCutoffLoad` | `PhysicalPotentialLoad.lean:21` | PASS；原 −bRz−Ir，实际 cutoffState 与 remainder。 |
| 3 | `Carleman.Physical.physical_cutoff_load_equation` | `PhysicalPotentialLoad.lean:26` | PASS；Γ 兼容、两个负号及原真实伴随截断残差。 |
| 4 | `Carleman.Physical.physical_cutoff_load_bound` | `PhysicalPotentialLoad.lean:37` | PASS；平方预算 2M² 和 2CI²，无交叉项遗漏。 |
| 5 | `Carleman.Physical.physicalWeight_lower_half` | `PhysicalPotentialAbsorption.lean:9` | PASS；原真实正弦权全时下界 qb/2。 |
| 6 | `Carleman.Physical.physical_potential_budget` | `PhysicalPotentialAbsorption.lean:19` | PASS；32CCE 的前置 Cb 预算给准确半能量条件，包含零势。 |
| 7 | `Carleman.Physical.physicalWeightedSq` | `PhysicalLoadCarleman.lean:15` | PASS；真实 dt 加权 Lp 平方和。 |
| 8 | `Carleman.Physical.physicalWeightedCubeSq` | `PhysicalLoadCarleman.lean:19` | PASS；原 q³ 乘真实加权 Lp 平方和。 |
| 9 | `Carleman.Physical.PhysicalLoadCarleman` | `PhysicalLoadCarleman.lean:23` | PASS／CONDITIONAL 接口；全周期 z/f 与实际载荷方程，尚待实例供应。 |
| 10 | `Carleman.Physical.cutoff_observation_budget` | `PhysicalLoadCarleman.lean:30` | PASS；真实 χ、线性 Bstar、空间指数去权，常数 6/rstar³。 |
| 11 | `Carleman.Physical.cutoff_carleman_absorb` | `PhysicalLoadCarleman.lean:52` | PASS；实际 CE 应用并吸收，最终系数 4CCE CI² 与 2CCE。 |
| 12 | `Carleman.Physical.physicalEndpointRate` | `PhysicalObservationAssembly.lean:12` | PASS；原 c_end=2rstar/sqrt(1+9π²)。 |
| 13 | `Carleman.Physical.physicalEndpointRate_pos` | `PhysicalObservationAssembly.lean:14` | PASS；rstar>0 时严格正。 |
| 14 | `Carleman.Physical.physicalInitialFactor` | `PhysicalObservationAssembly.lean:17` | PASS；真实中央初值恢复因子，无 S/网格依赖。 |
| 15 | `Carleman.Physical.physicalInitialFactor_pos` | `PhysicalObservationAssembly.lean:19` | PASS；T>0 给正除数。 |
| 16 | `Carleman.Physical.physicalRemainderFactor` | `PhysicalObservationAssembly.lean:23` | PASS；准确 10Cmass/(c_end qb T)exp(4MT)。 |
| 17 | `Carleman.Physical.physicalObservationConstant` | `PhysicalObservationAssembly.lean:26` | PASS；质量、恢复、余项、观测系数的完整合成。 |
| 18 | `Carleman.Physical.physicalObservationConstant_pos` | `PhysicalObservationAssembly.lean:30` | PASS；+1 保证 CCE=0 时仍严格正，所有分母合法。 |
| 19 | `Carleman.Physical.physical_observation_of_load_carleman` | `PhysicalObservationAssembly.lean:45` | PASS／CONDITIONAL；实际全轨迹、半指数端点余项与完整观测组装。 |
| 20 | `Carleman.Physical.physical_observation_uniform_of_load_carleman` | `PhysicalObservationUniform.lean:15` | PASS／CONDITIONAL；Cb/d0、C 的原量词次序及 exp(−2d0S)，实例义务明确保留。 |

## 固定版本、依赖与公理证据

20 项名称及顺序与固定 C045/T029 台账和 `/tmp/carleman-load-observation-declarations.json` 完全一致，五模块均由固定 root 导入。五模块本地 import 闭包含自身共 42 模块，根闭包共 303 模块。相对 base `fba691ef4acce0af1d303f19cae7ceaccfe7eb20`，数学新增仅这五模块与 root 导入，闭包内既有数学依赖、工具链及 mathlib pin 未变化。

已读取固定树中的 [T027 独立验收](T027-local-acceptance.md) 和 [T028 独立验收](T028-local-acceptance.md)；本次另行直接复核真实 BoundedMultiplier/Lp 代数、物理截断残差、qclass/原 qb、空间权、端点与中部加权能量的实际接口和本次调用实参。原稿 SHA256 仍为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

本机 `/tmp/carleman-load-observation-full.log` 记录 `Build completed successfully (3500 jobs).`。固定本机审计 `/tmp/carleman-load-observation-local-axioms.txt` 为 1009233 字节，SHA256 为 `23ecf1ee980361f7cb53f5f2e311a1cf44627d2200758c4c0bd86c7712357e86`，末尾为 `Axiom audit passed for all 3524 Carleman declarations.`。已逐项实际读取 20 项 elaborated 类型和公理输出，均恰为 `propext`、`Classical.choice`、`Quot.sound`；最后一项的公理输出换行显示，已按完整集合核对。全环境递归 `collectAxioms` 覆盖还原私有名后的 Carleman 声明，拒绝任何非允许公理。没有 sorryAx 或新增数学公理；显式 CE 和兼容输入是条件命题的前提，未被隐藏为公理。

通过 GitHub connector 独立读取 [main CI 39144611467 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39144611467/attempts/1) 的实际 run 与 jobs，确认 `head_sha=f84745210c4ee35c2dd924f9c6ff04788047c28d`、`head_branch=main`、`event=push`、`status=completed`、`conclusion=success`。`state-check`（117725804606）、`lean`（117725805314）、`dashboard / snapshot`（117726389384）均成功；实际 proof target 构建、checked source 记录和两项证据上传步骤均成功。

实际读取同次下载的 `/tmp/carleman-load-observation-main-ci/result.json`：`status=PASS`，`checked_sha=source_head_sha=f84745210c4ee35c2dd924f9c6ff04788047c28d`，target=`Carleman`，`finished_at=2026-10-18T16:22:57.037463+00:00`。原始 result 文件 SHA256 为 `1bb3a4a67fb4b35aef0909c7a6c9a7ba108dbfbc1616b61c54c20777904f9082`。Lean 4.35.0（提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）和 mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 与固定源码 pin 一致。

正式公理证据为同次 `/tmp/carleman-load-observation-main-axioms/axioms.txt`，1009233 字节，SHA256 为 `23ecf1ee980361f7cb53f5f2e311a1cf44627d2200758c4c0bd86c7712357e86`。已实际逐字节比较确认与固定本机副本相同，再次按全部 20 项完整名称核对正式产物的实际类型和三项正常基础公理集合，并确认 3524 声明递归审计通过。没有混用后续工作树或其它提交产物。

## 结论边界

固定 SHA 下，20 项声明的独立数学语义、真实载荷/截断/吸收/观测连接、同 SHA 实际构建和递归公理审计均为 **PASS**，未发现需要修正的数学缺陷。C045 可升级为 `REVIEWED`，scope 必须保持 `CONDITIONAL`，保留其显式周期 Lp CE 和数值接口供应义务，并绑定本报告及同 SHA 构建证据。

本次不能提升 P014 / 原 Theorem 7.2。尤其不能把当前显式 Bstar 自动登记为原实际控制伴随，不能宣称连续热 CE、具体 P1/FD、原网格尺度实例、控制或全文已经完成。

本次只写本报告，未改数学源码、root、台账、覆盖表或原稿，未 commit/push。
