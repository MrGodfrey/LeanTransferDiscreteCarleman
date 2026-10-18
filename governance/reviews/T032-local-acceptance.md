# T032 / C048 独立本机验收

- `checked_sha`: `1cf3071913d460625411022e4ea16c8336399bf8`
- `base_commit`: `4223cdff025d68431b81dc2f3fb620e8bdc9ec6b`
- `reviewed_at`: `2026-10-18T17:01:46+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- 验收对象：四个新模块、下列全部 16 项显式声明；C048 可登记 `REVIEWED / CONDITIONAL`。
- 范围：原 Section 6 一致质量 Galerkin 代数、质量、载荷与观察接口，以及从剩余原解析数据导出真实物理观测和控制的条件结论。**本报告不提升 P011 / Proposition 6.1、P014 / Theorem 7.2 或 P015 / Theorem 7.3 为原文完成。**

审查使用固定提交导出的源码树，直接读取证明、展开类型及原 `paper/main.tex`，没有用执行者说明或 CI 成功代替数学核对。工作区中后续的 Galerkin 测试算子及 ProjectedHeat 草稿不属于本次验收。

## 原文与固定版本

对照原稿 Section 2 的 A1–A4、N1–N5，Section 6 一致质量 P1 构造（尤其原稿 1493–1506 行附近的实际 L2 内积、刚度配对、R/J/Q/G、零缺陷与区域控制），以及 Theorems 7.2–7.3 的尺度、观测和 HUM 结论。

原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。相对基线的源码差异只增加本次四个数学模块；最终模块的 Carleman 导入闭包有 288 个模块，其中 284 个既有模块逐字节未变。四个新模块全部由 `Carleman.lean` 直接导入。已验收 T031 的真实热尺度到物理结论入口及其依赖没有被本次修改。

## 16 项声明逐项结论

下表名称均加前缀 `Carleman.Physical.`；位置均为固定提交下 `Carleman/Control/` 的文件和行号。清单与 C048、T032 及提交的声明清单一致，无遗漏。

| # | 声明 | 固定源码位置 | 数学核对与结论 |
|---|---|---|---|
| 1 | `conformingEnergyLift` | `GalerkinStiffness.lean:17` | 将实际包含 X→V 与原能量值等价的逆复合；有限维性只给此线性映射的连续性。PASS。 |
| 2 | `conformingEnergyLift_value` | `GalerkinStiffness.lean:20` | 提升后取值精确返回原 X→V 包含，没有换掉函数或 Sobolev 实现。PASS。 |
| 3 | `galerkinStiffness` | `GalerkinStiffness.lean:24` | 拉回原有界形式，再用 X 继承的真实 L2 内积之 Riesz 逆构造 X→X。PASS。 |
| 4 | `galerkinStiffness_form` | `GalerkinStiffness.lean:28` | 对全部 x,y∈X，精确证明 `(Ah x,y)_L2 = a(Rx,Ry)`。PASS。 |
| 5 | `galerkinStiffness_symmetric` | `GalerkinStiffness.lean:36` | 由原形式对称和精确配对推出实际算子对称；在此完备实 Hilbert 空间中对应其 Hilbert 伴随等于自身。PASS。 |
| 6 | `galerkinStiffness_nonneg` | `GalerkinStiffness.lean:45` | 将原形式的强制性应用于实际能量提升，得到全部状态的非负性；不是输入的刚度假设。PASS。 |
| 7 | `galerkinStiffness_unique` | `GalerkinStiffness.lean:51` | 任意具有同一形式配对的连续线性 A 与构造值相等；以全部测试 y 的内积判等。有限维下也覆盖任意线性算子。PASS。 |
| 8 | `galerkinStiffness_defect_zero` | `GalerkinStiffness.lean:60` | 对实际 reconstruction.R 的配对等式，缺陷是类型正确的零双线性形式。PASS。 |
| 9 | `conformingReconstruction_injective` | `GalerkinNumericalData.lean:14` | R 为子空间包含，单射性内部证明。PASS。 |
| 10 | `conformingReconstruction_G` | `GalerkinNumericalData.lean:18` | 对实际 J=正交投影、R=包含证明 JR=Id。PASS。 |
| 11 | `conformingReconstruction_QH` | `GalerkinNumericalData.lean:24` | 环境 L2 中的 QH 精确等于包含复合正交投影；没有把 V 值的 Q 与环境值混淆。PASS。 |
| 12 | `conforming_weighted_observation` | `GalerkinNumericalData.lean:29` | 对任意有界乘子 σ、可测观察集及全部 x，真实区域加权观察等于实际 ambient 控制伴随的 σ 范数。PASS。 |
| 13 | `galerkinNumericalData` | `GalerkinNumericalData.lean:52` | 仅给 N3/N4 后构造原 NumericalData：实际刚度、零缺陷、两重构比较、普通载荷 lift 及观察兼容，公共 Cnum=1。PASS。 |
| 14 | `GalerkinHeatData` | `GalerkinHeatData.lean:28` | 四字段仅为原 AllowedFamily、N3、N4、真实弱周期轨迹的连续 A4；无离散 CE、观测或控制结论字段。PASS。 |
| 15 | `GalerkinHeatData.toConforming` | `GalerkinHeatData.lean:44` | 原样传递解析数据并内部构造 NumericalData，输出同一 X/g/w 的实际刚度、缺陷零和 Cnum=1。PASS。 |
| 16 | `galerkin_heat_observation_control_uniform` | `GalerkinHeatControl.lean:28` | 内部选择构造的刚度及其对称、非负证明，得到完整物理观测、真实区域控制及全部前向状态；原尺度和常数次序保持。PASS。 |

## 刚度、质量与常数

`OriginalForm.scalarForm` 是原 Sobolev 能量形式通过 `valueEquiv.symm` 的精确表示；`valueEquiv` 的值为实际 L2 函数。`conformingEnergyLift` 因而没有另造能量或更换原形式。Riesz 映射使用的是 X 作为实际 L2 子空间继承的内积，不是能量内积，也不是另给的矩阵或抽象刚度。

有限维能量提升的算子范数可能依赖 X。本次证明只用其连续性形成有界双线性映射并定义刚度，没有声称该范数统一有界，没有把它作为常数 1，也没有将它传给最终统一估计。`galerkinStiffness_form` 消去提升后，剩余调用只用精确配对、对称和非负性。

常数 1 来自另一组实际恒等式：R 是 L2 包含，J 是 L2 正交投影，G=Id；Γ=J，普通载荷 lift=Id，右逆 I=包含，ΓI=Id。状态加权范数按同一乘子定义，故上下重构比较和普通 lift 比较是等式。这里的普通载荷 lift 不能与上述 Sobolev 能量提升混同。`NumericalData` 本身不单列全部 N1 的单射/正性字段或物理右逆字段；这些由本次独立定理及既有实际包含/投影定理提供，并在最终调用中使用。

零双线性缺陷的绝对值为零，利用 `ErrorScales.ηA_nonneg` 即满足登记的缺陷上界。特别允许 ηA=0，不要求正缺陷。最终仍保留原误差阶 `aE ≤ Cap*h`、`a₀+ηA ≤ Cap*h²`；没有把实际零缺陷误写成额外可调整的刚度。

`conforming_weighted_observation` 对所有有界乘子成立，故对全部允许权、全部实际时刻均可用。它通过已证明的实际 ambient 伴随等于 χ_ω 乘法识别，观察平方是原区域积分。最终物理入口使用的则是 `conformingRegionControl : L2(ω) → X`：其实际定义为正交投影复合限制映射的伴随，即零延拓后投影；伴随精确等于限制 `x|ω`，且配对为 `∫ω ux`。从 ambient 观察到区域观察使用已证明的范数恒等式，没有冒充一个任意命名的 Bstar。

## 剩余解析数据、时刻与权族

N3 的两个字段量化原闭时间区间的每个 t 和原完整算子域的每个 v，使用真实加权 Sobolev/参数范数和 L2 误差。N4 保留真实时间导数、端点周期性、对称非负、时间变化界和 `Csuper*h*qmax` 超逼近；本阶段未把 N4 构造出来。两者均要求两种空间权符号及原 `|τ|≤τStar`，没有只检查节点、单个符号或缩小允许指数范围。

连续字段量化全部 `Orientation` 和真实 `PeriodicWeakTrajectory`，载荷为实际 `s.sign*U' + A U`；连续能量、弱导数及观察来自既有真实 Sobolev/L2 几何。最终要求对完整 `PhysicalQClass` 中每个 `w.max≤Smax` 的权供应上述数据。没有添加目标误差、离散 CE、物理观测、控制存在或轨迹可积性作为替代前提；原解析正则性、椭圆估计、权导数/交换子界与连续 A4 仍明确保留。

原连续形式仍是一般 `OriginalForm`。本次没有证明它就是特定区域的 Dirichlet 梯度形式或其连续热 Carleman 估计，也未构造具有原局部网格分级条件的 P1 子空间、其 N3 或 N4。原 Section 6 的这些实质实例义务仍在，不能用“任意有限维 X≤V”的条件定理替代它们。

## 最终物理结论与统一量词

最终定理先固定原连续背景、解析常数和误差阶系数，再选择 `κ,h0,Δ0,Cb,d0>0`，随后才量化 `T>0,M≥0` 并选择正的 `Cphys(T,M)`。X、有限维实例、网格、h、误差数据、允许权、势序列、伴随轨迹和初值均在 Cphys 之后。代码在实例化 X 之前以 Cnum=1 调用 T031，因此没有空间维数、节点数、能量提升范数或网格相关常数潜入统一常数。

尺度严格为 `Smax = κ min(h^(-4/5),dt^(-2/5))`。`qb = Cb*(qc+T⁻¹+M^(2/3))`，以及 `h≤h0`、`dt≤Δ0`、`dt≤T/12`、`dt*M≤1/2`、`16qb≤Smax≤qb*T/(4dt)` 均保留。没有把 T 预先固定再选 κ/Cb/d0，也没有要求 M>0。

观测适用于全部 `p : Fin(N+1)→X`，方程使用真实 Hilbert 伴随 `(Ah + Π_h(b_i·)).adjoint`。观测项是 `dt Σ ‖B* p^(n−1)‖²`，终端项是 `exp(-2*d0*Smax)‖p^N‖²`。前向结论量化任意 `y0∈X`，存在 `u : Fin N→L2(ω)` 和完整 `y : Fin(N+1)→X`，满足初值及逐步真实后向 Euler 方程；控制范数为 `sqrt(dt Σ‖u^n‖²)`，控制代价和终值界分别为 `sqrt(Cphys)‖y0‖` 与 `sqrt(Cphys)exp(-d0*Smax)‖y0‖`。这与原文允许重命名的正 C(T,M) 一致。没有谱截断、状态子集或周期端点限制施加在物理轨迹上。

## 构建、真实 CI 与公理

独立读取 GitHub 实际 run `39147219355`、attempt 1：main、push、head SHA 为本报告固定 SHA，状态 `completed/success`。`state-check`、`lean`、`dashboard / snapshot` 三个 jobs 均 `success`。Lean job 的 pinned-toolchain、proof build、记录 checked source、上传结果及公理步骤均成功。

- [同次真实 CI](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39147219355/attempts/1)
- 原始结果：`/tmp/carleman-galerkin-physical-main-ci/result.json`；`status=PASS`，`checked_sha=source_head_sha=1cf3071913d460625411022e4ea16c8336399bf8`，`finished_at=2026-10-18T16:57:42.197316+00:00`，target 为 `Carleman`。
- Lean `4.35.0`，mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`，与固定源码的 pin 一致。
- 同次结果 artifact ID `12144215050`，声明/公理 artifact ID `12143717216`，均属于 run `39147219355` 和同一 head SHA。
- 远端公理原始文件：`/tmp/carleman-galerkin-physical-main-axioms/axioms.txt`，1,096,667 bytes；SHA256 `d0dac30c856dddb815f0a2379867302b37765b3a65bb486f31ab62874ea26b44`，与固定本机副本逐字节相同。
- 本机 `/tmp/carleman-galerkin-physical-full.log` 记载 `Build completed successfully (3513 jobs)`；同次远端公理产物末行实际为 `Axiom audit passed for all 3766 Carleman declarations.`

逐项检查了本次 16 项的展开类型和 `#print axioms`，全部仅依赖 `propext`、`Classical.choice`、`Quot.sound`。固定 `tools/CheckAxioms.lean` 的全局审计遍历环境内所有经 `privateToUserName` 归属 Carleman 的声明，并用 `collectAxioms` 递归收集依赖，只允许上述三项正常基础公理。无 sorry 或新增未清偿数学公理。实际 CI 构建 root target 并执行这一审计；并非仅依赖 16 行打印或成功字符串。

## 验收决定

**C048：PASS，可升级为 REVIEWED，scope 必须保留 CONDITIONAL。** 本次 16 项没有发现需要修复的数学或量词缺陷。该决定覆盖真实 Galerkin 代数/质量/载荷/观察接口及上述条件物理结论；不声称完成具体 P1/FD 实现、原 N3/N4 的网格证明、连续 Dirichlet 热实例或相应论文覆盖项。

本次仅写此验收报告；没有修改数学代码、台账、原稿或 root 导入，没有 commit/push。
