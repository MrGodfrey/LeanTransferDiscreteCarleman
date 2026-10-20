# T210 / C226 独立本机验收

- checked_sha: `3725f002ad895342683989c46d052625da5f57ba`
- base_commit: `bf85c15d7a923ca6dce0a5d5fdf10f31c28e413b`
- reviewed_at: `2026-10-20T04:23:42+00:00`
- reviewer: independent local Agent `/root/accept_spatial_foundations`
- result: **PASS — 4/4 定理，无阻断缺陷**
- axiom_check: **PASS**
- scope: **AUXILIARY；17/26 不变，P021 不提升**
- evidence_source: **local**；按当前简化协议核对实际本地构建、公理与固定源清单，未查询或声称远端 CI。

独立读取固定 Git 对象中三模块全部证明、四项完整展开类型、分析/MATH_SPEC/台账，并对照原稿 `paper/main.tex:2389–2415` 的弱方程及连续端点恢复。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。全文读取 T209 冻结报告 `b7d5dcfc6b9efb49b61c2226df0ce257f344a4fa`；另直接重读其实际平均势乘法/弱配对、P1 全节点有限测试一致性，以及本批调用的原投影初值收敛、完整状态预算、区域支撑、有限产品测试、弱强配对和连续端点/对偶导数接口。

## 四项声明

源码均为固定 SHA 的 `Carleman/Control/` 模块；下列名称省略公共前缀 `Carleman.`。raw 行号指 `/tmp/carleman-t210-p1-weak-limit-local-axioms.txt`。

| 模块:行 | 实际声明 | raw 行 | 结论 |
| --- | --- | --- | --- |
| RegionalTimeControl:15 | `regional_time_control_norm` | 39061 | **PASS**：实际区域零延拓时间重构的 L² 范数精确等于原物理 `controlNorm`。 |
| RegionalTimeControl:25 | `regional_time_control_supported` | 39069 | **PASS**：该真实 Bochner 重构几乎每个时刻属于原闭区域支撑子空间。 |
| P1WeakLimitIdentity:18 | `full_p1_finite_test_weak_limit_identity` | 39079 | **PASS**：原六项恒等式对任意完整有限测试取极限，保留同一 b/Y/U/y0。 |
| P1WeakControlLimit:18 | `full_p1_weak_control_limit_null_state` | 39197 | **PASS**：每个给定控制弱极限得到一个完整能量 Y，满足原预算、全部有限弱身份及真实连续初终迹/StrongDual 方程。 |

## 数学核对

**原区域控制。** `restrictRegionCLM ω` 的真实 Hilbert 伴随在明确的 `MeasurableSet ω` 前提下等于实际零延拓；零延拓保范数。时间胞元重构范数精确为 `sqrt(dt·∑ᵢ‖uᵢ‖²)`，因此第一个定理保留原区域控制费用，并非投影到状态空间后可能更小的范数。第二个定理先由真实零延拓 a.e. 公式给各胞元控制属于 `supportedRegionSpace ω`，再用时间重构的实际有限示性和及子空间加法封闭性给几乎每个时刻的成员身份。该空间实际定义为补集限制算子的核。没有任意代表的逐点支撑断言、不可数 a.e. 交换或更小控制空间假设。

**六项原方程的极限。** 采用完整 `M.conformingSpace (dirichletSubspace S)`、原 Galerkin 刚度、原 L² consistent mass，以及 `P_X(b_i·)` 势与 `P_X K` 控制。这里 `b_i=fixedTimeCellPotential ... b i` 已是同一个原时空 b 的真实时间胞平均。调用 T208 的精确身份：负时间差商项、正梯度项、正势项，等于正初值项加正控制项减终值项；状态为 `i.succ`，测试为 `i.castSucc`。投影仅在与 X 内测试的配对中消去，没有使用投影与乘法交换。

同一 `p1FiniteTestSequence` 提供前层值、后减前除 dt 的差商、完整弱梯度和两个端点。前三者通过真实 P1/时间一致性强收敛；弱状态/梯度/控制分别与这些强测试配对。势项通过实际 Bochner→产品线性等距映射 J、原平均势乘法身份及强测试传递到 `〈b·J(Yv),φ〉`；`finiteTensorTestMultiplier_eq_product` 识别的确为同一整个有限和。未输入 J 满射、状态强收敛、势光滑性或另一独立势。

初值项由原 L² 初值强收敛和实际节点 k=0 测试强收敛得到；终端物理状态范数趋零等价于其原 L² 包含像趋零，与 k=N 测试强收敛配对后消失。没有把终端测试强设为零，也没有把最后一个前层节点误当 T。有限测试允许任意 Fintype（含空集），时间系数及其实际导数仅在 `[0,T]` 连续，并保留 `HasDerivWithinAt`；两端不受限制。辅助定理明确输入全测试弱极限与场预算，不把这些前提隐藏为已构造。

**给定 U 与同一个 Y 的量词。** 最后定理先固定原 U 及其对全部 Bochner L² 测试的弱收敛，再调用实际方程的紧性结果，获得一个 Y 和一个严格递增 χ；`intro q η f ψ ...` 位于这一存在构造之后。因此所有有限测试共用同一个 Y、值场和全梯度场，χ 不依赖测试。U 的弱收敛通过 `StrictMono.tendsto_atTop` 沿 χ 保留，没有改选或重新命名为另一控制极限。返回的完整能量预算仍为 `stateTimeEnergyBound T M ‖y0‖ CU`。

原初值为 full P1 空间的实际 L² 正交投影。收缩性内部给初值预算；对全部 L² 初值的强收敛由真实紧支测试稠密性、节点插值误差与正交最佳逼近内部供应，不要求 y0 光滑或 H¹₀。原 ForwardEquation、真实平均势界 `b.bound≤M`、`dt*M≤1/2` 和原控制费用界内部给完整状态预算。用于弱强配对的 CE/CG 取固定原值/梯度 `compLpL` 算子范数乘此预算；它们不依赖离散网格或 χ，不使用离散提升算子范数，也不替换最终返回的预算。

**真实连续端点与方程。** 已展开 `FiniteDirichletControlIdentity` 与 `DirichletNullControlState`，后者不是空标签：它要求一个 `q` 在 `[0,T]` 上 H 连续，与同一 Y 的原值几乎处处相等，且 `q(0)=y0`、`q(T)=0`；同时包含原 pivot 在实际 `StrongDual ℝ V` 中的分布时间导数等式。此结论由刚证明的全部有限弱身份调用真实连续代表/端点及对偶导数定理得到，未输入 Y 连续或 Lp 代表端点。旧接口经原 V 测试稠密性与实际载荷配对识别 `U−Ay−by`；端点由不限端点测试、真实标量 Green 公式及 H 稠密性识别。所有对象仍为同一 b/Y/U/y0。

**范围与保留条件。** 此状态极限步骤适用于正维有界开凸 S、原有限测度及 FaceMatching/BoundaryFitted、统一内球形状界的 full P1 网格；`maxDiameter→0` 与 `dt→0` 独立，无 h/dt 耦合、嵌套、分级、盒域或 d≤3 限制。T 固定且允许预算依赖 T，不宣称该预算 T 统一。真实控制费用、物理终态范数趋零和给定 U 的弱收敛仍是明确输入；本批并未选择满足这些条件的实际 HUM 控制族。区域支撑定理给各离散重构的真实支撑，最后状态定理本身不额外返回区域代表/极限费用；后续可用既有闭核弱极限接口组装。没有声称一般多面体 CE、完整 P021 或新的解唯一性定理。

## 固定本地证据与依赖

`/tmp/carleman-t210-local-evidence.json` 的 checked/source SHA 均为本报告 proof，source=local、status=PASS，finished_at=`2026-10-20T04:20:26.969524+00:00`；实际 `lake build Carleman` 和 `lake env lean tools/CheckAxioms.lean` 均记录 exit 0。已读取定向 `target-build.log` **3831 jobs** 成功、全库 `build.log` **4221 jobs** 成功；审计 `axioms.log` 为 0 bytes。本报告核查执行记录与固定源码关联，不声称审核者重新运行全库。

固定源清单 `/tmp/carleman-t210-local-source-manifest.txt` 共 **986** 项，106931 bytes，SHA256=`6be38426243e6df82968eafc0eb6b7c6bb1ba3a4cf4286be4efd4e9a0aad5f22`。独立枚举 tracked Lean 与三项构建配置，确认集合完整无重复，每项 SHA256 均与 proof Git blob 一致。递归 Carleman 导入闭包 **611** 文件，其中 **608** 个旧文件与基线逐字节不变，三个新模块全读。另核对实际 `ConformingStateWeakCompactness`/`ConformingWeakTesting` 与 T208、`DirichletNullControlState` 与 T206、`DirichletTimeEndpoints` 与 T205、`DirichletDualTimeDerivative` 与 T200 固定接受版本源码不变；未重审无关历史或纳入后续工作区增量。

固定 raw **3008159 bytes**，SHA256=`56011f715e31b4603fc5cfeb20fcd0e475ad02c5e495f8637865dcf04552568e`，与 evidence 绑定匹配。四项完整类型及各公理记录已逐项读取，root 实际导入三模块，四项 `#check`/`#print axioms` 齐全；固定审计循环经 `privateToUserName` 遍历命名空间并递归 `collectAxioms`。raw 全部 **3532** 条显式记录（3528 个唯一声明，9 条无公理）仅含 `propext`、`Classical.choice`、`Quot.sound` 或无公理，末行 **9007** 项递归审计 PASS，无 sorryAx 或白名单外项。Lean v4.35.0/compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`，与固定配置一致。

本报告在上述 reviewed_at 冻结，仅单文件提交；不修改数学实现、原稿、总台账或覆盖统计，不 push。
