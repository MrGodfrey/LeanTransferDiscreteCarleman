# T206 / C222 独立本机验收

- checked_sha：`7b47cb8efa47015a5e2e62f6e2573204bd5c7418`
- mathematical_base：`bfa6e3a8b9af4367eca74101ad0473c42e8bdfa8`
- reviewed_at：`2026-10-20T03:55:40+00:00`
- reviewer：独立 Agent `/root/accept_spatial_foundations`
- 结论：**PASS，3/3 声明，无阻断缺陷；AUXILIARY，17/26 不变，P021 不提升。**

已直接阅读固定两新模块全部源码及三项 raw 展开类型，展开新结论谓词和真实载荷定义；阅读固定 `governance/analysis/T206-null-state.md`、MATH_SPEC 对应段、C222/T206 台账及原稿 `paper/main.tex:2318–2415`。原稿要求实际控制族的每个弱积聚点产生区域零延拓控制及零终态能量解。本批实现实际盒 Cartesian FD 分支的这一组合，不涵盖一般 P1 分支，也未新增能量解唯一性定理。原稿 SHA256 保持 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

## 三项声明

源路径为固定 `Carleman/Control/<模块>.lean`；名称均带 `Carleman.` 前缀。raw 行来自 `/tmp/carleman-t206-null-state-local-axioms.txt`。

| 模块:源行 | 声明 | raw 行 | 独立结论 |
| --- | --- | ---: | --- |
| DirichletNullControlState:16 | `DirichletNullControlState` | 38433 | PASS；定义正文包含同一 Y 的 H 连续代表、原初值、零终值和实际 StrongDual 分布方程，不是隐藏假设或新公理。 |
| DirichletNullControlState:29 | `FiniteDirichletControlIdentity.null_control_state` | 38446 | PASS；从原有限弱恒等式内部组合真实连续迹/端点与原对偶时间导数，构造全部结论。 |
| CartesianNullControlLimits:18 | `Physical.box_cartesian_controls_null_limits` | 38460 | PASS；保留同一真实控制族及所有原量词，对每个给定弱积聚 U 的原同一 Y 同时返回有限弱身份和连续零终态状态。 |

## 结论谓词的实质

`DirichletNullControlState T S hS b y₀ Y U` 中 Y 已是原 `Lp (DirichletEnergyState S) 2` 元素。谓词要求存在一个实际函数 q，在整个 `[0,T]` 上 H 连续，满足 `q=dirichletStateValue S ∘ Y` a.e.、`q(0)=y₀`、`q(T)=0`，并对每个内部光滑紧支时间测试 φ 满足

`∫ φ′ · dirichletPivotDual(Y) = −∫ φ · dirichletDualTimeLoad(T,hS,b,Y,U)`。

两侧是真实 `StrongDual ℝ V` 值 Bochner 积分。原 pivot 映射的求值为 `〈EY,Ew〉H`；实际载荷展开为 Riesz 映射作用于
`Eₜ*U − Gₜ*(GₜY) − Eₜ*J*(b.map(J(EₜY)))`。
任意标量 L² 测试及任意 w∈V 的已有真实配对身份将其识别为原 `U−Ay−by`。Y 的 L² 资格和有界 pivot 映射保证左侧场为 L²；载荷本身具有实际 `Lp (StrongDual ℝ V) 2` 类型。没有把有限个空间方向、形式符号或任意替代右端当作原 V′ 方程。

`null_control_state` 的输入只有原 `FiniteDirichletControlIdentity` 及其既有 T>0、S 开/有限测度接口。它先由 `continuous_H_trace` 构造同一 q 的连续性、a.e. 身份和两个端点，再接同一 Y、U、b 的 `dual_weak_time_derivative`。没有把新结论谓词、原 Y 连续、目标端点或新正则性作为前提。端点读取自真实连续 q；不对任意 Lp 代表的零测点强行赋值。

## 实际控制族、每个积聚点与常数

完整阅读并对比 T198 的 `box_cartesian_controls_weak_accumulation`。将本批主定理名称改回、仅删去最后新增的 `DirichletNullControlState` 合取后，两个完整 statement 经空白规范化**完全相同**；不是只比对标题或最终一行。

- 固定正边长盒、W/ωsharp/ω 嵌套观测区域及 `ratio≥1` 后，先存在 κ,d₀>0；再对每个 T>0、M≥0 选 C>0；C 在所有网格、时间序列、原势 b 和任意原 L² 初值之前。仅要求 hₙ→0 与 dtₙ→0 分别成立，无新增时空耦合。T 固定用于收敛；基础 κ,d₀ 的 T 独立性保留，未误称费用 C 与 T 无关。
- 同一个尾段 J、uₙ、yₙ 原样保留：初态是实际 Eₕ* y₀；方程使用实际 Cartesian 刚度、同一原 b 的时空平均节点势和真实区域控制扩张；全节点状态、原物理控制费用、指数终值界及 dt·M≤1/2 均保留。初始重构强收敛、物理终态范数趋零和重构终态趋零也同时保留。
- 原 K 是真实时间单元与空间控制单元的复合重构。支撑结论仍为 Kₙ(t) 在 ω 外零 a.e.，费用仍为 `√C‖y₀‖`。区域空间使用真实限制测度，`restrictRegionCLM.adjoint.compLp v=U` 是已证明的零延拓身份；重读 `SupportedTimeControl` 和 `ObservedRegionLp` 核实该伴随确为实际零延拓，范数由真实 Lp 等距身份保持。
- 相对弱紧性仍对任意取样 a（允许重复）给严格递增 χ 及区域 v。更强的积聚点结论先固定任意严格递增 a，再固定每个满足全部 H 值 Bochner L² 测试弱收敛的给定 U，之后才得到 Y 和 v。代码直接取旧 `hacc a ha U hU` 返回的 Y、预算、v、零延拓身份和有限弱恒等式；唯一新增步骤是对该原 `hid` 调用 `null_control_state`。U、Y、v、离散控制族和费用常数均未替换。

新定理没有把 q 的构造所需 T⁻¹ 乘入费用，也未改变原 y₀、势或控制支撑。最终返回存在的零终态能量状态及原有限弱身份，未另证明解唯一性。主盒定理维数是 d+1、保留原正维非空观测条件；辅助状态接口适用于其原全部维数/开域范围。一般 P1 网格分支和整体 P021 仍不提升。

## 依赖与固定本地证据

新模块 Carleman 递归源闭包共 **856** 文件，其中 **854** 个旧文件与基线逐字节相同。直接重读 T198 原族证明、区域弱极限/零延拓、T200 实际载荷与对偶配对、T205 标量 Green/端点及 `continuous_H_trace`。T198、T200、T205 的相应关键文件分别与已验收固定证明 `714954acb8b017b09da56c71d4bd91b7d0ccffe2`、`a081c61839658c2869ef6a01e7bcd387a81b9af4`、`bfa6e3a8b9af4367eca74101ad0473c42e8bdfa8` 一致。全文读取 T205 冻结报告 `ac4d2338d0ccfec3dc8427b03a36d8bf6ed5d9a9:governance/reviews/T205-local-acceptance.md`（6/6 PASS）；其正文与实际已读文件逐字节相同。本次没有重复全历史数学审核，也没有以依赖报告代替实际接口检查。

- `/tmp/carleman-t206-local-evidence.json`：`source=local`、`status=PASS`，`checked_sha=source_head_sha` 精确为本报告 proof SHA；实际 `lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 均记录 exit 0，完成时间 `2026-10-20T03:52:22.154717+00:00`。
- `/tmp/carleman-t206-local-source-manifest.txt`：**976** 项逐一匹配固定 Git 内容摘要；集合恰为全部受控 Lean 源文件及三项工具链/依赖配置，无重复、遗漏或多项。**105829 bytes**，SHA256 `89b882d6758bf4c8aba36e8abe4ca166d45502ab840782fe25d34a779896f28c`。
- 实际读取 `/tmp/carleman-t206-target-build.log`：两新模块成功、**4094 jobs**；`/tmp/carleman-t206-build.log`：完整根构建成功、**4211 jobs**；`axioms.log`、`probe3.log` 均为空，未将 probe 空日志单独当作退出码证据。本次核查固定执行记录，没有声称重新运行全库。
- 固定 raw **2959947 bytes**，重新计算 SHA256 `e26f6a9737b107713dc7e95e5a143ac2bde800f585ae70f14cb456fe1f330d8f`，与证据/台账一致。三项根导入、`#check`、`#print axioms` 和完整展开类型均对应；新定义另已直接展开源码正文。
- 显式公理输出 **3504** 条、**3500** 个不同名称（9 条无公理），仅正常 `propext`、`Classical.choice`、`Quot.sound`，无白名单外项。固定全命名空间循环使用 `privateToUserName` 与 `collectAxioms` 递归检查，raw 末行确认 **8945** 项审计通过。工具链为 Lean `4.35.0` / compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`、mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`，与固定配置及证据一致。

按用户简化政策不查询或等待远端 CI。**C222 可在实际盒 FD 分支的 AUXILIARY 范围接受，3/3 PASS。** 报告签发后冻结正文和时间，仅单文件提交，不改变数学、台账、原稿或原文覆盖数。
