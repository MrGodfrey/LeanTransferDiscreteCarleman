# T202 / C218 独立本机验收

- checked_sha：`1b8ccf90c8aeef46bf0f614e537c02a6494caa5a`
- mathematical_base：`cf2701d48ac60007502c1ad44286c1d64b1303ce`
- reviewed_at：`2026-10-20T03:33:02+00:00`
- reviewer：独立 Agent `/root/accept_spatial_foundations`
- 结论：**PASS，4/4 声明，无阻断数学缺陷；AUXILIARY，17/26 不变，P021 不提升。**

直接阅读固定 `Carleman/Control/PivotTimeTrace.lean` 全部证明、四项 raw 展开类型、分析 `governance/analysis/T202-weighted-trace.md`、`governance/MATH_SPEC.md` 对应段和 C218/T202 台账。原稿 `paper/main.tex:2415` 声称控制极限的 H 连续迹及端点，本批仅提供其所需的质量加权迹估计，未完成该句全部结论。原稿 SHA256 保持 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

## 四项声明

名称均带 `Carleman.` 前缀；源行来自固定 `Carleman/Control/PivotTimeTrace.lean`，raw 行来自 `/tmp/carleman-t202-weighted-trace-local-axioms.txt`。

| 源行 | 声明 | raw 行 | 独立结论 |
| ---: | --- | ---: | --- |
| 14 | `ac_time_norm_sub_bound` | 38182 | PASS；真实绝对连续标量函数在任意两闭区间点之间的差，由全区间实际导数范数积分控制；允许两点逆序或相同。 |
| 31 | `integral_norm_mul_le_l2` | 38186 | PASS；真实范数函数的标量 L² 类与 Cauchy–Schwarz 给任意测度下的乘积积分界。 |
| 52 | `HasWeakTimeDerivative.pivot_energy_variation` | 38191 | PASS；原弱导数内部给绝对连续性及 a.e. 强导数，能量变化由实际 `D=E*E du` 控制，系数为 2。 |
| 87 | `HasWeakTimeDerivative.pivot_trace_bound` | 38203 | PASS；对起点积分平均，得到所有闭区间时刻的真实 H 迹界，精确保留 `1/T`。 |

## 数学核查

令 `T=g.period>0`、`μ=g.timeMeasure=volume.restrict (Ioo 0 T)`。输入为任意完整实 Hilbert 空间 V、H、任意有界线性 `E:V→H`、真实分布身份 `HasWeakTimeDerivative g u du`、`u` 在 `[0,T]` 上 V 连续及 `du∈L²(μ;V)`。连续性内部供应 `u∈L²`，有界算子内部供应 `Eu` 和 `D=E*E du` 的 L² 资格；没有另输入目标迹估计、质量导数预算、E 的单射性或有限维性。`u` 本身无周期性前提；TimeGrid 在这里仅提供正时间长度和实际测度。

`ac_time_norm_sub_bound` 先把绝对连续性限制到 `uIcc a b`，实际区间 FTC 给差值；有向区间积分的范数界转到 `uIoc a b`，再以非负可积函数的集合积分单调性嵌入全区间。导数积分可积性来自绝对连续性；`Ioo/Icc` 的转换只使用 Lebesgue 端点零测，不把端点函数值识别为任意 Lp 代表。

对能量函数 `‖Eu‖²`，实际弱 FTC 给 u 绝对连续及 a.e. 强导数；E 与范数的 Lipschitz 性和绝对连续乘法规则给能量绝对连续。mathlib 的范数平方链式法则及真实伴随身份产生
`d/dt ‖Eu(t)‖² = 2〈Eu(t),E du(t)〉 = 2〈u(t),E*E du(t)〉`
的 a.e. 等式。随后 Cauchy–Schwarz 和真实 L²×L² 可积性控制绝对导数积分。范数函数的 `toLp` 代表通过 a.e. 身份识别，`eLpNorm_norm` 精确保留原范数；未用未证明可积性的积分默认值。

最后固定任意 `t∈[0,T]`，对 a.e. 起点 a 积分能量变化界，使用 `μ.real univ=T` 和实际 L² 内积平方身份，合法除以正 T，得到

`‖Eu(t)‖² ≤ T⁻¹ ‖Eu‖²_{L²_tH} + 2 ‖u‖_{L²_tV} ‖E*E du‖_{L²_tV}`。

结论包含 0、T 两端点，且对 E=0、零空间同样成立。右侧没有 `‖du‖`、正则化逆范数或额外 `‖E‖` 因子；T⁻¹ 显式，**不属于 T 统一估计**。这里的 V 连续性是当前弱 H¹ 近似轨迹的明确输入；证明未把它施加给原控制极限 Y，也没有构造该 Y 的 H 连续代表。将正则化近似接入本估计、证明一致收敛并识别原初终态仍属后续工作。

## 依赖与固定本地证据

新模块 Carleman 递归源闭包共 **29** 文件；其中 **28** 个旧文件相对数学基线全部逐字节不变。直接重读 `WeakTimeEnergy`、`WeakTimeFTC`、`TimeTraceBound` 的实际定义/证明；其弱 FTC 确实基于原弱导数和连续代表，不输入经典导数。核对 mathlib `AbsolutelyContinuousFun` 的 FTC、`DerivIntegrable` 的导数可积性及 `InnerProductSpace/Calculus` 的范数平方链式法则，三个实际文件均匹配 pin `56a005855ea17e0b0958f73ec801ae140b0a1679`。另全文读取 T201 冻结报告 `ead953059ca10ece442e495c14c134d23058d593:governance/reviews/T201-local-acceptance.md`（19/19 PASS），确认其范围仍只到质量正则化强收敛。

- `/tmp/carleman-t202-local-evidence.json`：`source=local`、`status=PASS`，`checked_sha=source_head_sha` 精确匹配本报告；`lake build Carleman` 和 `lake env lean tools/CheckAxioms.lean` 均记录 exit 0，完成时间 `2026-10-20T03:27:02.702594+00:00`。
- `/tmp/carleman-t202-local-source-manifest.txt`：**968** 项逐一匹配固定 Git 内容摘要，集合恰为全部 tracked Lean 源文件及三项工具链/依赖配置，无重复、遗漏或多项；**104946 bytes**，SHA256 `ddfb424adea94a7df143686c883d0f980a9dfa08b10659c5be675c300c891c6d`。
- 实际读取 `/tmp/carleman-t202-target-build.log`：新模块成功、**3172 jobs**；`/tmp/carleman-t202-build.log`：完整根构建成功、**4203 jobs**；`/tmp/carleman-t202-axioms.log` 为 **0 bytes**。本次核验这些固定执行证据，没有声称再次运行全库。
- 固定 raw **2922527 bytes**，重新计算 SHA256 `a1fc23ca20badfc9b43a3953a21c148545e6f0c370225b4af024df8bb1cb0e86`，与证据/台账一致。全部四项根导入、`#check`、`#print axioms` 及展开类型均对应；四项仅依赖 `propext`、`Classical.choice`、`Quot.sound`。
- 显式公理输出 **3488** 条、**3484** 个不同名称（9 条无公理），均无白名单外项。另独立读取固定全命名空间 `collectAxioms` 循环，末行实际确认 **8913** 个声明递归审计通过。Lean 为 `4.35.0`，compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，与固定配置及证据一致。

按用户简化政策，仅使用固定本地构建、公理审计和独立数学审核，不查询或等待远端 CI。**C218 可在上述 AUXILIARY 范围接受。** 本报告签发后冻结正文与时间，仅单文件提交；不改变数学、台账、原稿或覆盖数。
