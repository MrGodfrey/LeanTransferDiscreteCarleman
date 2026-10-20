# T200 / C216 独立本机验收

- checked_sha / proof_sha：`a081c61839658c2869ef6a01e7bcd387a81b9af4`
- mathematical_base：`c8020ad62e0ebb26a1c9144edc50d2ac2458a6d9`
- reviewed_at：`2026-10-20T03:20:08+00:00`；独立验收 Agent：`accept_spatial_foundations`
- 结论：**PASS，15/15 声明，无阻断缺陷**。范围为 **AUXILIARY**：原有限测试身份推出实际 `L²(0,T;V′)` 分布时间导数；未签发 `H` 连续时间迹、初终端识别或完整控制收敛。原文覆盖保持 **17/26**。

## 固定源码与本地执行证据

仅使用固定 Git 对象、固定本地证据和下列必要依赖；未将动态工作树或后续审计文件混入。按用户简化政策不查询或等待远端 CI。

- `/tmp/carleman-t200-local-evidence.json`：`source=local`、`status=PASS`，`checked_sha=source_head_sha` 均为本报告 proof SHA；记录 `lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 均 exit 0，完成时间 `2026-10-20T03:15:08.509426+00:00`。
- `/tmp/carleman-t200-local-source-manifest.txt`：逐项重新计算 **964** 个路径的固定 Git 内容 SHA256，全部相符；路径集合也恰为全部受控 Lean 源文件及三项工具链/依赖配置，无遗漏或多项。清单 SHA256：`9737441b7e2ba61bc5b591e128da8d37db594a6be01946ec13eebc2023d570b3`。
- 实际读取 `/tmp/carleman-t200-target-build.log`：四个新模块构建成功，**3621 jobs**；`/tmp/carleman-t200-build.log`：根构建成功，**4199 jobs**；`/tmp/carleman-t200-axioms.log` 为 **0 bytes**。
- 固定 raw `/tmp/carleman-t200-dual-time-local-axioms.txt`：**2911732 bytes**，重新计算 SHA256 为 `70040ce6bf5174b7d5fae754e025f2f565d48e2cecd84baf7b1dcc4e84a6fbea`，与证据及固定台账一致。已逐项读出本批 15 个完整 `#check` 类型与公理记录；末行确认 **8873** 个 Carleman 声明的全命名空间递归审计通过。
- 独立检查显式公理输出 3465 条、3461 个不同名称，仅出现 `propext`、`Classical.choice`、`Quot.sound` 或无公理。另读固定 `tools/CheckAxioms.lean` 末尾循环，确认遍历包括私有名称恢复后的整个 Carleman 命名空间并递归检查，不把显式输出数量误称全审计数量。
- Lean `4.35.0` / compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`。本次重读的 mathlib `LinearMap`、`Dual`、`Adjoint` 和 Bochner `ContinuousLinearMap` 文件均逐字节匹配该 pin。

## 原文、对象与依赖

直接阅读固定原稿 `paper/main.tex:2403–2415`，重点 `9.26-eq16` 的内部时间测试及右端 `1ωu−Ay−by∈L²(0,T;V′)`；原稿 SHA256 仍为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。也读取固定 `governance/analysis/T200-dual-time.md`、`MATH_SPEC.md` 对应段、C216/T200 台账与 15 项 manifest；规格与台账不替代证明审查。

四新模块的 Carleman 源依赖闭包共 **419** 文件，其中 **415** 个既有文件相对数学基线逐字节不变。已读 T199 冻结报告 `b64539bd63c95a3808b4a2e3a5a0e8c4283c8542:governance/reviews/T199-C215-local-acceptance.md`（5/5 PASS），并重读实际 `AllEnergyControlTests`、`DirichletTestDensity`、`FiniteWeakControlIdentity`、`DirichletTimeWeakCompactness`、`L2Pairing` 与弱时间导数相关定义/证明。`DirichletEnergyState` 是原 `H¹₀` 子空间载体，继承真实图内积；值/梯度映射来自原 jet。T199 的 `SobolevHilbert.jetEquiv` 仅按连续线性等价使用，没有当成等距。

## 15 项逐项核对

以下源定位均为固定提交 `Carleman/Control/<模块>.lean`；raw 行号来自上述固定公理文件。全部名称以前缀 `Carleman.` 展开。

| 模块:源行 | 声明 | raw 行 | 结论与核对点 |
| --- | --- | ---: | --- |
| TensorAdjointPairing:15 | `timeTensor_eq_scalarTensor` | 37915 | PASS；同一 `f(t) • v` 的真实 a.e. 代表给 Lp 相等。 |
| TensorAdjointPairing:21 | `inner_timeTensor_integral` | 37919 | PASS；实际 L² 张量内积等于 Bochner 积分与 `v` 的内积。 |
| TensorAdjointPairing:27 | `compLpL_adjoint` | 37924 | PASS；全 Hilbert 值 L² 上由真实内积逐点交换证明提升与伴随可交换。 |
| TensorAdjointPairing:41 | `HasWeakTimeDerivative.map_integral` | 37931 | PASS；L²×L² 先提供可积性，再交换有界线性映射与两侧积分。 |
| DirichletTimeLoad:15 | `dirichletTimeMass` | 37943 | PASS；定义确为原值嵌入的 `E*E`。 |
| DirichletTimeLoad:20 | `dirichletTimeLoad` | 37947 | PASS；真实 Bochner 伴随构造完整控制、梯度和产品势三项。 |
| DirichletTimeLoad:34 | `dirichletTimeMass_pairing` | 37958 | PASS；任意 `w∈V`、标量 `f∈L²` 的质量配对恢复实际 H 配对。 |
| DirichletTimeLoad:51 | `dirichletTimeLoad_pairing` | 37969 | PASS；任意上述测试下恰为 `U−Ay−by`，两个负号正确。 |
| DirichletMassWeakDerivative:16 | `FiniteDirichletControlIdentity.mass_test_identity` | 37987 | PASS；原全 V 测试推出质量身份，保留真实 `η(0)y₀` 项及负时间导数。 |
| DirichletMassWeakDerivative:36 | `FiniteDirichletControlIdentity.mass_weak_time_derivative` | 38012 | PASS；全部内部光滑紧支测试给 `∂t(MY)=D`，不是输入该导数。 |
| DirichletDualTimeDerivative:15 | `dirichletPivotDual` | 38032 | PASS；实际 `innerSL ∘ M : V→L V′`。 |
| DirichletDualTimeDerivative:20 | `dirichletPivotDual_apply` | 38036 | PASS；点态求值精确为原 H 内积 `〈Ev,Ew〉`。 |
| DirichletDualTimeDerivative:25 | `dirichletDualTimeLoad` | 38041 | PASS；Riesz 映射提升得到实际 `Lp (StrongDual ℝ V) 2` 元素。 |
| DirichletDualTimeDerivative:33 | `dirichletDualTimeLoad_pairing` | 38053 | PASS；任意标量 L² 测试与任意 V 测试识别原三项右端。 |
| DirichletDualTimeDerivative:59 | `FiniteDirichletControlIdentity.dual_weak_time_derivative` | 38071 | PASS；原 pivot 状态的完整 StrongDual 值分布积分恒等式。 |

## 关键数学核验与边界

记 `V=DirichletEnergyState S`、`H=L²(S)`、`μ=volume.restrict (Ioc 0 T)`。原值与全梯度映射分别为 `E:V→H`、`G:V→L²(S;DerivativeFiber d 1)`，其 Bochner 提升记为 `Eₜ,Gₜ`。实际定义展开为
`M=E*E` 和 `D=Eₜ*U−Gₜ*(GₜY)−Eₜ*J*(b.map(J(EₜY)))`。
这里 `J` 是既有 Bochner→产品 L² 线性等距嵌入，`J*` 是 mathlib 的真实 Hilbert 伴随。所有项都是已构造的 L² 元素；没有假设 `J` 满射，也没有把 `J*` 当作逆映射。任意 `f∈L²(μ)`、`w∈V` 的配对准确保留原产品势积分。因此右端对应原控制与同一 Y 的弱梯度/值，不是替代场。

全 V 身份给 `−〈MₜY,η′⊗w〉=〈y₀,η(0)Ew〉+〈D,η⊗w〉`。内部紧支 `φ` 的支撑条件给 `φ(0)=0`；对全部 `w` 用 Hilbert 内积外延性恢复向量积分恒等式。`Ioo` 与 `Ioc` 时间测度通过端点零测相等转换；各 Lp 代表仅作 a.e. 替换。L² 乘光滑时间测试的可积性已由 Hölder 供应，未利用未定义积分的默认值。

最后以实数域的实际 `innerSL : V→L StrongDual ℝ V` 映射两侧积分。`dirichletPivotDual_apply` 明确恢复原 H pivot，而非 V 图内积；故结论确为原状态的 V′ 分布导数。`dirichletDualTimeLoad_pairing` 在任意标量 L² 测试与任意 `w` 下识别原 `U−Ay−by`，无需交换不可数 a.e. 全称量词。内部构造一步 `TimeGrid` 只是调用已有时间弱导数定义，最终结论对每个 `T>0` 成立，不引入网格、步长或耦合限制。

最终定理明确保留开域、空间有限测度、原有界乘子、`Y∈L²_tV`、`U∈L²_tH` 以及既有 `FiniteDirichletControlIdentity`；这些是已接受控制极限阶段的输入。未增加经典时间可微、空间 H²、目标导数存在性或新正则性假设；零维和空域未被排除。本批不逆转 `M`，不宣称 `Y∈H¹_tV`，也未证明原稿下一句 `y∈C([0,T];H)` 或 `y(0)=y₀,y(T)=0`。**C216 可在上述 AUXILIARY 范围接受；P021 与整体控制收敛仍不提升。**
