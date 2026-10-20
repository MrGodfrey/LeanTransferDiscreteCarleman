# T215 / C231 独立本机验收

- checked_sha: `2bbedbc1881148eb48d0280570a98d0234ef0813`
- base_commit: `9662adfb01356f17d6bdb85ea93c7e47046373b0`
- reviewed_at: `2026-10-20T04:56:20+00:00`
- reviewer: independent local Agent `/root/accept_spatial_lemma`
- result: **PASS — 8/8 声明（7 定理、1 定义），无阻断缺陷**
- axiom_check: **PASS**
- scope: **AUXILIARY；17/26 不变，不提升 P021**
- evidence_source: **local**；依现行简化协议核对固定提交的实际本地构建、公理审计与源清单，不等待或声称远端 CI 成功。

独立读取固定 Git 对象中的三模块全部源码、八项完整 raw 类型、分析及 MATH_SPEC，对照原稿 `paper/main.tex:2338–2415`，并读取前面的真实 V′/梯度形式定义。原稿 SHA256=`492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本批确实建立一般原能量解的唯一性；比较解不受零终态限制。它仍是控制收敛整合的辅助阶段，不补足一般多面体实现或整条 PAPER 结论。

## 逐项声明

源码位于固定 SHA 的 `Carleman/Control/`；raw 行号指 `/tmp/carleman-t215-dual-solution-local-axioms.txt`。

| 模块:行 | 完整声明 | raw 行 | 独立结论 |
| --- | --- | --- | --- |
| WeakDerivativeInjection:12 | `Carleman.HasWeakTimeDerivative.of_injective_map_integral` | 39997 | **PASS**：实际注入 CLM 下的分布积分身份反推出原弱导数，先证明两个测试加权函数可积。 |
| DirichletDualMassEquivalence:13 | `Carleman.dirichlet_dual_mass_weak_iff` | 40011 | **PASS**：同一 Y/U/b 的真实 StrongDual 方程与质量弱方程双向等价，时间测度和 a.e. 代表正确。 |
| DirichletDualMassEquivalence:58 | `Carleman.dirichlet_dual_energy_memLp` | 40032 | **PASS**：原 pivotDual 状态及实际 StrongDual 载荷均为真实 L² 函数，不增加可积性前提。 |
| DirichletEnergySolution:15 | `Carleman.DirichletEnergySolution` | 40043 | **PASS**：定义要求原 L²V 状态、真实 V′ 方程和连续 H 初迹；完整定义中没有 q(T)=0。 |
| DirichletEnergySolution:27 | `Carleman.DirichletNullControlState.energy_solution` | 40056 | **PASS**：从真实零终态解删除终态条件，保留同一状态、控制、势及初值。 |
| DirichletEnergySolution:39 | `Carleman.DirichletEnergySolution.mass_weak_time_derivative` | 40067 | **PASS**：一般能量解的原 StrongDual 方程内部给实际质量弱导数。 |
| DirichletEnergySolution:52 | `Carleman.DirichletEnergySolution.unique` | 40085 | **PASS**：任意两个同一 b/U/y0 的一般能量解在完整 L²V 中相等，无有限测试身份或终态输入。 |
| DirichletEnergySolution:70 | `Carleman.FiniteDirichletControlIdentity.unique_energy_solution` | 40098 | **PASS**：原有限测试身份产生能量解；任意同数据比较解均等于它，并取得真实零终迹。 |

## 数学与量词核查

**注入映射下的真实弱导数。** 通用辅助定理要求原 u、du 为 L² 函数，L 是实际注入连续线性映射。对每个紧支光滑时间测试，φ 与 φ′ 在有限闭时间区间上的连续性内部供应其 L² 资格；L²×L² 的乘积给 `φ′u`、`φ du` 的真实 Bochner 可积性。证明再用 L 与积分交换、L 的线性性和注入性反推 `∫φ′u=−∫φ du`。没有从可能不可积、被默认置零的积分反推结论，也没有要求 L 满射、逆有界或值域闭。

**真实 StrongDual 与质量方程的等价。** 已重读实际旧定义：`dirichletTimeMass=E*E`；`dirichletPivotDual=(innerSL ℝ)∘(E*E)`，其作用在任意 w 上恰为 `〈Ev,Ew〉_H`；`dirichletDualTimeLoad` 是同一 `innerSL` 的 Bochner 延拓作用于原 D。这里 D 仍是实际 `E*U−G*GY−E*J*(b.map(J(EY)))`，即原控制减梯度形式算子减同一势；不是重新选择的右侧或另一个状态。

固定 mathlib 的 `toDualMap` 确以 `innerSL` 构造为线性等距嵌入（实数情形），其注入性是实际库定理。新证明只反演这个注入映射下的等式，未反演质量算子 M，也未假设 M 的值域稠密、M 满射或逆有界。两项 `integral_congr_ae` 分别使用 M 的 `compLpL` 代表身份与 `innerSL.compLpL` 的载荷代表身份；不把 Lp 类的选定代表视为处处相等。`g.timeMeasure=volume|_(0,T]` 通过 period=T 和 Lebesgue 端点零测精确转换，所有测试仍为原 `(0,T)` 内紧支光滑测试。正向使用新注入引理，反向使用已证实际 CLM 积分交换，因此确为双向等价。

`dirichlet_dual_energy_memLp` 对原任意 L²V 状态及 L²H 控制，从真实 CLM 的 Bochner 延拓和 a.e. 身份直接推出 pivotDual 状态的 L² 资格；右侧本来就是实际 `Lp (StrongDual ℝ V) 2` 对象，故其代表的 MemLp 同时成立。与完整分布方程合并，这给出了实际 V′ 中的 L² 状态及 L² 时间弱导数。没有假设原 Y 有 V 值强 H¹ 正则性，也没有把 V′ 仅作未解释符号。

**一般解定义与真正唯一性。** 已展开 `DirichletEnergySolution` 的完整定义，而非只检查返回 Prop 的 raw 类型。Y 的载体是原 `Lp (DirichletEnergyState S) 2`；定义只存在一个 H 值 q，使 q 在 `[0,T]` 连续、q=EY a.e.、q(0)=y0，并满足上述真实 V′ 弱方程。定义中没有终态条件，也没有离散极限、有限测试身份、预算或小势前提。连续 H 迹是能量解的真实正则性，已有原质量弱方程的连续迹结果可供应；未读取任意 Lp 代表的端点。

唯一性从两份上述一般解得到各自质量弱方程、连续代表 q/r 和相同初迹，再调用已接受 T214 的实际 `dirichlet_mass_energy_unique`。直接重读其证明，确认它使用同一 b/U 的差方程、零初值的 Volterra 能量论证，输入没有 q(T)=0 或 r(T)=0。结论 Y=Z 是整个 H¹₀ 值 Bochner 类的相等，不只是零阶值相等。内部 `TimeGrid` 取一步且 period=T，仅用于调用既有时间测度接口；由 T>0 构造，不增加任何离散网格、CFL、h/dt 耦合或额外时间限制。

最后一项先从原有限弱身份内部取得同一 Y 的真实零终态解，再忘掉终态条件得到一般解。随后对任意 Z，唯一输入是同一 T/S/b/y0/U 的一般能量解资格；得到 Y=Z 后，把已存在的真实连续零终迹沿该完整类等式传给 Z，返回 `DirichletNullControlState`。因此零终态是比较解的结论，不是输入，也未重选 U、b 或 y0。对任意连续代表，既有连续代表唯一性保证其在整个闭区间与该迹相同。

范围为正 T、原开域 S 和有限空间测度；没有凸性、盒域、H² 正则性、正维或新的统一常数前提。这里证明同数据解唯一及有限测试身份所给解的识别，不新增任意数据的独立存在定理，也不借此宣布所有空间实现和完整 P021 完成。

## 不变依赖与固定本地证据

已全文读取 [T214 冻结报告](T214-local-acceptance.md)，提交 `85fc7f94d5211094b5c538ccbcc37f2361690111`、checked SHA 等于本批基线；直接重读本批调用的质量弱唯一性及零数据证明。三新模块的递归 Carleman 闭包 **443** 文件，其中 **440** 个旧文件与基线逐字节不变。另核对 `DirichletDualTimeDerivative`/`TensorAdjointPairing` 与已接受 T200 `a081c61839658c2869ef6a01e7bcd387a81b9af4`、`DirichletNullControlState` 与 T206 `7b47cb8efa47015a5e2e62f6e2573204bd5c7418`、质量唯一性与 T214 均不变；直接读取其实际类型、定义与有关证明，不重复全历史审核。

`/tmp/carleman-t215-local-evidence.json` 的 checked/source SHA 均为本报告 proof，source=local、status=PASS，finished_at=`2026-10-20T04:53:32.104586+00:00`。实际 `lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 均记录 exit 0；定向 `target-build.log` **3646 jobs** 成功，全库 `build.log` **4237 jobs** 成功，`axioms.log` 为 0 bytes。本次核查实际执行记录与固定源关联，不声称审核者另行重建旧闭包。

独立枚举 `/tmp/carleman-t215-local-source-manifest.txt` 的 **1001** 个 tracked Lean/三项构建配置文件，集合完整无重复，逐项 SHA256 与 proof Git blob 相同。清单 **108581 bytes**，SHA256=`9796e108d3d1f647f82e559087aec304907be3b5ee68dd352137019dd0d0dd07`，与 evidence 匹配。Lean v4.35.0/compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` 与 mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 均匹配固定配置；Riesz 映射定义从该 mathlib pin 的 Git 对象读取。

固定 raw **3081773 bytes**，SHA256=`abc0b30a79815079dd1a0bd41cc2818b1ad6fa91a597dceccda9539a4f63b39c`。八项完整类型与各自公理记录均核对，仅含 `propext`、`Classical.choice`、`Quot.sound`。全部 **3555** 条非空公理列表和 **9** 条无公理记录没有白名单外项；末行 **9054** 项全 Carleman 命名空间递归审计 PASS，无 sorryAx。固定 root 导入全部三模块，八项 `#check`/`#print axioms` 齐全；实际全局审计使用 `privateToUserName` 与递归 `collectAxioms`，并非仅本批名单。

本报告于上述 reviewed_at 冻结，仅单文件提交；不修改实现、台账、原稿或覆盖统计，不 push。
