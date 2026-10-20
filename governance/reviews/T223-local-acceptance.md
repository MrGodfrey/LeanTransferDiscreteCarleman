# T223 / C239 独立本机验收

- checked_sha: `7413b28a97681bcf834d35701a7ca878ebac1b99`
- mathematical_base: `a3993a7a580ebab556f2a780ecb0ac3f81942390`
- reviewed_at: `2026-10-20T05:51:29+00:00`
- reviewer: 独立本机 Agent `accept_spatial_lemma`
- result: **PASS，9/9 显式声明（5 定理、3 定义、1 结构），无阻断缺陷。**
- scope: **AUXILIARY；C239 可在此范围验收，原文 17/26 不变。**

直接读取固定 `Carleman/Spatial/WeakCoefficientJet.lean` 全部源码、完整 raw 类型/公理、固定分析和 MATH_SPEC，对照原稿 2624–2635 行一般 W^{2m,∞} 系数与 Leibniz 步骤，以及 286 行原有界域设置。本批提供有限阶真实弱系数乘法和完整乘后 Hⁿ 射流；不等同于原关联算子的微分表达式、严格降阶交换子或完整 Proposition A.1。

## 数学核对

1. **有限阶原系数数据。** `BoundedWeakCoefficient S n` 的 derivative l 是真实有界可测乘子；其唯一导数条件为每个 |l|<n、每个坐标 i 的 `IsWeakMultiplierDerivative S e_i (derivative l) (derivative (i::l))`。已直接展开该条件：对全部原紧支光滑测试，要求实际 Lebesgue 积分分部积分身份。没有 C∞、经典导数、Lipschitz 代表、域外延拓、无限阶链或预设排序对称性。虽然存储函数定义在全部列表上，但 |l|>n 的项没有导数约束，也不参与本批 ≤n 阶展开；可任取零有界乘子，不能将这种总函数存储误认作无限阶正则性。`truncate` 保持同一数据，只用 k≤n 缩小允许链长。结构是原有限 W^{n,∞} 分布数据的显式接口，本批未额外宣称与某另一未定义 W^{n,∞} 类型的形式等价。
2. **真实一阶乘积法则正确迭代。** 已读 T222 的 `mul_weakCoefficient` 及实际磨光测试证明：原有界系数在有限测度下内部构造同一 L² 类，经 φ 乘局部卷积测试的值和导数强收敛，得到 D_i(a u)=a D_i u+(D_i a)u。它不要求系数光滑或状态域外弱延拓。本批对 `derivativeSplits l` 的每个 p 使用该法则，长度恒等式 |p₁|+|p₂|=|l|<n 同时保证 |p₁|<n 和 |p₂|<n，故系数下一阶链与状态下一阶字段均合法，最高只到 n。求和后的两部分恰为下一词的展开，未越界调用较高阶导数。
3. **完整列表重数与真实 L² 字段。** 原 `derivativeSplits` 每次把新方向分别放在系数词或状态词，使用列表拼接，不去重。因此重复坐标所带的二项式重数、混合项和零阶项全部保留。每项为实际 `BoundedMultiplier.map` 作用于原 `wordField` 的 L² 类，列表有限和合法；并非将形式符号指定成目标导数。词字段在有效长度范围内是原 Sym 分量，所有用于微分的词均已证明有效，不使用超阶 wordField 的默认零分支制造身份。
4. **弱唯一性与排序无关。** 对已有零阶乘法身份的 v，`weakCoefficient_wordField_mul` 从空词开始归纳，用原全部测试上的弱导数唯一性逐阶识别字段。随后 permutation 归纳的 cons 分支同样使用唯一性；swap 分支在 |l|+2≤n 下构造两条真实二阶弱链并调用 `mixed_commute`。后者实际通过原测试二阶导数交换和积分分部证明，不是公理或系数光滑假设。trans 分支保持词长。由此证明整个乘积展开与词排序无关，而非直接假设所有系数代表逐点相等。
5. **内部构造完整原 Hⁿ jet。** `weakCoefficientProductJet` 对每阶每个无序多指标取排序词的实际 Leibniz L² 类，再由既有连续线性 `derivativeFieldAssembly` 装配原 Euclidean 分量场。其标量分量确实恢复输入 L² 类。对每个 k<n、α、i，排序后的 Sym.cons i α 与 i::sort α 的真实列表置换及已证排序无关性，把下一分量接到上一项的真实弱导数。故内部证明了原 `weakJetSubmodule` 所有阶、所有方向、所有 SpatialTest 的完整链。零阶通过 Sym.nil 和空词公式精确恢复 `(a.derivative []).map u.value`。没有输入乘后状态存在或目标导数公式；最终 word 定理又识别这个已经构造的同一 jet 的任意有效词字段。
6. **实际图拓扑上的连续线性乘法。** CLM 的加法与数乘由真实零阶乘法线性和完整 jet 的值注入性得到；该注入性已读，是各阶弱导数唯一性的归纳结论。连续性逐字段、逐有限分量通过实际有界乘子 CLM、原词字段 CLM、有限列表和及 `derivativeFieldAssembly.continuous` 复合，进入原弱 jet 的子空间拓扑。`continuous_leibnizField` 的实际类型仅需乘子族与词，不携带旧光滑系数假设。这里的拓扑为全 Hⁿ 图拓扑，未把零阶 L² 范数当作高阶范数，也没有用无穷维空间的虚假自动连续性。CLM 对固定有限系数数据构造；本批没有另行宣称其范数是某个尚未证明的统一显式常数。
7. **原假设及退化情形。** 主定理明确输入开域和 `IsFiniteMeasure (volume.restrict S)`；有限测度仅用于有界系数的真实 L² 实现，原论文有界 Ω 已满足，未添加几何正则性或状态光滑性。n=0 时导数链为空、装配只剩零阶，实际恢复 L² 乘法。d=0、空域或零测度无非法方向、正体积要求或零除；有限 Sym 的 a.e. 分量识别没有不可数零测集交换。本批没有证明弱系数乘法保持 H₀ⁿ、一般关联算子域或完整算子交换子，也未如此计入覆盖。

## 全部声明

源行指固定 `Carleman/Spatial/WeakCoefficientJet.lean`，raw 行指下列固定本机公理文件。九项完整类型、结构字段和实际定义/证明均已核对。

| 声明 | 源行 / raw 行 | 逐项结论 |
|---|---:|---|
| `Carleman.BoundedWeakCoefficient` | 16 / 40919 | PASS；有限真实分布链，无无限光滑或排列对称性前提。 |
| `Carleman.BoundedWeakCoefficient.truncate` | 24 / 40921 | PASS；仅缩小阶数，保持同一实际系数族。 |
| `Carleman.WeakSobolevJet.weakCoefficient_leibnizField_weak` | 34 / 40925 | PASS；逐分裂项合法调用真实弱乘积，再恢复完整下一阶展开。 |
| `Carleman.WeakSobolevJet.weakCoefficient_wordField_mul` | 51 / 40935 | PASS；原零阶身份推出任意已有乘后 jet 的全部有效词身份。 |
| `Carleman.WeakSobolevJet.weakCoefficient_leibnizField_perm` | 66 / 40944 | PASS；弱唯一性及真实 mixed_commute 证明排序无关。 |
| `Carleman.WeakSobolevJet.weakCoefficientProductJet` | 87 / 40953 | PASS；内部装配全部场并证明所有原弱链。 |
| `Carleman.WeakSobolevJet.weakCoefficientProductJet_value` | 105 / 40961 | PASS；实际零阶 L² 类等于原系数乘原状态。 |
| `Carleman.WeakSobolevJet.weakCoefficientProductCLM` | 113 / 40967 | PASS；原完整图拓扑上的真实连续线性乘法。 |
| `Carleman.WeakSobolevJet.weakCoefficientProductJet_word` | 129 / 40975 | PASS；同一内部构造 jet 的所有有效词精确等于实际 Leibniz 展开。 |

## 依赖及固定本地证据

T222 正式冻结报告 `fcd4a0abd52632a49eb110f3b17491813a9839a9` 已全文读取（checked_sha 为本批基线，reviewed_at `2026-10-20T05:49:36+00:00`，13/13 PASS）。两项实际 T222 模块与该版本逐 Git blob 不变，且本批已直接读其全部源码及所用定义。新模块 Carleman 导入闭包为 **127 文件**，其中 **126 旧模块与基线逐 blob 不变**；HigherWeakProduct、WeakMixedDerivative、DerivativeFieldAssembly 又分别比对已验收 T217 固定版本不变。实际调用的词分量、列表分裂、完整弱 jet、图拓扑和唯一性也已重读；未重审无关旧历史，未混入未来 T224 工作树。

- `/tmp/carleman-t223-local-evidence.json`：source=local、PASS，checked/source 精确等于本报告 proof SHA，finished_at `2026-10-20T05:46:46.338198+00:00`；实际全库构建和公理审计命令均记录 exit 0。本次核对真实执行记录及固定源，不虚称重新执行全库，也未查询远端 CI 或看板。
- 独立枚举固定提交全部 tracked Lean 文件及三项构建配置，核对 `/tmp/carleman-t223-local-source-manifest.txt` 路径完整性、唯一性及全部固定 Git blob 字节摘要：**1014 项全匹配**。清单 **109998 bytes**，SHA256 `12397d60f029941d30e2ae05a04267119a1602c2ddd9686d0000738c4a9d9788`。
- 实际 `/tmp/carleman-t223-target-build.log`：**3299 jobs** 成功，107 bytes，SHA256 `fa172a90bd01e64a42c229a28c7461df18d2fa65a7377f4a8b0e4c7a2b358221`；`/tmp/carleman-t223-build.log`：**4250 jobs** 成功，80 bytes，SHA256 `ee67093bb57288d6dc5fd41e660da1bf3beb2f6875706b40f4cf284f5bef5dfb`；审计 stderr `/tmp/carleman-t223-axioms.log` 为 0 bytes。
- 固定 raw `/tmp/carleman-t223-weak-coefficient-jet-local-axioms.txt`：**3145687 bytes**，SHA256 `56d962cde3ed16a954610290695bcc4918b591a5233cfed7ee8d4b0f5435ce04`。全部九项完整展开类型/公理逐项核对；扫描 **3657 个非空公理列表和 10 个无公理记录**，只有 `propext`、`Classical.choice`、`Quot.sound`，无 sorryAx 或额外数学公理。固定工具按 `privateToUserName` 遍历全 Carleman 命名空间并递归 `collectAxioms` 检查白名单；raw 末行确认 **9386 声明递归审计 PASS**，包含结构生成声明。根导入新模块、九项 #check/#print axioms 齐全，原递归审计循环未变。
- 固定 Lean 4.35.0（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）、mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 与证据相同。原稿 SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef` 未变。

没有需要修复的数学或证据缺陷；仅接受有限阶原弱系数的完整 Hⁿ 乘法基础，保持 AUXILIARY / 17 of 26。正文与 reviewed_at 签发后冻结；仅单文件提交报告，不修改数学、台账、根导入或原稿，不 push。
