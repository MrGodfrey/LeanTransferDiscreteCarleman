# T219 / C235 独立本机验收

- checked_sha: `1039ed66b829e865571f6ba6da574091bd785a80`
- mathematical_base: `b41b6861b988e758d026fed32f5d5802e411b636`
- reviewed_at: `2026-10-20T05:25:52+00:00`
- reviewer: 独立本机 Agent `accept_spatial_lemma`
- result: **PASS，9/9 显式声明（8 定理、1 定义），未发现阻断缺陷。**
- scope: **AUXILIARY；C235 可按本范围验收，原文 17/26 不变。**

直接读取固定 Git 对象中 `Carleman/Spatial/SmallParameterInterpolation.lean` 全部代码、9 项完整 raw 类型、公理、T219 分析/MATH_SPEC 和原稿。论文 286 行已给定有界 Lipschitz 域；2637–2650 行使用任意 η>0 的低阶双和插值。本批清偿该插值步骤，尚未把真实系数共轭形式差控制为此双和，未完成 Proposition A.1 的加权下界或整条结论。执行者说明和编译成功均未代替以下数学核对。

## 数学核对

1. **原域、真实弱状态和范数。** `lowerParameterNorm q u` 是严格低阶 `Σ(k<n) q^(n-k) ‖field k u‖`；`parameterNorm q one u` 含全部 0…n 阶。每个 field 是原完整弱射流该阶全部 Sym 多指标组成的 Euclidean L² 场；不存在经典光滑代表、给定乘后射流、边界零值或额外目标估计前提。`IsBoundedLipschitzDomain` 是开有界集和真实局部 Lipschitz 图。已直接复核 `DomainJetInterpolation`、`DomainJetNeighbor`、局部图定义与参数范数：旧参数插值通过域内统一锥及真实弱导数获得，没有输入高阶 Sobolev 扩张算子或待证 η 插值。
2. **一次小系数及常数量词。** 固定旧域插值常数 I≥1 后，选 `R=max(1,I/η)`，故 R>0、I/R≤η。严格低阶 n−k≥1 给出 `R L_q≤P_(Rq)`；原域插值可用于 Rq≥1，除以 R 得 `L_q≤η‖u‖jet+C q^n‖value u‖`，实际 `C=1+I R^n/R≥1`。I、R、C 均在 q 与全部弱状态之前选择，只依赖固定域、维数、阶数和 η。未要求 η≤1，也未引入网格、时间或状态依赖。
3. **二次小系数。** 另选 `R=max(1,2I²/η)`，利用真实参数范数单调性 `P_q≤P_(Rq)`，各因子非负，从而 `R L_q P_q≤P_(Rq)²`。再用域插值及 `(a+b)²≤2(a²+b²)`，得到 `L_q P_q≤η‖u‖jet²+C(q^n‖value u‖)²`；实际 `C=1+2I²(R^n)²/R≥1`。这里并非把一次估计和未经吸收的完整范数直接相乘；R 同时控制平方后的主项系数。
4. **双和完整、q 幂准确。** 对 k,j∈Fin(n+1)，自然数恒等式 `2n−k−j=(n−k)+(n−j)` 合法，故令 `X_k=q^(n-k)‖field k u‖` 后原每一项正好为 X_k X_j。条件 k+j<2n 精确分解为 k<n 的全部 j≤n，以及 k=n、j<n；只排除最高阶对 (n,n)。因此双和等于 `L_q P_q+X_n L_q≤2 L_q P_q`，没有漏掉非对角、交叉或零阶项。调用二次估计的 η/2 版本，并准确改写 `(q^n‖value u‖)²=q^(2n)‖value u‖²`，得到原指数和任意 η 系数。
5. **真正 Hᵐ 范数。** jet 采用有限积范数，`SobolevHilbert` 采用全部阶场 L² 范数的平方和；二者没有被当成相等。`toJet_norm_le` 逐阶使用非负平方和中单项≤总和，证明 `‖toJet u‖jet≤‖u‖Hm`。最终入口只在 η≥0 下放大该项，value 仍为同一零阶 L² 类；同一 C 适用于全部实际 Hᵐ 状态，因而也适用于原 H₀ᵐ 子空间。后续若双和前有固定系数常数，仍须相应选择 η 或处理零系数；本批没有擅自省去真实形式差这一步。
6. **退化和边界情形。** 代数辅助只需 q≥0，参数插值入口明确 q≥1；所有除法均除以已证正的 η 或 R，不除以 q、状态范数或维数。n=0 时低阶和为空、双和唯一候选 (0,0) 被严格条件排除，证明仍成立。d=0、空域、零状态不触发非法指标或正体积要求；域假设若在某退化情形无实例，也没有伪造该实例。原论文 d,m≥1 是这些声明的子范围。

## 全部声明

以下源行均指固定 `SmallParameterInterpolation.lean`，raw 行均指下列固定本机公理文件；每项均已核对完整类型和实际证明，结果均 **PASS**。

| 声明 | 源行 / raw 行 | 实际内容 |
|---|---:|---|
| `Carleman.WeakSobolevJet.lowerParameterNorm` | 13 / 40439 | 真正严格低阶参数场范数和；唯一新增定义。 |
| `Carleman.WeakSobolevJet.lowerParameterNorm_nonneg` | 16 / 40444 | q≥0 下逐项非负。 |
| `Carleman.WeakSobolevJet.lowerParameterNorm_rescale` | 20 / 40449 | R≥1 的真实缩放比较，包含完整最高阶非负项。 |
| `Carleman.WeakSobolevJet.boundedLipschitz_lowerParameter_small` | 38 / 40458 | 原域全部弱 jet 的一次 η 插值；C 先于 q/u。 |
| `Carleman.WeakSobolevJet.boundedLipschitz_lowerParameter_product_small` | 67 / 40473 | lower×full 的二次 η 插值；非预设结论。 |
| `Carleman.WeakSobolevJet.lowerOrderQuadratic_le` | 111 / 40489 | 全部 r+s<2n 双和≤2 lower×full。 |
| `Carleman.WeakSobolevJet.boundedLipschitz_lowerOrderQuadratic_small` | 149 / 40502 | 完整原双和任意 η 界及准确 q^(2n)。 |
| `Carleman.SobolevHilbert.toJet_norm_le` | 169 / 40522 | 实际积范数≤实际平方和 Hilbert 范数。 |
| `Carleman.boundedLipschitz_hilbert_lowerOrderQuadratic_small` | 180 / 40526 | 原完整 Hᵐ 状态上的统一双和界。 |

## 依赖边界与本地证据

本模块递归 Carleman 导入闭包 92 个模块，其中 91 个旧模块与数学基线逐 blob 不变；该旧闭包也逐 blob 等于已独立验收的 Section 3 固定证明 `a315bdc449c58a705a982f0d009f1dde24d6af66` 对应闭包。已核对 T019 报告中原域 hI 的内部供应，同时重读本批实际调用的域插值、范数单调性和 Sobolev Hilbert 实现。相邻 T218 正式报告 `523976572bfe70ad8a386ea3ad1ffb777271912f`（checked_sha 为本批数学基线，reviewed_at `2026-10-20T05:17:34+00:00`）已读取；本模块没有导入或假设 T218 的系数形式结论。固定差分仅新增本模块及根导入/审计项，没有改变旧数学证明。

按用户简化后的本机协议，独立核对固定本地实际执行记录和原始产物，不等待或查询远端 CI，也未把记录核对表述为重新执行全库构建。

- 证据 `/tmp/carleman-t219-local-evidence.json`：`source=local`、`status=PASS`，checked/source SHA 均为上述完整 proof SHA；finished_at `2026-10-20T05:20:19.468322+00:00`。`lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 均记录实际 exit 0。
- `/tmp/carleman-t219-local-source-manifest.txt`：独立枚举固定提交全部 tracked Lean 文件及三个构建配置，核对 1008 项路径集合、唯一性及每个固定 Git blob 的 SHA256；全部匹配。文件 109342 bytes，SHA256 `65fca91f8433002e73a0da67c18cd85da44fda6a75381e96300ba2fbf90b1690`。
- 定向 `/tmp/carleman-t219-target-build.log`：3239 jobs 成功，116 bytes，SHA256 `ea7fc9f189c7db35ae9a05dd8f3ae88886628042643516c4f88addca6f147033`。全库 `/tmp/carleman-t219-build.log`：4244 jobs 成功，80 bytes，SHA256 `4ee277739939c61107f8331f2979d5485b71adbd6fc41463a32e7ede543c03ac`。审计 stderr `/tmp/carleman-t219-axioms.log` 为空。
- 固定 raw `/tmp/carleman-t219-small-interpolation-local-axioms.txt`：3113482 bytes，SHA256 `93b4a06fac6a4540ade877e4bb6acb4f188c50e7652343d4149217fac1428d96`；末尾实际全命名空间递归审计 **9261 声明 PASS**。9 项完整展开类型及逐项依赖均在该文件中；全部 3617 个非空打印公理列表及 9 个无公理记录已扫描，只有 `propext`、`Classical.choice`、`Quot.sound`，无 sorryAx 或额外数学公理。根模块确实导入新文件，审计工具包含全部 9 项显式检查，递归审计覆盖生成声明。
- Lean 4.35.0（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）、mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 均与固定配置一致。原稿 SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef` 未变。

本报告仅接受原低阶参数双和的任意小系数插值及其真实 Hilbert 范数版本；实际系数共轭余项、完整 A.1 及相关 PAPER 覆盖不随本报告提升。报告签发后正文与 reviewed_at 冻结；未修改数学实现、总台账、根导入或原稿。
