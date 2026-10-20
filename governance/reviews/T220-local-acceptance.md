# T220 / C236 独立本机验收

- checked_sha: `1d10859fce3c68f87f9f5e7e166f41e3c90d60c5`
- mathematical_base: `1039ed66b829e865571f6ba6da574091bd785a80`
- reviewed_at: `2026-10-20T05:31:08+00:00`
- reviewer: 独立本机 Agent `accept_spatial_foundations`
- result: **PASS，15/15 显式声明（13 定理、2 定义），无阻断缺陷。**
- scope: **AUXILIARY；C236 可按此范围验收，原文 17/26 不变。**

直接读取固定 Git 对象中两新模块全部定义与证明、15 项完整 raw 类型/公理、原稿 `paper/main.tex:2615–2652`（尤其 2637–2650）、固定分析/MATH_SPEC/C236/T220 声明清单及下述实际依赖。本批得到真实共轭形式误差的 lower×full 界；未把相对权导数常数的统一供应、乘后 H₀ᵐ 状态组装、coercivity 吸收或完整 Proposition A.1 当作已完成。

## 数学审查

1. **唯一主项和真实重数。** 已直接读取旧 `derivativeSplits` 递归：每次导数分别落在左/右因子，产生两个列表的拼接；重复坐标导致的相同分裂仍保留为重复列表项。`derivativeSplits_empty_left` 的列表归纳过滤掉全部左侧新增导数的分支，并在右分支递归恢复唯一 `([],l)`。`derivativeRemainderSplits` 使用同一列表的相反布尔过滤，没有转成集合、去重或丢失二项式重数。非空左词长度>0，配合原 `|p₁|+|p₂|=|l|`，得到严格 `|p₂|<|l|≤n`。`leibnizField_eq_principal_add` 用原两个过滤和的准确分拆，因此是原实际 L² 展开的身份，不是误差估计的定义。
2. **真实单项界和 q 次幂。** `leibnizRemainder_term_bound` 把 `outer.map ((a p₁).map ...)` 精确写成实际乘子乘积，以给定 a.e. 相对导数界控制 L² 范数，再以原 Sym 字段范数控制词分量。所有自然数减法均由长度约束合法化，实际使用 `q^(n−|l|) q^|p₁|=q^(n−|p₂|)`。这里的状态字段严格低于 n，故落入 `lowerParameterNorm`，没有把最高阶偷放进 lower。完整余项应用实际列表范数三角不等式、线性映射与有限和交换，逐个保留重数后，以过滤列表长度≤2^|l| 给常数。代数层允许 q≥0；去掉前置 q^(n−|l|) 的最后共轭词界明确要求 q≥1，且 2^|l|≤2^n。
3. **实际弱导数与主项消去。** 已读 `CoordinateWords.wordField`、`WeakLeibniz.leibnizField_weak/wordField_mul` 和真实弱乘积规则。它们对原全部紧支光滑测试证明分布乘积公式，再由同一零阶乘法身份和弱导数唯一性逐阶识别既有乘后 jet；没有把高阶公式输入为假设。`conjugated_word_remainder_bound` 正确调用该身份，展开 principal+remainder，再由实际 `outer*(a [])=1` 的 L² 乘法反演消掉主项，得到 `outer D^l v−D^l u` 的范数。原弱状态无需经典导数或点态代表光滑性。
4. **完整系数形式及 K(K+2)。** 已读取同一 `coefficientJetForm` 的所有阶/Sym 双和、真实乘子交换和 `inner_inverse`。`coefficientJetForm_inverse_pairing` 把原 a(v,z) 精确改写为每项 `⟨aαβ(wDβv),ξDαz⟩`，无需系数对称或系数导数。令 L=lower(q,u)、R=parameter(q,one,u)，已证明 0≤L≤R。每项原分量≤R，两侧误差≤KL 给 `‖ξDαz‖≤(K+1)R`。实际配对差是 `⟨a(x−p),y⟩+⟨ap,y−t⟩`，两项 L² Cauchy–Schwarz 与系数 bound 给 `bound·K(K+1)LR+bound·KLR=bound·K(K+2)LR`。完整双和逐项取绝对值再求和，仅引入 `Σαβ bound(aαβ)`，非对角、低阶和零阶系数全部保留。
5. **真实 intrinsic 导数供应与方向。** `intrinsicWordMultiplier` 的值就是原函数实际 `wordDerivative`；其可测性、有界性及 cons 的真实 Fréchet 导数身份由 `BoundedSmoothOn`、开域和测度集中条件内部供应。空词精确等于原乘子，`coordinateVector_represents` 将该实际词导数还原为原无序 Sym 分量。最终定理仅对权 w、ξ 要求 `BoundedSmoothOn`，算子系数 a 仍只有有界可测乘子数据。证明分别把 `(weight,outer)=(ξ,w)` 用于 v、`(w,ξ)` 用于 z，并显式交换第二处互逆乘法；两侧都以同一 u 为中心。因此取 u=σv、w=σ、ξ=σ⁻¹ 时，差是原 `a(v,σ²v)−a(σv,σv)`，没有逆权或参数方向颠倒。
6. **前提和范围严格保留。** 辅助 `error_of_components` 确实输入两侧分量误差，最终 `smooth_conjugation_error` 已用实际导数定理内部清偿这些输入。最终仍明示 q≥1、C≥0、全部长度≤n 的两侧相对导数界，以及 u/v/z 是真实 Hⁿ jets、v.value=ξu.value、z.value=wu.value；本批没有单独构造乘后 H₀ⁿ 成员，也没有把这两个零阶身份称为已从无前提得到。对于**固定** C、阶数及系数，形式误差常数 `Σbound·(2^n C)(2^n C+2)` 不含 q/权 sup/状态/时间；但从整个原允许权族在所有参数之前统一选 C，仍是下一阶段要接入的已有 `allowedWeight_word_uniform`。这里没有声称已经完成原小系数 η 吸收或加权下界。n=0 时余项/低阶和为空、原互逆配对使形式差为零；q=1、d=0、空域、零系数或零状态均没有除以零或非法索引。通用接口保留开域和 ν 集中于 S；原受限 Lebesgue 测度满足这些条件。

## 全部 15 项声明

源码定位相对于固定 `Carleman/Spatial/`；raw 行号相对于 `/tmp/carleman-t220-leibniz-remainder-local-axioms.txt`。每项均直接检查完整类型和实现。

| 固定源码定位 | 完整声明 | raw 起始行 | 逐项结论 |
|---|---|---:|---|
| LeibnizRemainder:13 | `Carleman.derivativeSplits_empty_left` | 40545 | PASS；空左词过滤精确为单元素 [([],l)]，含 l=[]。 |
| LeibnizRemainder:21 | `Carleman.derivativeRemainderSplits` | 40548 | PASS；仅过滤非空左词，保留原列表重复项及重数。 |
| LeibnizRemainder:24 | `Carleman.derivativeRemainderSplits_lt` | 40550 | PASS；非空左词和长度守恒给状态词严格低阶。 |
| LeibnizRemainder:36 | `Carleman.WeakSobolevJet.leibnizRemainder` | 40553 | PASS；实际余项是原 L² 乘子作用于原弱词字段的有限列表和。 |
| LeibnizRemainder:40 | `Carleman.WeakSobolevJet.leibnizField_eq_principal_add` | 40560 | PASS；完整 Leibniz 场精确分解为唯一主项加实际余项。 |
| LeibnizRemainder:49 | `Carleman.WeakSobolevJet.lowerParameterNorm_component` | 40567 | PASS；q≥0 下严格低阶和中的任意真实场单项受控。 |
| LeibnizRemainder:55 | `Carleman.WeakSobolevJet.lowerParameterNorm_le_parameterNorm` | 40574 | PASS；lower≤full，原最高阶项保持非负。 |
| LeibnizRemainder:60 | `Carleman.WeakSobolevJet.leibnizRemainder_term_bound` | 40582 | PASS；实际乘子范数与精确 q 幂恒等式给逐项低阶界。 |
| LeibnizRemainder:89 | `Carleman.WeakSobolevJet.leibnizRemainder_weighted_bound` | 40597 | PASS；全部重复项求和，过滤长度≤2^|l|，完整余项常数准确。 |
| LeibnizRemainder:117 | `Carleman.WeakSobolevJet.conjugated_word_remainder_bound` | 40611 | PASS；真实弱 Leibniz 与互逆乘法消去主项，给同一乘后状态的词导数误差。 |
| CoefficientConjugationError:19 | `Carleman.jetScalarComponent_parameter_le` | 40637 | PASS；原任意 Sym 分量由完整参数范数控制。 |
| CoefficientConjugationError:26 | `Carleman.coefficientJetForm_inverse_pairing` | 40643 | PASS；同一完整系数形式与实际双侧互逆乘子配对精确相等。 |
| CoefficientConjugationError:39 | `Carleman.coefficientJetForm_error_of_components` | 40655 | PASS；两项配对差真实展开，常数 Σbound·K(K+2)；分量误差为本辅助层显式前提。 |
| CoefficientConjugationError:102 | `Carleman.intrinsic_conjugated_component_remainder_bound` | 40675 | PASS；实际 intrinsic wordDerivative 供应全部弱微分关系，再识别原 Sym 分量。 |
| CoefficientConjugationError:126 | `Carleman.coefficientJetForm_smooth_conjugation_error` | 40696 | PASS；同一 u 的逆权/正权状态，内部清偿两侧分量误差，K=2^n C。 |

## 固定本地证据和依赖边界

- 独立枚举 `/tmp/carleman-t220-local-source-manifest.txt` 全部 **1010** 项，核对其集合恰为固定提交全部受检 `.lean` 和三项构建配置、无重复，并逐项 SHA256 比对 Git blob，全部一致。清单 **109561 bytes**，SHA256 `6f446fda53b8e86aa66e13ad2e37eb14fcc55c4835bd12fed2dcc99cd2c7ae51`。原稿 SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef` 未变；固定 root 实际导入两新模块，15 项 `#check @`/`#print axioms` 齐全。
- 两模块实际 import 递归闭包 **126** 文件；其中 **124** 个旧模块的 Git blob 与数学基线完全不变，另外两项正是本次新模块。已直接重读本批使用的分裂、弱 Leibniz、实际乘子、intrinsic 导数、低阶/完整参数范数及系数形式。T219 冻结报告提交 `2dc8b09b757c041154c765d0d39d71ca67923c79`（reviewed_at `2026-10-20T05:25:52+00:00`，checked_sha 为本批数学基线）已全文读取；本批实际使用的是其低阶范数定义及缩放比较，未假称已应用最终 η 吸收。不重复无关历史或未来工作树。
- `/tmp/carleman-t220-local-evidence.json` checked/source SHA 精确匹配本报告，source=local、status=PASS，finished_at `2026-10-20T05:27:48.841200+00:00`。实际 `lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 均记录 exit 0。已读取 `target-build.log` 的两模块成功及 **3284 jobs**，`build.log` 的全库 **4246 jobs** 成功；`axioms.log` 为 **0 bytes**。本次核对真实执行记录和固定源绑定，没有另行声称重建旧闭包或检查远端 CI。
- raw **3126715 bytes**，SHA256 `a9599c334d28d499f6a9b18871c5c7af140f17cd78ba37d1d0afe7c83a9cb8da`，与 evidence/固定登记相同。15 项完整类型及公理已逐项读取；独立扫描 **3641** 条显式公理记录，只有 `propext`、`Classical.choice`、`Quot.sound` 或无公理。另检查固定审计工具以 `privateToUserName` 遍历全 Carleman 命名空间并递归 `collectAxioms`、遇白名单外项报错；raw 末行实际为 `Axiom audit passed for all 9285 Carleman declarations.`。**9285** 是含生成声明的完整递归审计数，区别于显式打印数；无 sorryAx 或新数学公理。固定 Lean **4.35.0**，mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`。

本报告确认真实严格低阶 Leibniz 余项与实际系数共轭形式误差界，无需修复的数学或证据缺陷。相对权导数界的全参数统一供应、原 H₀ᵐ 乘后状态整合及最终加权下界仍待；AUXILIARY / 17 of 26 保持。reviewed_at 与正文签发后冻结；仅单文件提交本报告，不修改数学、台账、原稿，不 push。
