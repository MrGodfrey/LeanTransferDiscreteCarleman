# T225 / C241 独立本机验收

- checked_sha: `f616d5d02bde9bd06cc719a33a727b40c5d44675`
- mathematical_base: `03f8c203f00dc90f126a44f9200c5ac56f645752`
- reviewed_at: `2026-10-20T06:07:01+00:00`
- reviewer: 独立本机 Agent `accept_spatial_lemma`
- result: **PASS，11/11 显式声明（9 定理、2 定义），无阻断缺陷。**
- scope: **AUXILIARY；C241 可按此范围验收，原文 17/26 不变，不提升完整 P022 / Proposition A.1。**

已直接读取固定 `Carleman/Spatial/CoefficientCommutator.lean` 全部实现、固定 T225/C241 清单、11 项完整 raw 类型/公理、分析及 MATH_SPEC，对照原稿 `paper/main.tex:2615–2654` 及 `ass:localization` 的原 `[A,σ]σ⁻¹` 方向、全部状态和 q 幂。以下结论基于实际证明与依赖，而非执行者描述或构建成功。

## 数学审查

1. **同一原形式关联算子。** 已直接重读 `CoefficientDifferentialTerm/Operator`、原 `CoerciveForm.domainV/domain/operator`、`operator_isAssociated` 和 `domainSobolevJet_value`。原域由存在真实 L² 载荷、对全部 H₀ᵐ 测试满足变分式定义，算子取该唯一载荷；并非将当前微分表达式重命名为原算子。T224 的测试积分身份经真实 Hᵐ 闭包推广，已把 Σαβ(−1)^|α|D^α(aαβD^βu) 识别为同一原算子。本批最终同时以 `higherCoefficient_operator_canonical` 重写 z 和 v 的实际算子值，并以 canonical jet 的真实零阶身份传递 z=wv，因此估计没有换算子、状态或域。
2. **真实有限弱系数及完整展开。** 系数为 `BoundedWeakCoefficient S (2*m)`，仅要求有限阶有界分布导数链，零阶对称性和 coercivity 仍取原形式数据。没有要求系数 C∞、经典代表或域外延拓。实际 differentialTerm 是 derivativeSplits(l) 列表上的全部 `(D^p₁a)D^(p₂++r)u`；列表保留重复项和二项式重数。新 term 差恒等式把 w 的真实 L² 线性乘法移入列表和，再与标量系数乘子交换，精确化为 `(D^p₁a)[D^(p₂++r)u−wD^(p₂++r)v]` 的和。|p₁|+|p₂|=|l| 与 |l|+|r|≤n 保证所有状态词仍≤n，不调用超阶默认零字段。此处辅助词差界 E 明示为输入；最终定理已内部供应，未把目标交换子界作为原问题假设。
3. **系数界、符号和求和。** `coefficientTermBound` 精确求和每个原分裂项的实际 coefficient bound；非负性来自各有界乘子。逐项乘子范数估计及列表三角不等式给 term error≤termBound·E。operatorBound 再累加所有 α、β，包括全部低阶、零阶和非对角项。原 (−1)^|α| 被保留在差身份中，只在范数估计时用其绝对值为 1；没有删去某些系数或错误抵消符号。operatorBound 是固定系数有限导数界的有限和，不含 q、权的 sup、状态、时间或网格；这些 derivative bound 均来自原有限 W^{2m,∞} 数据，并非额外目标常数。
4. **主项真实相消及严格降阶。** 对 v=ξu、wξ=1，使用的 `conjugated_word_remainder_bound` 已直接重读：完整弱 Leibniz 中唯一空权导数词为 `([],l)`，乘 w 后由真实互逆 L² 乘法消掉 D^l u；剩余左词非空，因此状态词严格短于 l。所有 |l|≤2m，故最高状态阶为 2m−1。实际每项幂等式为 `q^(2m−|l|)q^|p₁|=q^(2m−|p₂|)`；其阶数约束使自然数减法合法。用 q≥1 去掉前置非小于 1 的因子、以列表长度≤2^|l|≤2^(2m) 控制重数，得到原 `lowerParameterNorm(q,u)=Σ(j<2m)q^(2m−j)‖D^j u‖₂`，没有残留 2m 阶项、负幂或替代范数。新证明用 norm_sub_rev 对齐差方向，只改变符号而不改变算子定义。
5. **原全允许权族和常数量词。** 已读 `allowedWeight_inverse_relative_uniform` 的真实 ξ=`q^(−τ)exp(q(−eta)ρ)`、wξ=1 及两侧相对词导数证明。本批仅对光滑权的逆权使用实际导数链，系数仍是有限弱链。J>0 在 q≥1、全部实 τ、|eta|=1、w 和状态之前固定；由 u.value=w v.value 内部推出 v.value=ξu.value。实际统一常数为 `C=(1+coefficientOperatorBound a)·2^(2m)·J>0`，其中加 1 只保证严格正性，放大时使用 lower≥0。C 与 T、网格、qmax、状态以及权绝对界无关；全部实 τ 的结论包含原固定有限 τ_*。最终 `SmoothOnClosure` 经原有界域紧闭包提供域内 BoundedSmoothOn，不要求域外光滑延拓或给定权导数界。
6. **完整域保持与原正则性前提。** `higherCoefficient_operator_multiplier_preserves` 用已证 D(A)=H₀ᵐ∩H^{2m}：原 domain_le 给 H₀ᵐ，明确输入的 hreg:D(A)⊆H^{2m} 给高阶资格；已验收真实光滑乘法分别保持这两个完整空间，再由域等式返回原 D(A)。并未假定乘后状态在域中，也未限制为光滑状态。hreg 是原 Proposition A.1 已给的域等式所蕴含的一向资格；本批不证明一般椭圆正则性，也不输出原定量图估计。有限测度实例是原有界 Ω 的既有性质。V 的乘法保持仍由同一已调用 H₀ᵐ 定理提供。
7. **原交换子方向及逆权域资格。** 最终实际结论为任意原域 z、v 且 z=wv 的 `‖Az−wAv‖≤C lower(q,jet z)`，右端是同一个 z 的完整真实弱导数。对原任意 z，取 v=w⁻¹z：逆权属于同一允许族（−τ、−eta），同一域保持定理保证 v∈D(A)，互逆乘法恢复 z=wv。因此正是原 `[A,w]w⁻¹z`，没有把整个算子取负或以错误状态计算右端。逆权域保持来自此全族量词/同一 helper，不是假定给定 v 总能找到。m=0 时严格低阶和为空、实际零阶标量算子与权交换；零系数界、零状态、空域、d=0 和 q=1 均无非法除法/索引。所有代表等式都在实际 L²/a.e. 意义下使用。

## 全部 11 项声明

源行指固定 `Carleman/Spatial/CoefficientCommutator.lean`，raw 行指下列固定本机审计文件。逐项实际类型与定义/证明均已检查。

| 声明 | 源行 / raw 行 | 逐项结论 |
|---|---:|---|
| `Carleman.list_sum_map_sub` | 15 / 41143 | PASS；有限列表差与两原和之差准确相等。 |
| `Carleman.WeakSobolevJet.coefficientTermBound` | 25 / 41146 | PASS；实际分裂列表全部系数界之和。 |
| `Carleman.WeakSobolevJet.coefficientTermBound_nonneg` | 29 / 41149 | PASS；逐项非负，含重复项。 |
| `Carleman.WeakSobolevJet.coefficientDifferentialTerm_error_of_words` | 37 / 41152 | PASS；真实乘子交换及完整和给单项差界，状态阶数合法。 |
| `Carleman.coefficientOperatorBound` | 75 / 41166 | PASS；全部原 αβ 的固定有限界。 |
| `Carleman.coefficientOperatorBound_nonneg` | 80 / 41172 | PASS；完整双和非负。 |
| `Carleman.coefficientDifferentialOperator_error_of_words` | 87 / 41177 | PASS；原全算子符号和双重求和正确，辅助词差条件明示。 |
| `Carleman.coefficientDifferentialOperator_smooth_commutator` | 123 / 41187 | PASS；实际逆权主项消去，仅严格低阶原弱字段。 |
| `Carleman.coefficientDifferentialOperator_allowed_commutator` | 149 / 41210 | PASS；内部供应真实逆权/相对导数，全允许参数前固定正常数。 |
| `Carleman.higherCoefficient_operator_multiplier_preserves` | 177 / 41231 | PASS；同一原算子完整域保持，原 hreg 明确保留。 |
| `Carleman.higherCoefficient_allowed_commutator` | 194 / 41250 | PASS；原闭包光滑 profile、真实域保持及同一 canonical jet 的实际 Az−wAv 界。 |

## 依赖与固定本机证据

T224 冻结报告 `94223761edea20d3d77cb6eb4b62ee05be8868e7` 已全文读取（checked_sha 为本批基线、reviewed_at `2026-10-20T05:54:29+00:00`，15/15 PASS）。新模块实际 Carleman 导入闭包 **194 文件**，其中 **193 个旧模块与数学基线逐 Git blob 不变**。除直接读取关键定义和证明外，已比对实际微分表达式两模块与 T224、严格低阶余项与 T220、全族权供应与 T221、高阶乘法与 T217、有限弱系数接口与 T223 的接受版本不变；未混入未来 T226 工作树或动态审计。

- `/tmp/carleman-t225-local-evidence.json`：source=local、PASS，checked/source 精确等于完整 proof SHA，finished_at `2026-10-20T06:03:46.451529+00:00`。实际 `lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 均记录 exit 0。本次独立核对这些真实记录和固定源绑定，不声称重新执行全库或检查远端 CI/看板。
- 独立枚举固定提交全部 tracked Lean 文件及三项构建配置，与 `/tmp/carleman-t225-local-source-manifest.txt` 核对路径完整性、唯一性及逐 Git blob 字节摘要：**1017 项全部一致**。清单 **110341 bytes**，SHA256 `0da5b02044f43571420e2ade234ff22258b32e584ac0d25212e18cdb4285fbdf`。
- 实际 `/tmp/carleman-t225-target-build.log`：**3366 jobs** 成功，109 bytes，SHA256 `a2aac2b7f824dafe70da4c5533570926825fcde63b2f83a827149a5e4b1f6f4d`；`/tmp/carleman-t225-build.log`：**4253 jobs** 成功，80 bytes，SHA256 `fcc389ba20660c712c8086818b0fca4c1be231f58cee9abbb115ee512fbe85a4`。`/tmp/carleman-t225-axioms.log` 为空。
- 固定 raw `/tmp/carleman-t225-coefficient-commutator-local-axioms.txt`：**3168036 bytes**，SHA256 `171c1b62cfc9f36778feb61f28ca133eb89ebd37dd51bab63085660127ba49e5`。完整 11 项展开类型逐项读取；独立扫描 **3683 个非空公理列表及 10 个无公理记录**，只有 `propext`、`Classical.choice`、`Quot.sound`，无 sorryAx 或新数学公理。原全命名空间 `privateToUserName` / `collectAxioms` 递归白名单循环未变，raw 末行确认 **9446 声明递归审计 PASS**。根导入新模块，11 项 #check/#print axioms 齐全；新增生成声明也在递归覆盖内。
- 固定 Lean 4.35.0（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）和 mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 与证据一致；原稿 SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef` 未变。

未发现需修复的数学或证据缺陷。仅接受本批同一原弱系数算子的全允许权交换子界和域保持；完整 A.1 接口装配与 P022 整项验收仍留后续，保持 AUXILIARY / 17 of 26。签发后正文与 reviewed_at 冻结；仅单文件提交此报告，不改数学、台账、根导入或原稿，不 push。
