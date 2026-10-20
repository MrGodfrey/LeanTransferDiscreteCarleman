# T227 / C243 独立本机验收

- checked_sha: `4573638d5529914e0140c25f4dfe3689be92afaa`
- mathematical_base: `4728609fbece53cc6afcc9013b94592eb23ee87d`
- reviewed_at: `2026-10-20T06:23:47+00:00`
- reviewer: 独立本机 Agent `accept_spatial_lemma`
- result: **PASS，14/14 显式声明（12 定理、2 定义），未发现阻断缺陷。**
- axiom_check: **PASS**
- accepted_scope: **AUXILIARY；任意实 Hilbert 空间上正有界算子的正有界平方根存在性。原文覆盖保持 17/26，P022 不升级。**

已从固定 Git 对象全文读取 `Carleman/Continuous/RealOperatorSquareRoot.lean`，逐项对照固定 raw 的完整类型、公理记录、analysis/MATH_SPEC/声明清单及原稿 A1。未纳入后续工作树、动态 `.ci` 或未来平方根域实现。本次按既定本地验收协议核对实际执行记录和固定源码，没有重跑全库，也未查询远端 CI 或看板。

## 原文对应与实际结论

原稿 `paper/main.tex:353` 明确要求同一原关联无界算子 A 满足 `D(A^(1/2))=V` 和 `‖A^(1/2)v‖₂²=a(v,v)`。本批最终完整类型是：对任意 `H`，仅假设 `NormedAddCommGroup H`、`InnerProductSpace ℝ H`、`CompleteSpace H`，对任意 `R : H →L[ℝ] H`，由 `R.IsPositive` 得到某个实际连续线性算子 `B`，使 `B.IsPositive ∧ B * B = R`。这里乘法是连续算子的复合，正性是实际对称性及全向量非负二次型；没有把“平方根”定义为标量范数，也没有将平方身份作为输入。

已全文读取 T226 冻结报告 `63c553825231ccf22f1efb72dc2f10ed4e666fde`。本结果为清偿其 F1 提供正确的有界算子工具，但尚未建立原 A 的无界平方根、组合域、平方根域等于原 V 或形式能量身份，也未声称平方根唯一性。本批通过不等于 F1 已销项，不能将其算作完整原 A1 或 P022。

## 关键数学核对

1. **真实非交换迭代及标量控制。** 标量 `c₀=0`、`cₙ₊₁=(1+cₙ²)/2` 的非负性、上界 1 和单调性均由递推证明。单调有界极限 c 与后移序列具有同一极限，连续运算给 `c=(1+c²)/2`，所以 `(c−1)²=0`，确实得到 c=1。对任意实范数代数、任意 `‖X‖≤1`，`P₀=0`、`Pₙ₊₁=(X+Pₙ²)/2` 的范数界由三角不等式和乘积范数界归纳获得。双指标差估计使用恒等式 `p²−r²=p(p−r)+(p−r)r`；中间交叉项精确抵消，不使用 p、r 交换。标量差的因式分解只发生在 ℝ 中。故 `‖Pₙ−Pₘ‖≤|cₙ−cₘ|` 对全部 n,m 成立。
2. **算子范数收敛及平方身份。** n≤m 时距离至多 `1−cₙ→0`，给实际范数 Cauchy 性，未错误使用严格压缩映射。只有存在极限的定理增加 `CompleteSpace A`；代数平方恒等式的定理显式不需要完备性。范数、乘法和加法连续，将同一 P 的后移极限识别为 `P=(X+P²)/2`，并给 `‖P‖≤1`。由 `P+P=X+P²` 得 `(1−P)²=1−X`，第二次同样使用非交换合法展开。代入连续算子代数后，这就是实际算子范数极限和复合平方，不是逐点强收敛的偷换。
3. **正收缩补算子的范数界。** `R.IsPositive` 在实 Hilbert 空间上同时给自伴性与 `⟨Rx,x⟩≥0`；`‖R‖≤1` 和 Cauchy–Schwarz 给 `⟨Rx,x⟩≤‖x‖²`。证明对实际自伴算子 `1−R` 调用 Rayleigh 商范数刻画，商为 `⟨(1−R)x,x⟩/‖x‖²`，绝对值不超过 1。x=0 被单独处理，非零 x 才使用正分母；没有隐藏非零空间或单位球非空假设。实际 mathlib 定理索引全部 x，且范数刻画用极化证明，不以紧性、有限维、谱分解或复函数演算为前提。
4. **极限自伴与正性。** `X=1−R` 自伴，逐次平方、相加及实数 1/2 缩放保持自伴。连续算子上的 star 是实际 Hilbert 伴随；其连续性使 `star P=P` 的集合闭，从而把自伴性传到同一个范数极限 P。`B=1−P` 的非负二次型直接由 `‖P‖≤1` 和 Cauchy–Schwarz 得到，不需要额外证明或假设 P 正。结合实际自伴性得 `B.IsPositive`；平方身份则由前项取 `X=1−R` 得到，正性与平方使用同一个 B。
5. **任意正有界算子与边界情形。** 取 `K=max(1,‖R‖)>0`，证明 `K⁻¹R` 正且范数≤1，然后把其根 B 缩放为 `sqrt(K)B`。平方中系数为 `sqrt(K)²K⁻¹=1`，实际复合恢复 R。只除以严格正的 K；零算子、非可逆算子和零 Hilbert 空间均包含。全部定理不要求有限维、可分、紧算子、谱假设、复化或预先存在的根。一般 Banach 代数辅助部分也没有可交换性假设。K 的依赖仅用于逐个 R 的存在性构造，本批没有宣称不依赖 R 的统一根范数或无界算子结论。

## 全部声明逐项结论

下列源码行均在固定 `Carleman/Continuous/RealOperatorSquareRoot.lean`；raw 行在本批固定审计文件。14 项完整类型与各自公理记录均已读取。

| 源码 / raw 行 | 声明 | 结论 |
|---|---|---|
| 14 / 41439 | `Carleman.sqrtScalarIter` | PASS；实际实数递推定义。 |
| 18 / 41441 | `Carleman.sqrtScalarIter_bounds` | PASS；全部 n 的 `0≤cₙ≤1`。 |
| 25 / 41443 | `Carleman.sqrtScalarIter_monotone` | PASS；真实单调性。 |
| 31 / 41445 | `Carleman.sqrtScalarIter_tendsto` | PASS；实际极限等于 1。 |
| 43 / 41447 | `Carleman.sqrtComplementIter` | PASS；任意实范数代数中的实际迭代。 |
| 47 / 41449 | `Carleman.sqrtComplementIter_norm` | PASS；全 n 的范数控制。 |
| 60 / 41452 | `Carleman.sqrtComplementIter_dist` | PASS；完整双指标、合法非交换差估计。 |
| 102 / 41458 | `Carleman.sqrtComplementIter_cauchy` | PASS；真实范数 Cauchy 性。 |
| 113 / 41461 | `Carleman.sqrtComplementIter_exists_limit` | PASS；完备空间中同一极限、范数界和固定点身份。 |
| 125 / 41466 | `Carleman.sqrtComplementIter_limit_square` | PASS；非交换代数中精确平方身份，无完备性前提。 |
| 137 / 41469 | `Carleman.sqrtComplementIter_selfAdjoint` | PASS；每一迭代的真实伴随身份。 |
| 144 / 41473 | `Carleman.positive_contraction_complement_norm` | PASS；实际 Rayleigh 范数界，含 x=0。 |
| 165 / 41476 | `Carleman.positive_contraction_exists_sqrt` | PASS；同一个真实正有界 B 满足 B²=R。 |
| 186 / 41480 | `Carleman.positive_exists_sqrt` | PASS；任意正有界 R 的正根存在，无附加谱或维数条件。 |

## 依赖及固定本地证据

新模块只导入四个固定 mathlib 模块，不导入旧 Carleman 模块；T226 是任务用途的前置阶段，不是本构造的 Lean 依赖。已直接读所调用的正性定义、正性与自伴/二次型等价、伴随 star、连续算子范数环、Rayleigh 范数刻画、单调收敛及 Cauchy 判据。实际 mathlib checkout 无修改，HEAD 与固定 `lake-manifest.json` 一致为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。固定 proof 相对 base 的数学改动仅新增本模块、根导入与审计清单；旧数学声明未变。Lean 固定为 4.35.0，编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`。

- `/tmp/carleman-t227-local-evidence.json`：source=local、PASS，checked/source 均为本报告 proof；finished_at=`2026-10-20T06:17:44.690162+00:00`。`lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 的实际执行记录均为 exit 0。
- 独立枚举固定提交全部 tracked `.lean` 及 `lean-toolchain`、`lake-manifest.json`、`lakefile.toml`，与 `/tmp/carleman-t227-local-source-manifest.txt` 的路径集合、唯一性和逐 Git blob 摘要比对：**1021 项全部匹配**。清单 110771 bytes，SHA256 `84c7271f0f0ec88b003e9e3e603dc7102f570c9de57af2f4bf4d8cfb180fbd6f`。
- `/tmp/carleman-t227-target-build.log`：**2751 jobs** 成功，114 bytes，SHA256 `436fa131df716adff3b0dee53bb6ddf3222b93c34907cdc3b98353e422cb2907`。`/tmp/carleman-t227-build.log`：**4258 jobs** 成功，80 bytes，SHA256 `222558e5e3d4369bfb94b81c9eb11686d184ec8d6707567714646259ed7fb673`。`/tmp/carleman-t227-axioms.log` 为 0 bytes。
- `/tmp/carleman-t227-real-square-root-local-axioms.txt`：**3181728 bytes**，SHA256 `a6d0c24cad37d425fcfe164019f8f4be996a08a653941b11c4783d165942137b`，与固定证据摘要一致。14 项均仅依赖正常基础公理 `propext`、`Classical.choice`、`Quot.sound`。全部显式输出的 3704 个公理列表及 10 个无公理记录均无其它公理；原 `privateToUserName` / `collectAxioms` 递归白名单循环未改，末行确认全命名空间 **9484 声明审计 PASS**。未见 sorryAx 或额外数学公理。
- 固定根导入及全部 14 项 `#check` / `#print axioms` 齐全。原稿与 base 逐字节相同，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

验收接受本批 **AUXILIARY 正有界平方根存在性**；无修复项。原无界 A 的平方根域与能量身份仍须独立完成。正文及 reviewed_at 签发后冻结，仅单文件提交本报告，不修改数学、台账、原稿或其它报告，不 push。
