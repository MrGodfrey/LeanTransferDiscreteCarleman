# T052 / C068 独立本机验收

- `checked_sha`: `df8b853f9203194295be90f39ef5f797af31b9b3`
- `base_commit`: `51e67cf2b206b1e754d90a53ccd03c6e80e570fc`
- `semantic_checked_at`: `2026-10-18T20:08:42+00:00`
- `reviewed_at`: `2026-10-18T20:11:24+00:00`
- `result`: **PASS**。
- `axiom_check`: **PASS**。
- 范围：**AUXILIARY**。本阶段只证明有限系数型的加权强制性。系数型与真实单元积分的识别、完整 V_h 的节点对应和测试构造、实际加权 L² 投影稳定性均尚待；不提升 P011/P012 或其他完整原文覆盖，完成计数保持 12/26。

本报告直接读取固定提交的实际源码、全部 9 项完整类型、公理产物、相关依赖及原 `paper/main.tex`。执行者说明仅用于定位范围；后续工作树增量不参与本次验收。

## 全部 9 项声明

名称均加前缀 `Carleman.`，行号属于固定提交的 `Carleman/Spatial/P1CoefficientCoercivity.lean`。

| # | 声明 | 源码行 | 独立核查结论 |
|---|---|---|---|
| 1 | `p1MassMargin` | 11 | PASS；精确定义 μ(d,γ)=1−(d+1)(γ−1)²/(4γ)，没有引入依赖系数或权的常数。 |
| 2 | `p1MassMargin_pos` | 13 | PASS；原 1≤γ<Γ_d 及真实 sqrt(d+2) 恒等式推出 μ>0，未收紧 γ。 |
| 3 | `weight_deviation_bound` | 30 | PASS；对任意 1≤a≤γ 证明 |a−γ/a|≤γ−1，除数严格正。 |
| 4 | `p1CoefficientForm` | 42 | PASS；实际有限公式为 Σᵢcᵢeᵢ+(Σᵢcᵢ)(Σᵢeᵢ)，并未假定它是积分。 |
| 5 | `p1CoefficientForm_smul_right` | 45 | PASS；对任意实数 a 的右变量标量线性，直接由有限求和及乘法代数证明。 |
| 6 | `weighted_coefficient_deviation` | 57 | PASS；对任意有限索引，有限 Cauchy–Schwarz 给准确 card(ι)(γ−1)² 偏差平方界，无 c 同号要求。 |
| 7 | `weighted_p1_coefficient_coercive` | 80 | PASS；Fin(d+1) 的基数、两平方差和正 4γ 给 E(c,ω²c)≥μΣ(ωc)²。 |
| 8 | `weighted_p1_coefficient_coercive_scaled` | 104 | PASS；a>0、a≤ωᵢ≤γa 下用 ω/a，双边准确恢复 a²，μ 不变。 |
| 9 | `weighted_p1_coefficient_form_pos` | 127 | PASS；阈值下 μ>0、正权及 c≠0 给严格正值，允许任意混合符号系数。 |

## 原文定位与范围

原 `paper/main.tex:1465–1485` 的 Section 6.1 定义一致质量 P1 空间，并在 `eq:grading` 使用 `Γ_d=(sqrt(d+2)+1)/(sqrt(d+2)−1)` 与 1≤γ<Γ_d。`paper/main.tex:1506–1521` 的 Step 1 通过原四类权的邻接比较，将有效权分级控制在 `(γ+Γ_d)/2<Γ_d` 后引用 DST 得到 `eq:p1-weighted-projection`。

T052 是面向该投影稳定性目标的独立代数路线辅助步骤，不是上述原文完整命题的形式化。现有 `p1GradingLimit` 定义精确使用原根式，d=2 给 3，d=3 给 (3+sqrt 5)/2；本阶段的代数结论推广到所有 d∈ℕ。对每一个固定 d 及 1≤γ<Γ_d，都有此显式正 μ。γ 趋近阈值时 μ 可以趋于零，本报告不声称对整个开区间存在统一正下界，也不声称阈值的必要性或最优性。

未来应用还须把实际有效节点/权分级参数代入此处 γ，并证明其满足该区间，不能直接把原 mesh grading γ 与实际权分级常数混用。该识别、重心坐标一阶/二阶真实积分、单元体积系数和真实一致质量矩阵对应、完整 V_h 节点表示、节点测试构造及实际 L² 投影估计均不由本阶段结论提供。原 H² 插值/超逼近及其他 P1/连续分析义务也未完成。固定规格明确保留这些义务，与 AUXILIARY 范围相符。

## 原阈值与正强制性系数

令 s=sqrt(d+2)。由 d≥0，s>1，故原 Γ_d 的分母 s−1 严格正。γ<Γ_d 可正确交叉相乘得到 γ(s−1)<s+1，即 (γ−1)s<γ+1。γ≥1 确保左边非负，右边正，因而可以严格平方；使用真实 `Real.sq_sqrt` 得 `(γ−1)²(d+2)<(γ+1)²`，等价于 `(d+1)(γ−1)²<4γ`。γ>0 使除以 4γ 保持方向，最终 μ>0。代码没有把 sqrt(d+2) 写成 d+2，没有丢失 d+1，也没有新增 γ≤某个更小阈值。

μ 的定义对所有 γ 作为 Lean 实数运算均有意义；其正性声明只在 γ≥1 及原严格阈值下成立。归一化强制性不等式本身只需 γ≥1，即使 μ 非正也仍成立；严格正值定理才额外使用 γ<Γ_d。这些前提放置准确，未将非严格下界误称为所有 γ 下的严格正性。d=0、γ=1、ω 常数和 c=0 等情形未被不当排除。

## 偏差界、有限 CS 与两平方差

先对 1≤a≤γ 使用 a>0 及身份 `a(a−γ/a)=a²−γ`。两个非负乘积 `(a−1)(a+γ)` 和 `(γ−a)(a+1)` 分别给出下界 −(γ−1) 与上界 γ−1，形成准确绝对值界。这一步只涉及正 a；不对系数作符号假设。

令 A=Σcᵢ、B=Σωᵢ²cᵢ、S=Σ(ωᵢcᵢ)²、D=B−γA。真实逐项恒等式是 `(ωᵢ²−γ)cᵢ=(ωᵢ−γ/ωᵢ)(ωᵢcᵢ)`，除数非零由 ωᵢ≥1 给出。有限 Cauchy–Schwarz 直接作用于两个实向量，得到 D²≤Σ(ωᵢ−γ/ωᵢ)²·S；逐项偏差界给 D²≤card(ι)(γ−1)²S。它对混合符号 c 同样成立，没有把带符号和改为绝对值和。一般有限索引版本也允许空索引，此时两边为零。

在 Fin(d+1) 上，card 精确为 d+1。`p1CoefficientForm c (ω²c)=S+AB`，而 `(B+γA)²−(B−γA)²=4γAB`。由第一个平方非负可得 `4γAB≥−D²`，于是 `4γE≥[4γ−(d+1)(γ−1)²]S`，正数 4γ 消去后正好是 μS≤E。已沿此等式独立复核源码中的 `nlinarith` 步骤，其输入确实包含完整偏差平方界和另一个非负平方，未假设 AB≥0。

## 归一化、严格正值与量词

缩放版本明确假设 a>0，并把 a≤ωᵢ≤γa 转为 1≤ωᵢ/a≤γ。真实平方和满足 S(ω)=a²S(ω/a)，右变量标量线性给 E(c,ω²c)=a²E(c,(ω/a)²c)。双边同乘 a² 后恢复原式，因此 μ 仅依赖 d、γ；它不依赖局部尺度 a、系数 c、各权值 ω，也不依赖任何网格或单元几何。

严格正值版本由 c≠0 得某个 cᵢ≠0，再由 ωᵢ≥a>0 得 (ωᵢcᵢ)²>0，其余平方非负，所以 S>0。与 μ>0 相乘后接入已证下界。没有除以 S 或某个系数，零系数及正负混合均被覆盖。最终完整类型中的 c、ω 完全任意，额外前提仅为已列出的正归一化、权比区间、原阈值和 c≠0；未增加维数限制、同号性或离散目标估计假设。

## 固定声明版本与递归公理

独立检查 Carleman 导入闭包共 95 个模块，其中 94 个既有模块相对 base 逐字节不变，唯一新模块为本次模块。`Carleman.lean` 明确导入它。AGENTS、流程规则、原论文、Lean/mathlib pin 和 CI 流程未在该差异中改变。原论文 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

固定 `/tmp/carleman-coefficient-coercivity-full.log` 实际记录 `Build completed successfully (3601 jobs).`。固定 `/tmp/carleman-coefficient-coercivity-local-axioms.txt` 中 9 项完整类型与实际源码吻合，9 项递归 `#print axioms` 均仅依赖正常基础公理 `propext`、`Classical.choice`、`Quot.sound`。已核对审计程序遍历所有 Carleman（含内部生成）声明，以递归 `collectAxioms` 拒绝白名单之外的公理；产物末行确认全部 4787 项通过。显式打印的 1264 项不同声明公理集合扫描也无白名单外项，没有 sorry 或未清偿数学公理。

固定本机产物为 1,338,736 bytes，SHA256 `36e272afc0ef17837a366b82f44b035ffb4c49e1ebfe0f0ff938f44ad9771c2e`。工具链为 Lean 4.35.0，mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`。

## 远端证据及最终结论

已独立读取真实 [main/push run 39161889554](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39161889554/attempts/1)、attempt 1，head SHA 精确为本次 checked SHA，顶层 completed/success。三项 jobs 全部 completed/success：lean `117776729928`、state-check `117776730098`、dashboard / snapshot `117777313025`。Lean job 的实际构建、记录源码和上传证据步骤也全部 success。

独立核对同次产物元数据：`lean-ci-result` id `12148603292` 与 `lean-declaration-evidence` id `12149480262` 均绑定该 run 和同一 head SHA。实际读取 `/tmp/carleman-coefficient-coercivity-main-ci/result.json`：status=PASS，checked_sha/source_head_sha 均为 `df8b853f9203194295be90f39ef5f797af31b9b3`，ci_url 精确对应该 run/attempt，finished_at=`2026-10-18T20:09:18.938356+00:00`，target 为 `Carleman`。Lean 4.35.0（commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）及 mathlib 固定版本均吻合。

实际读取 `/tmp/carleman-coefficient-coercivity-main-axioms/axioms.txt` 并与固定本机产物逐字节比较：完全相同，1,338,736 bytes，SHA256 `36e272afc0ef17837a366b82f44b035ffb4c49e1ebfe0f0ff938f44ad9771c2e`。再次核对远端产物的全部 9 项完整类型及递归公理集合，均通过；末行确认全部 4787 项审计通过。

最终结论：**T052 / C068 PASS，可以将 C068 升为 REVIEWED，保留 AUXILIARY。** 9 项声明及所声称范围通过，未发现数学缺陷。系数型与真实单元积分的对应及实际加权 L² 投影稳定性仍待，不提升完整原文覆盖，完成计数保持 12/26。本 Agent 仅写本验收报告，未修改证明、台账、root 导入或原稿，未 commit/push。
