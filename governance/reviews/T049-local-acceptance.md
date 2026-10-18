# T049 / C065 独立本机验收

- `checked_sha`: `99694c20834ac8d3b712f5e2d071a4e4ccfc308b`
- `base_commit`: `2ccd0e5f1ae783f69c70d18593e09c79dfe7d7bd`
- `semantic_checked_at`: `2026-10-18T19:50:27+00:00`
- `reviewed_at`: `2026-10-18T19:53:37+00:00`
- `result`: **PASS**。
- `axiom_check`: **PASS**。
- 范围：**AUXILIARY**。完整实际 H¹ 分片仿射状态上的全域加权逆估计，仍显式要求真实内球形状控制和逐单元权比较。原 allowed 权族及 ℓ/diam 与这些输入的对应尚待，不提升 P011/P012 或其他完整原文覆盖，完成计数保持 12/26。

本报告独立读取固定提交三个新模块的实际证明、全部 9 项完整类型、相关依赖、原 `paper/main.tex` 与阶段规格。后续工作树增量不参与本次验收；执行者说明及 CI 结论没有替代语义检查。

## 全部 9 项声明

名称均加前缀 `Carleman.`，源码位置相对于固定提交的 `Carleman/Spatial/`。

| # | 声明 | 源码位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `SimplicialPartition.cell_restrict_domain` | `SimplicialIntegrals.lean:15` | PASS；闭单元与内部的零测差、内部包含于开凸域，给准确的双重限制测度等式。无有限索引或非空域前提。 |
| 2 | `SimplicialPartition.integral_eq_sum_cells` | `SimplicialIntegrals.lean:22` | PASS；真实 a.e. 唯一分区给有限 indicator 和，利用实际可积性逐项积分；共享面不重复计数。 |
| 3 | `BoundedMultiplier.restrictMeasure` | `CellwiseInverseWeight.lean:12` | PASS；ν≤μ 时保留实际函数，将 a.e. 可测性和界按正确方向传到 ν。 |
| 4 | `SimplicialPartition.inverseScale` | `CellwiseInverseWeight.lean:24` | PASS；实际函数为 Σᵢ1_Kᵢ/hᵢ，有限和给真实有界乘子；其粗界不进入最终常数。 |
| 5 | `SimplicialPartition.inverseScale_on_cell` | `CellwiseInverseWeight.lean:40` | PASS；域测度 a.e. 的单元上值恰为 hᵢ⁻¹，交界上的点态多重值未被误称为唯一值。 |
| 6 | `SimplicialPartition.inverseWeight` | `CellwiseInverseWeight.lean:55` | PASS；实际逆尺度乘子与 w 的点态乘积。 |
| 7 | `SimplicialPartition.inverseWeight_on_cell` | `CellwiseInverseWeight.lean:58` | PASS；正确的域测度 a.e. 条件式，值为 hᵢ⁻¹w(x)。 |
| 8 | `SimplicialPartition.inverseWeight_sq_sum` | `CellwiseInverseWeight.lean:66` | PASS；真实加权 L² 范数平方恰为 Σᵢhᵢ⁻²∫Kᵢ|w|²|u|²，正确迁移代表身份至单元测度。 |
| 9 | `conforming_weighted_inverse` | `ConformingWeightedInverse.lean:12` | PASS；对完整 H¹ jet 且 value 属于真实 conformingSpace 的任意状态，局部真梯度识别、统一逆界及积分求和给 ‖w∇u‖≤C‖h⁻¹wu‖；C 先于全部域、网格、权和状态。 |

## 原文对应与未清偿范围

原 `paper/main.tex:1465–1497` 的 Section 6.1 指定 d=2,3、固定有界凸多面体 Ω、形状正则单纯形网格，以及 `V_h={v∈H¹₀(Ω):v|K∈P₁}`；`eq:grading` 同时规定 ℓ_K 与真实直径 h_K 的双边比较和相邻单元的 grading 条件。原 Step 2 在 `paper/main.tex:1523–1551` 先由 allowed 权的导数界推出 `eq:element-weight-comparison`，再得到 `eq:p1-weighted-inverse` 的全域估计。当前阶段准确完成显式几何和权比较输入之下的全域逆估计。

最终 hᵢ 是正数，几何要求是 `ball(aᵢ,rᵢ)⊆Kᵢ`、rᵢ>0 和 hᵢ≤κrᵢ。它尚未被定义为原 ℓ_K 或 diam(K)；还须由原形状正则性和 ℓ_K≈diam(K) 供应统一 κ 及对应的真实内球。权比较为正 sᵢ 及 `|w|≤Wsᵢ`、`sᵢ≤W|w|`，W 在全部权与网格之前固定。原 σ、σ⁻¹ 等 allowed 权在 hq≤δ_num 下如何给出统一 W 仍未证明。本批没有导出 δ_num，也没有把时间或 q 的统一性作为已经清偿的事实。

全域求和不需要相邻单元 grading 阈值或 FaceMatching：实际 H¹ 状态已在范围内，且有限分区的内部不相交足以积分。这些未使用假设的省略扩大适用范围，没有缩小原 V_h；原投影稳定性仍会需要相应 grading 条件。H² 插值、加权投影/逼近、测试估计、椭圆正则性及连续热 CE 等其余 P1 义务不由本批完成。因此不得将整个原 Proposition 6.1 或其他完整原文结果提升。

## 闭单元积分与零测交界

`SimplicialPartition` 包含真实非退化 d-simplex、闭凸包单元包含于 closure S、覆盖 S 及内部两两不交。`simplicialCells_ae_partition` 使用各单元已证的 Haar 零测边界和有限索引，得到域测度下 a.e. 唯一单元，不是把点态闭单元误作互不相交。

开凸 S 给 `interior K⊆S`；证明单独处理 S=∅，没有暗加非空域。利用 K 与 interior K 在 ambient volume 下 a.e. 相等，先传到域限制测度，再应用内部包含关系，得到 `(volume|S)|K=volume|K`。所以右侧确为完整闭单元积分，而非不明的 K∩S 积分。边界位于 ∂S 时也只差零测集合。

`integral_eq_sum_cells` 对任意真正可积实密度成立。由 a.e. 唯一性写成 Σᵢ1_Kᵢf，各 indicator 项由原 hf 得到可积性，才使用有限和积分交换。后续两处应用的密度分别由实际有界乘子作用于 L² 字段的 `integrable_density` 供应，未依赖不可积函数默认积分为零。空索引意味着 S 为空，公式及最终估计仍成立；d=0 也没有被排除。

## 逆尺度和真实代表

`inverseScale` 在共享面上可能取多个 hᵢ⁻¹ 的和；代码仅声称 a.e. 单元身份，这与 L² 乘子所需完全一致。粗全局界 Σᵢ|hᵢ⁻¹| 只用于证明乘子合法，不进入最终 C，因此不导致常数依赖单元数、最小尺度或 mesh grading。

`inverseWeight` 使用既有 `BoundedMultiplier.mul` 的实际函数乘积。`BoundedMultiplier.seminorm` 是对真正 a.e. 商 L² 类乘以该函数后取 L² 范数，并非任意指定范数。域测度下的 `inverseWeight_on_cell` 经 `volume|K≤volume|S` 按正确方向限制到单元，再结合 a.e. 属于 K 得到准确等式。平方中使用 |ab|²=a²b² 和常数提出积分，故缩放是 hᵢ⁻²，不是 hᵢ⁻¹ 或正尺度的倒置。辅助身份不要求 h 正；最终定理明确要求所有 hᵢ>0。

## 完整 H¹ 状态及实际梯度

最终声明量化任意 `V : Submodule ℝ L²(S)` 和任意 `WeakSobolevJet d 1 (volume|S) S`，只要求 value 属于 `M.conformingSpace V`。既有双向成员刻画将此空间准确识别为 V 与全部单元 a.e. 仿射多项式状态的交，不是节点系数像的子集。对于原 V=H¹₀，`dirichletSubspace` 是实际紧支光滑测试函数 H¹ 图范数闭包的 value 像，`dirichletSubspace_sobolev` 给每个成员的真实 jet；value 在开域上单射。因此以 jet 表述不会遗漏原 V_h 的状态，也不会允许为同一状态自由指定梯度。

已直接检查 `conforming_local_polynomial` 及其调用链：先从成员刻画取得真实 AffineMap p；将实际弱 jet 限制到单元内部；仿射函数的 CLM 导数由 Lipschitz 积分分部得到弱导数，再由完整测试族的唯一性识别所有方向；最后使用零测边界传回闭单元。得到的 `field 1 u` 等于真实 `derivativeOneFiber(fderiv p)`，其 fiber 是全部 Euclidean 坐标导数的 ℓ² 范数。最终积分采用这个真实全梯度，未使用独立“能量”输入。没有节点表示、额外状态光滑性或 FaceMatching 前提。

## 统一常数和全域组合

实际完整类型的量词为：∀d κ W，κ>0、W>0 ⇒ ∃C>0，随后才量化索引类型 ι、Fintype、S、M、域性质、有限测度实例、a/r/h、几何证据、w/s、比较证据、V 和 u。构造 C 时只调用 `simplex_weighted_inverse_integral d κ W`。该依赖的共同参考单元仅依赖 d，真实仿射参数化处理任意物理单纯形；其局部权归一化 s 精确消去，C 可依赖 d、κ、W，不能依赖物理单元或 w 的有界乘子粗界。

将 w 按真实测度单调性限制到每个单元，点态值不变，故局部比较假设直接适用。每个单元先得到 ∫Kᵢ|w|²|∇u|²≤(C/hᵢ)²∫Kᵢ|w|²|u|²。之后是精确求和、提出共同 C²、使用实际逆权平方身份，再利用两边非负从平方不等式返回范数不等式。没有使用带单元数因子的三角不等式，也没有全域最大尺度替代局部 hᵢ。零状态或零梯度不会触发除以状态范数；正 C、hᵢ、sᵢ 的使用位置正确。允许带符号实权是对正原权情形的扩大。

## 固定声明版本与公理依赖

三个新模块从固定 Git 源码读取；它们的 Carleman 导入闭包共 87 个模块，其中 84 个既有模块相对 base 逐字节不变。`Carleman.lean` 明确导入全部三个模块。原论文、Lean/mathlib 固定版本与 CI 流程没有被此批改写；原论文 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

固定本机完整日志 `/tmp/carleman-global-inverse-full.log` 实际含 `Build completed successfully (3592 jobs).`。固定 `/tmp/carleman-global-inverse-local-axioms.txt` 的 9 项完整类型与本次源码吻合，9 项递归 `#print axioms` 全部仅有 `propext`、`Classical.choice`、`Quot.sound`。已检查审计程序逐个遍历所有 Carleman（含内部生成）声明，并递归 `collectAxioms` 后拒绝其余公理；产物末行是 4733 项全部通过。产物还显式打印了 1219 项不同声明的递归公理集合，扫描未见白名单外项。没有 `sorryAx` 或未清偿数学公理。

本机固定产物为 1,317,258 bytes，SHA256 `2384a7eac07fcf000a13e495cd17a5038dbd4ea911b072e3a5088351faf7399f`。固定工具链为 Lean 4.35.0，mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`。

## 远端证据及最终结论

已独立读取真实 [main/push run 39160438454](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39160438454/attempts/1)、attempt 1，head SHA 精确为本次 checked SHA，顶层状态 completed/success。三项 jobs 均 completed/success：state-check `117772423589`、lean `117772423899`、dashboard / snapshot `117773001964`。Lean job 中构建、记录 checked source、上传两项证据的实际 steps 全部 success。已核对同次产物元数据：`lean-ci-result` 为 `12147564972`，`lean-declaration-evidence` 为 `12147544817`，均绑定同一 run 和 head SHA。

已实际读取 `/tmp/carleman-global-inverse-main-ci/result.json`：status=PASS，checked_sha 与 source_head_sha 都是 `99694c20834ac8d3b712f5e2d071a4e4ccfc308b`，ci_url 对应该次 run/attempt，finished_at=`2026-10-18T19:50:10.312679+00:00`，target 为 `Carleman`，Lean 4.35.0（commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）和 mathlib 固定提交均一致。

已实际读取 `/tmp/carleman-global-inverse-main-axioms/axioms.txt` 并与固定本机副本逐字节比较：完全相同，1,317,258 bytes，SHA256 `2384a7eac07fcf000a13e495cd17a5038dbd4ea911b072e3a5088351faf7399f`。再次在远端产物中核对全部 9 项实际完整类型和递归公理白名单，且末行确认 4733 项全部审计通过。

最终结论：**T049 / C065 PASS，可以将 C065 升为 REVIEWED，保留 AUXILIARY。** 本批 9 项声明及所声称范围通过，未发现数学缺陷。原 allowed 权比较、原 ℓ/diam 与几何输入的对应仍待；不提升 P011/P012 或其他完整原文覆盖，完成计数保持 12/26。本 Agent 只写本验收报告，未修改证明、台账、root 导入或原稿，未 commit/push。
