# T191 / C207 独立本机验收：时间取样、差商与有限张量测试

- `checked_sha`: `ec7ddbfba0b338f3ba97039442ed5c2108ac99aa`
- `base_commit`: `f0ab18741c799cd2d821174cfce77ffbb454fa20`
- `reviewed_at`: `2026-10-20T01:32:24+00:00`（UTC；签发后冻结）
- `reviewer`: 独立本机 Agent `/root/accept_spatial_lemma`，没有参与本批证明实现。
- `result`: **PASS，18/18 公开显式声明；另一个 private 辅助证明亦通过语义检查**。
- `axiom_check`: **PASS**；`scope`: **AUXILIARY**。C207 可按此精确版本登记独立验收通过；原文覆盖仍为 **17/26**，不提升整个 P021。

## 固定版本、原文与方法

直接读取固定 Git 对象的三个新模块全部源码、完整证明与固定原始审计中的十八项展开类型，读取 `governance/analysis/T191-time-tests.md`、`governance/MATH_SPEC.md` 的 T191 段落和唯一台账中 T191/C207 的实际记录。模块及声明名单分别为 `/tmp/carleman-t191-time-tests-modules.json`、`/tmp/carleman-t191-time-tests-declarations.json`。不把说明文字、旧报告、构建成功或执行者口述当作数学验收。

固定 `AGENTS.md`、`governance/PROJECT_OPERATIONS.md`、`state/README.md`、MILESTONES、PAPER_COVERAGE 与本 Agent 已完整读取的 T189 版本逐字节相同，沿用其固定声明、独立语义和真实同 SHA CI 要求。核对原 `paper/main.tex:2926–2956` 的有限张量测试、前层取样、差商、端点及势乘积步骤，及 `2387–2400` 中这些测试在控制极限中的用途。原稿 SHA256=`492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，没有修改原稿。

原稿使用固定有限和 `Σₗηₗ(t)ψₗ(x)`，ηₗ 在闭时间区间光滑，空间测试具有实际紧支撑。本批证明时间部分以及**输入空间强逼近后**的张量组合。它没有定义或识别原 I_hψₗ，也没有把空间逼近、产品 L∞ 测试收敛或状态方程极限包装成已经完成的结论。

## 十八项完整声明

下表路径相对固定提交的 `Carleman/Control/`；raw 行指自行下载且与固定本机副本相同的 `axioms.txt` 中展开类型起始行。共 **17 个公开 theorem、1 个实际 def**；另检查一个 private theorem，不把它漏在审查之外。

| 完整声明 | 固定源码 / raw 行 | 实际类型与数学检查 | 结论 |
| --- | --- | --- | --- |
| `Carleman.fixedTimeCellIsometry_eq_reconstruction` | `TimeTestDifference.lean:14` / 36220 | 真实标量胞元等距与同值数组的 Bochner 重构严格相等，使用双方 a.e. 指示和及 Lp.ext。 | PASS |
| `Carleman.timeCell_derivative_average` | `TimeTestDifference.lean:22` / 36224 | 原胞元导数平均等于真实后向差商；前提只有区间内 HasDerivWithinAt 和 f 的 L² 可积性。 | PASS |
| `Carleman.timeCell_test_difference_eq_projection` | `TimeTestDifference.lean:46` / 36230 | 差商重构恰为同一胞元等距 E 与其真实伴随 E* 作用于 f 的 L² 类；未假设目标身份。 | PASS |
| `Carleman.fixedTimeCell_test_difference_eq_projection` | `TimeTestDifference.lean:61` / 36238 | 沿 period=T 运输到固定实际时间 L²，保留同一投影和差商。 | PASS |
| `Carleman.time_test_difference_strong_convergence` | `TimeTestDifference.lean:71` / 36246 | 固定 T、dt→0 时差商在真实 L² 中趋于 f；内部调用已证明的全 L² 平均投影强收敛。 | PASS |
| `Carleman.time_test_left_sample_error` | `TimeTestSampling.lean:13` / 36258 | 闭区间 C-Lipschitz 的真实左端取样误差 ≤ C·dt·√T，保留准确时间质量及未覆盖区处理。 | PASS |
| `Carleman.time_test_left_sample_strong_convergence` | `TimeTestSampling.lean:64` / 36264 | 从上述误差夹逼给真实前层取样的强极限，无嵌套前提。 | PASS |
| `Carleman.continuous_time_memLp` | `TimeTestSampling.lean:76` / 36272 | 闭区间连续函数由真实紧性界与有限限制测度得到 MemLp。 | PASS |
| `Carleman.time_test_lipschitz` | `TimeTestSampling.lean:83` / 36275 | 区间内真实导数及其连续性内部给同一区间上的 Lipschitz 常数；无区间外假设。 | PASS |
| `Carleman.smooth_time_test_consistency` | `TimeTestSampling.lean:93` / 36279 | 同时输出前层取样和差商两个强极限；实际输入只需闭区间 C¹ 数据，内部供应两份 MemLp 和 Lipschitz 常数。 | PASS |
| `Carleman.timeTensor` | `TensorTimeTests.lean:23` / 36293 | 真正连续双线性映射 H→L²(时间;ℝ)→L²(时间;H)，由原标量乘法及 compLpL₂ 构造。 | PASS |
| `Carleman.timeTensor_ae` | `TensorTimeTests.lean:27` / 36301 | 实际 Lp 代表等于 t↦f(t)•v，按 a.e. 而非任意代表的逐点相等处理。 | PASS |
| `Carleman.timeTensor_reconstruction` | `TensorTimeTests.lean:31` / 36305 | 同一实际张量映射与固定时间指示重构严格交换。 | PASS |
| `Carleman.timeTensor_strong_convergence` | `TensorTimeTests.lean:41` / 36310 | 两个变化因子沿同一 n 强收敛时张量强收敛，调用实际双线性连续性。 | PASS |
| `Carleman.tensor_time_test_consistency` | `TensorTimeTests.lean:47` / 36318 | 同一变化空间因子 vₙ→v₀ 与时间取样/差商组合，得到真实 Bochner 两个强极限。 | PASS |
| `Carleman.fixedTimeCellReconstruction_sum` | `TensorTimeTests.lean:65` / 36336 | 真实 Lp 重构保持任意固定有限和；逐项 a.e. 身份只作有限合并。 | PASS |
| `Carleman.finite_tensor_time_test_consistency` | `TensorTimeTests.lean:83` / 36341 | 任意固定有限张量整和的取样及**整和差商**强收敛；空间强逼近 hv 明确保留。 | PASS |
| `Carleman.finite_tensor_test_endpoint_consistency` | `TensorTimeTests.lean:110` / 36361 | 对每个固定 τ 的同一空间张量和强收敛，特别包含 0、T；不声称状态端点。 | PASS |

全部十八项在固定根模块实际导入范围内，在 `tools/CheckAxioms.lean` 均有 `#check @...` 与 `#print axioms ...`。表中类型的全部量词、类型类和假设均已读取；没有未公开的光滑代表或空间一致性条件藏在定义中。

## 真实胞元、区间内 FTC 与差商

实际 `TimeGrid` 有 steps>0、dt>0，period=steps·dt。新的差商使用实数时间 `i.val·dt` 和 `(i.val+1)·dt`；最后一个胞元的右端确为 T，而不是有限指标的循环 successor。虽然共享数据结构还服务周期问题，本批完全没有调用 next/prev、没有要求 η(0)=η(T)，因此不会把原物理时间端点周期化。

`timeCell_derivative_average` 首先由 i<steps、dt>0 证明闭胞元 `[nodeTime i,nodeTime i+dt]⊆[0,T]`。f 在整个受限时间域的 L² 资格，经有限测度得到 L¹，再沿真实限制测度单调性得到每个胞元的可积性。通过 `intervalIntegrable_iff_integrableOn_Ioc_of_le` 转为实际 IntervalIntegrable，未对不可积函数形式使用 FTC。

φ 的闭区间连续性由每点的 HasDerivWithinAt 内部推出。对胞元内部 t，证明 0<t<T，从而 `[0,T]` 是 t 的邻域，才能把原 within 导数转为 HasDerivAt。端点仅使用闭区间连续性；没有把 t=0 或 T 当作整个实轴内点来要求外侧导数。随后调用固定 mathlib 的 `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`，并以 `integral_of_le` 将区间积分恢复成原左开右闭胞元积分。已直接读取该 FTC 的实际前提和实现路径，所需连续性、内部导数、可积性均在本地清偿。

因此结论是实际 `dt⁻¹∫cell f = dt⁻¹(φ(tᵢ₊₁)−φ(tᵢ))`；没有使用一个人为命名的“导数”，f 与 φ 的关系由完整区间内真实导数前提约束。最初 FTC 定理并不要求 f 连续；f 的 L² 资格和逐点导数关系已足够。后续闭区间 C¹ 实例则进一步内部提供 f 的 MemLp。

差商投影身份先比较 `fixedTimeCellIsometry` 和时间指示重构的实际 a.e. 代表，再用实际 Hilbert 伴随胞元平均公式。`hf.toLp f` 的代表仅 a.e. 等于原 f，证明显式将 `hf.coeFn_toLp` 限制到该胞元并以 `integral_congr_ae` 换元。这一步没有把 Lp 商类的任意代表拿到节点求值：节点值取的是给定的区间连续/可微函数 φ，导数类只用于积分。

EE* 确是原胞元等距及其真实 Hilbert 伴随，不是任意投影。重读依赖中的胞元等距、平均公式、正交残差与最佳逼近、稠密有界连续函数的收敛及一般 L² 的稠密延拓。`fixedTimeCell_average_strong_convergence` 内部由胞元距离≤dt、实际未覆盖测度为零及 dt→0 实现其全部前提。于是新定理是在固定 L² 空间中应用已有全 L² 强收敛，既没有把差商收敛当作假设，也没有要求时间网格嵌套。

## 前层取样、常数与固定 T

前层取样取 `φ(nodeTime i)`，在真实胞元内 `0<t−nodeTime i≤dt`，故原区间上 Lipschitz 界给 `|φ(t)−φ(nodeTime i)|≤C·dt`。Lp 代表替换均显式使用 `coeFn_toLp`。节点在闭区间内，包括最初 t=0；最后取样点是 T−dt，和原 `φ_h^(n−1)` 完全一致。

证明没有直接略去未覆盖项：先使用真实有限胞元误差公式 `‖u−Ev‖²≤ε² μ(univ)+B² μ(uncovered)`。其中全域 bound `|φ(0)|+C·T` 在闭区间内部证明，原时间胞元的互不相交、质量 dt 及 steps·dt=T 给真实未覆盖测度=0。再用 `μ(univ)=T` 得平方误差≤C²dt²T，两边非负后取平方根，准确恢复 **C·dt·√T**。没有遗漏 √T，也没有把正体积空间边界条带的事实错误移用于这里。

`time_test_lipschitz` 仅从闭区间连续导数的紧性界 B，选 C=max(0,B)，并调用凸区间上的真实 within 导数均值定理。已读 mathlib 的 `lipschitzOnWith_of_nnnorm_hasDerivWithin_le` 实现，导数界在所有区间点成立，所需凸性内部供应。该 C 依赖固定时间区间及固定测试函数/导数，不依赖任何网格或空间因子；原稿此段本来固定 T，因此报告不声称 C 对所有 T 一致。两个 MemLp 都由闭区间紧性与有限时间测度给出，最终 C¹ 接口不再要求调用者另给 Lipschitz 常数或可积性。

各收敛定理的额外 `0≤T` 是原 T>0 的弱化形式，并且只要有 `g.period=T` 便已由正 TimeGrid 自动满足。没有新增 T 下界或上界，也没有全实轴连续、可微、有界或全局 Lipschitz 假设。虽然函数在类型上写为 ℝ→ℝ，区间外的取值从未被正则性前提约束。

## 真实张量、private 引理与有限和

实际 `timeTensor` 是 `((smulRightL ℝ ℝ H) (id ℝ ℝ)).compLpL₂ 2 μ`，不是为预定结论选择一个 Hilbert 同构。已读 mathlib `compLpₗ₂/compLpL₂` 的实现：每个固定 v 使用真实 CLM 在 Lp 中复合，a.e. 身份供应对 v 的线性，`norm_compLp_le` 和 `le_opNorm` 给实际连续双线性界。新的 `timeTensor_ae` 又直接公开同一映射的实际代表 `f(t)•v`；与时间重构交换则使用已接受的 `fixedTimeCellReconstruction_map`，该依赖同样是按真实 a.e. 指示和证明。

H 只要求实赋范空间，不附加有限维、Hilbert、可分或完备性假设；这些声明本身只需要 Lp 的赋范空间结构。因而可分别在原 L² 空间、真实 H¹₀ 载体或弱梯度值空间实例化，仍须向对应实例供应其明确的空间强极限。没有额外选择改变这些空间的原范数。

`TensorTimeTests.lean:15` 的 private `bilinear_seq_tendsto` 已逐字读取完整类型和证明：对任意真实 `B : E→L[ℝ]F→L[ℝ]G`，从 vₙ→v₀、fₙ→f₀，直接把 `B.continuous₂.tendsto (v₀,f₀)` 与 `hv.prodMk_nhds hf` 复合。它不是被公理化的收敛原则，也不含额外有界或目标极限前提。使用同一 n 的乘积收敛，不作两个极限的迭代交换。该 private 声明由全环境递归公理审计涵盖，且被公开的张量强收敛证明实际调用。

局部 `attribute [local irreducible] timeTensor` 和单条 theorem 的 transparency 选项只控制 elaborator 展开。其前面实际 def、a.e. 代表及重构交换已经证明，后面的强收敛把**同一个**连续双线性对象送入 private 引理；没有引入新的 opaque axiom、替换数学定义、取消字段或通过未检验计算完成证明。核对公开类型和最终递归公理信息亦与此一致。

`fixedTimeCellReconstruction_sum` 在 Lp 中证明严格有限和身份，使用有限类型 ι 上 `eventually_all` 合并例外集，再将时间胞元和与有限张量和交换。没有对不可数测试换取一个统一零测例外集。最后的差商结论确实是 `dt⁻¹ • ((Σₗηₗ(tᵢ₊₁)vₗ,ₙ)−Σₗηₗ(tᵢ)vₗ,ₙ)`；证明显式分配整和差、标量乘法和同一空间因子，再对各项强极限求有限和。不是只证明逐项差商而漏掉原整和身份。ι 固定但任意有限，空和也合法。

最终前提 `∀ l, Tendsto (v l) atTop (𝓝(v₀ l))` 是**明确保留的空间强逼近输入**。实际定理没有网格 h，也没有把空间逼近速率与 dt 相除；dt→0 和各 vₗ,ₙ 的强收敛沿同一序列足够，无 h/dt 条件、嵌套或额外一致性预算。端点定理对每个固定 τ 以常数数乘连续性与有限和处理，覆盖 τ=0、T；它不识别状态 y 的连续端点，也不允许把变化中的任意 τₙ 当作该声明的结论。

## 依赖闭包、前置报告和范围

递归解析三模块的所有 Carleman 导入，闭包共 **69 个模块**，本批新增3个、旧66个。全部66个与 mathematical_base 逐字节相同；从 base 到 checked SHA 的 `Carleman/` 改动也恰是本批三个新模块。关键入口的完整闭包另与已接受版本逐字节比较如下：

| 入口 | 已接受固定版本 | 闭包数 | 变化 |
| --- | --- | --- | --- |
| `Control/FixedTimeCellStrongConvergence` | `01d32d5c9dc4a907e058d302714a3f64366e8767`（T184） | 30 | 0 |
| `Control/TimeReconstructionEstimates` | `69cee61bd440c386c2ac20af6104f72e98b3563c`（T187） | 24 | 0 |
| `Control/DirichletTimeWeakCompactness` | `32711e6669f223eba5851b43e9ec886a40c45b6e`（T188） | 59 | 0 |

已完整读取 T190 冻结报告 `governance/reviews/T190-local-acceptance.md`，提交 `1fa4fcec70aa9fb41e099d42f8812ed5a31c760a`，checked SHA 为本批 base，reviewed_at=`2026-10-20T01:13:32+00:00`，20/20 PASS、AUXILIARY。核对其工作区字节与冻结提交一致，19041 bytes，SHA256=`acf4b7797335f50a82a64ec6ebc90c9f0c123b49e2409a4fdec5a3f5cc305fd4`。

T189 的有限网格弱恒等式和 T190 的 Bochner/产品 L² 桥是主线已接受的组合背景；本批三个模块的实际证明并不调用它们去完成极限 PDE。新张量构造直接使用真实标量乘法的 Lp 映射，不能把较大的项目依赖记录误读为已经调用 T190 推出了所有乘积收敛。实际用到 T188 的是重构与 CLM 交换接口，而非假装调用紧致性得到了此处强收敛。

本批清偿时间取样、差商以及给定空间强逼近后的有限张量组合。原 I_h 的完整空间实例、E_h 测试的产品 L∞ 一致性、原势与测试乘积的完整强极限、各弱配对传极限及状态初终端点仍须后续证明；不据本批提升 P021 或原附录整段的一切结论。没有发现超出所声明 AUXILIARY 范围的隐藏额外假设。

## 构建、公理与真实同 SHA CI

只采用正式最终日志：`/tmp/carleman-t191-target5.log`（104 bytes，SHA256 `bb88415f6fa637a31000be3cbc376a92d647d80e9d0522fdf40f13aa6abc75b2`）明确 **3221 jobs 成功**；`/tmp/carleman-t191-time-tests-build.log`（80 bytes，`db244ec800a7d5f8a0777942e97ac727f70ede95f464918ee605b2f1eb05539e`）明确 **4173 jobs 成功**。`-axioms.log` 为零字节 stderr，但成功依据是完整 raw 的实际审计末行，不从空输出推断完成；早期 probe/运行中日志不作为最终验收证据。

固定 raw 实际解析到 **3356 条带公理记录、9 条无公理记录、3361 个不同显式名称**；十八项均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。另读固定 auditor 的真实实现：遍历环境中所有 Carleman 前缀、对 privateToUserName 还原后的名称同样处理，每项 collectAxioms 并拒绝白名单外依赖。实际末行是 **`Axiom audit passed for all 8602 Carleman declarations.`**，包含 private 辅助及生成声明，和显式打印数不是同一计数口径。没有 sorryAx、未授权数学公理或把目标一致性作为公理。

工具链固定 Lean **4.35.0**，编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib **`56a005855ea17e0b0958f73ec801ae140b0a1679`**，实际本机 HEAD 匹配且干净。工具链、manifest、两个 workflow、lean_ci.sh 与 T189 已检查版本全部相同。已直接读取固定 mathlib 的 FTC、within 导数均值界及 compLpL₂ 实现，而非仅凭声明名接受它们。

本 Agent 按精确 SHA 独立发现 [main run 39353514491 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39353514491/attempts/1)，并独立访问 run、完整分页 jobs、工件和 main 分支 API。实际 main SHA 与本批完全相同；run 为 `event=push`、`head_branch=main`、`head_sha=ec7ddbfba0b338f3ba97039442ed5c2108ac99aa`，最终 **completed/success**，updated_at=`2026-10-20T01:31:32Z`。三作业实际 head_sha 均相同，最终结果如下：

| 作业 | job ID | 实际状态 | completed_at UTC |
| --- | --- | --- | --- |
| lean | `118402967452` | completed / success | `2026-10-20T01:31:23Z` |
| state-check | `118402967793` | completed / success | `2026-10-20T01:27:30Z` |
| dashboard / snapshot | `118404162295` | completed / success | `2026-10-20T01:31:31Z` |

读取的全部步骤也均 success，包括真实构建、测试、审计工件上传、同次快照及最终 Complete job。工件出现时 lean 的缓存清理尚未结束，彼时没有提前签发；等待三个作业及 run 真正完成后才记录本报告时间。本次无需使用摘要迟滞的完整日志替代规则。

本 Agent 自行执行两次 `gh run download 39353514491`，两次实际 exit 0，分别下载 `lean-ci-result` 至 `/tmp/carleman-t191-time-tests-main-ci`，`lean-declaration-evidence` 至 `-main-axioms`，未使用 root 副本。原始 API 工件均绑定此 run/main/精确 SHA：

| 工件 | artifact ID | ZIP bytes / GitHub SHA256 |
| --- | --- | --- |
| lean-ci-result | `12234726928` | 492 / `e2263a548b3d033e336acfc3176abb6d2bd321c58ab51aba96295cbebe7e2256` |
| lean-declaration-evidence | `12234617230` | 256394 / `d4bd67d8747d1b3ad2bf8ff05e3ef2223e0c5e3d6866cdffd37defa57f9c85c8` |

实际 `-main-ci/result.json` 为 **537 bytes**，SHA256=`3e2bfe6262c85d5d47ae95597922691dc2f406d25c799a1dbc9826f7149ffe22`；status PASS，checked_sha=source_head_sha=本批精确 SHA，targets 为 Carleman，ci_url 精确对应上述 run/attempt，finished_at=`2026-10-20T01:30:20.769658+00:00`，Lean/mathlib pin 匹配。

实际 `-main-axioms/axioms.txt` 与固定 `/tmp/carleman-t191-time-tests-local-axioms.txt` **逐字节完全相同**：**2777527 bytes**，SHA256 **`31d23366d5b7b32ed84cae890f104d69a3df962ab7fca9829b263c9086643d73`**，十八项完整类型与公理记录、8602 项递归审计均在同一文件中。这里展开文件的摘要与上表 ZIP 摘要分开记录，没有混用。

独立 API 原始 JSON 留存于 `/tmp/carleman-t191-time-tests-review-run.json`（15324 bytes，SHA256 `285b90630fb99ef0878caaee1ddc5726c9020cc497228ead77293d67ab401bc7`）、`-review-jobs.json`（11819 bytes，`d21712791e2e69fd6651d97ac5c931c6e02d6f188d90a8184db3e05e0b0a53f6`）、`-review-artifacts.json`（1816 bytes，`f210ea5e47e12e7de6844d29988fbcc26d4496e69c03d28121158e4c20f7d820`）、`-review-main.json`（4617 bytes，`21b6c5faf9e9d88dc70291cc4676d7e0c5a1c7490785866ccba7cb778bbffd08`）。

## 判定与冻结

**T191/C207：PASS，18/18 公开声明及 private 辅助证明语义通过，axiom_check PASS。** 实际区间内 FTC、原胞元平均、前层取样误差、真实 Lp 代表、双线性张量、整和差商与固定端点全部符合声明；空间逼近作为明确辅助输入保留。没有阻断或需要修复后重验的数学缺陷。

保持 **AUXILIARY、17/26**；不提升原空间测试/L∞ 一致性或整个 P021。本报告是唯一仓库写入，单文件提交，不修改实现、台账、根导入、公理脚本、原稿或其他报告，不推送。签发时间及正文定稿后冻结。
