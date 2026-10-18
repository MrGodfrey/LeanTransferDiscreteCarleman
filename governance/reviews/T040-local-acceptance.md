# T040 / C056 独立本机验收

- `checked_sha`: `4f669626b3228adea39a16fbf6c1d22313763331`
- `base_commit`: `fa61af9d4b260cac83d599ef4e228af88f67aee8`
- `semantic_checked_at`: `2026-10-18T18:34:39+00:00`
- `reviewed_at`: `2026-10-18T18:38:26+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- 范围：**AUXILIARY**。完成真实 H₀¹ 的 Poincaré、纯梯度形式及 Lean `OriginalForm` 的全部字段；仅清偿原 A1 的闭合稠密空间和形式部分，**不代表原 A1 的 H² 图正则性已经清偿**。不提升 P011/P012、解析实现或其他完整论文覆盖，原文完成计数保持 12/26。

独立读取固定提交四个新模块、全部 27 项实际类型与递归公理产物、相关既有依赖及原 `paper/main.tex`。执行者的阶段说明用于定位范围，没有代替源码和数学核对；后续未提交数学文件不参与此次验收。

## 全部 27 项声明

全部名称加前缀 `Carleman.`；源码位置相对于固定提交下的 `Carleman/Spatial/`。下表 PASS 为逐项语义结论。

| # | 声明 | 源码位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `SpatialTest.zeroTest` | `SpatialTestOperations.lean:12` | PASS；真实零函数满足 C∞、紧支及支撑包含。 |
| 2 | `SpatialTest.addTest` | `SpatialTestOperations.lean:18` | PASS；实际函数相加，紧支并集与支撑包含均证明。 |
| 3 | `SpatialTest.smulTest` | `SpatialTestOperations.lean:24` | PASS；任意实数倍，含零和负系数，保留测试条件。 |
| 4 | `SpatialTest.zeroTest_jet` | `SpatialTestOperations.lean:30` | PASS；Lp 值身份结合真实弱 jet 的值单射得到完整零 jet。 |
| 5 | `SpatialTest.addTest_jet` | `SpatialTestOperations.lean:38` | PASS；由真实 a.e. 加法和值单射证明 jet 相加，无自由导数选择。 |
| 6 | `SpatialTest.smulTest_jet` | `SpatialTestOperations.lean:48` | PASS；真实 a.e. 标量乘法与 jet 标量乘法一致。 |
| 7 | `exists_test_of_mem_test_span` | `SpatialTestOperations.lean:60` | PASS；span 归纳配合前述运算，每个 span 元素本身就是一个真实测试 jet。 |
| 8 | `SpatialTest.linearMul` | `TestPoincare.lean:12` | PASS；实际 L(x)φ(x) 为 C∞ 紧支测试，支撑不超过 φ 的支撑。 |
| 9 | `SpatialTest.linearMul_derivative` | `TestPoincare.lean:18` | PASS；Fréchet 导数准确为 `L(e)φ(x)+L(x)D_eφ(x)`。 |
| 10 | `SpatialTest.weakDerivative` | `TestPoincare.lean:28` | PASS；任意方向 e 的全测试族弱导数恒等式，由实际 Lipschitz 积分分部推出。 |
| 11 | `SpatialTest.linearMul_norm_le` | `TestPoincare.lean:36` | PASS；slab 条件给真实受限 Lebesgue L2 乘法界 `‖Lφ‖≤R‖φ‖`。 |
| 12 | `SpatialTest.poincare_slab` | `TestPoincare.lean:47` | PASS；L(e)=1、R≥0 下精确得到 `‖φ‖≤2R‖D_eφ‖`，零范数单独处理。 |
| 13 | `SpatialTest.sobolevJet_derivative` | `DirichletPoincare.lean:13` | PASS；每个一阶 jet 分量与对应真实坐标方向导数 Lp 类严格相等。 |
| 14 | `derivativeComponent_norm_le` | `DirichletPoincare.lean:26` | PASS；真实 Euclidean 分量的 L2 范数受完整 fiber 的 L2 范数控制，常数为 1。 |
| 15 | `dirichlet_poincare` | `DirichletPoincare.lean:34` | PASS；将坐标 slab 估计通过实际 H¹ 图闭包传给所有 Dirichlet jet。 |
| 16 | `WeakSobolevJet.norm_zero_field` | `DirichletForm.lean:15` | PASS；零阶唯一空指标的完整 fiber 范数恰等于 scalar value 范数。 |
| 17 | `DirichletEnergy` | `DirichletForm.lean:28` | PASS；真实 Dirichlet L2 子空间在 Sobolev Hilbert 空间中的逆像。 |
| 18 | `dirichletGradient` | `DirichletForm.lean:31` | PASS；包含、真实 jet 等价及一阶场 CLM 的复合，输出完整实际弱梯度。 |
| 19 | `dirichletForm` | `DirichletForm.lean:36` | PASS；真实梯度 L2 内积给连续双线性形式，不包含零阶项。 |
| 20 | `dirichletForm_apply` | `DirichletForm.lean:40` | PASS；定义性识别为两梯度的 L2 内积。 |
| 21 | `dirichletForm_symmetric` | `DirichletForm.lean:43` | PASS；实 L2 内积对称性精确传递。 |
| 22 | `dirichletForm_integral` | `DirichletForm.lean:48` | PASS；真实积分中所有一阶 Sym 分量恰各出现一次。 |
| 23 | `dirichletEnergy_norm_sq` | `DirichletForm.lean:57` | PASS；H¹ Hilbert 范数平方准确为 L2 值平方加完整梯度平方。 |
| 24 | `dirichletForm_coercive` | `DirichletForm.lean:64` | PASS；Poincaré 给正系数 `((2R)²+1)⁻¹`，适用于每个能量状态。 |
| 25 | `dirichletOriginalForm` | `DirichletForm.lean:81` | PASS；显式 slab 下内部供应真实 V、Sobolev 包含、H¹ 闭性、L2 稠密、形式、对称与强制。 |
| 26 | `dirichletForm_coercive_of_bounded` | `DirichletForm.lean:92` | PASS；任意正维有界开集先选固定正半径与坐标，再得 `∃c>0,∀u` 的强制性。 |
| 27 | `boundedDirichletOriginalForm` | `DirichletForm.lean:103` | PASS；只输入开集、正维、有界性便构造完整 Lean OriginalForm，无目标估计假设。 |

## 原文映射与声明边界

原 `paper/main.tex:333–351` 的 (A1) 包含闭合稠密 V、连续对称强制形式，随后还要求关联算子域进入 H²ᵐ 和椭圆图估计。本阶段实现 m=1 的前一部分。Lean `OriginalForm` 的字段为 V、sobolev、closed、dense、form、symmetric、coercive；它不包含 H² 域识别或 `eq:ellreg`。因此“完整 OriginalForm”不能表述为“原 A1 全部完成”。此范围区别已通知执行者，执行者确认保留 H² 义务并将在归档措辞中澄清。

Section 3 使用上述原形式的闭合、稠密和强制性构造连续辅助问题；新对象可以供应该既有接口，但本阶段没有改变或重新证明 Section 3 的完整命题。原 Section 6.1 的 `paper/main.tex:1469–1470` 和 Section 6.2 的 `1634` 明确取 V=H₀¹(Ω)、`a(u,v)=(∇u,∇v)L2`。第 17–27 项给出的正是这两个真实数学对象，而非假设其存在的抽象替身。

原附录 `paper/main.tex:2659–2664` 的 `prop:analytic-realizations` 同时使用 H² 椭圆正则性和 Poincaré；本阶段供应其中 Poincaré 与原形式部分，但不能据此提升完整解析实现。对任意有界开集的形式构造比原凸多面体/盒子范围更广，这是正确的一般化；没有声称一般有界开集具备原 H² 正则性。

## 完整测试族、运算与弱积分分部

已直接追查 `WeakDerivative.lean`：`SpatialTest S` 是全 Euclidean 空间上的任意 C∞ 实函数，具有紧支撑且 `tsupport⊆S`。它没有把节点函数、固定有限测试族或某组特殊多项式当作完整弱测试族。对于开 S，这正是用全局零延拓表达的 C_c∞(S)。测试函数及其实际 Fréchet 方向导数均以已有 MemLp 证明构造 Lp 类，并以 `toLp_ae`/`derivativeLp_ae` 识别代表。

零、相加、任意实数倍的光滑性、紧支撑和支撑包含均由函数实际性质证明。其 jet 线性身份通过 Lp a.e. 运算及 `WeakSobolevJet.value_injective` 得到，后者由完整测试族上的分布弱导数唯一性证明。没有只检查零阶后任意指定一阶场。span 归纳的重要作用是把每个有限线性组合表示成单个测试；Poincaré 因而可在该测试上直接使用，而不是错误地用三角不等式处理可能相互抵消的线性组合。

`linearMul` 使用真实连续线性泛函 L 的点值乘 φ。L 可以在全空间无界，但乘积的支撑包含于 φ 的紧支撑，故仍是合法测试。导数公式来自实际乘法微分，不依赖目标 Poincaré。`SpatialTest.weakDerivative` 对每个方向 e 得到 `∀ψ:SpatialTest S` 的弱身份；已追查其 `weakSpatialDerivative_of_lipschitz` 依赖：由 mathlib 的全局 Lipschitz 差商积分定理和测试函数紧支撑，将全空间积分严格转换到 volume.restrict S，没有留下未证边界项或把积分分部作为输入。

slab 假设 `∀x∈S, |Lx|≤R` 在 `volume.restrict S` 的 a.e. 域成员上使用，给 `‖Lφ‖L2≤R‖φ‖L2`。该乘法界本身没有 R≥0 前提；若 R<0 而 S 非空，slab 前提不可能成立，空域时两 Lp 类为零。mathlib 使用的实际范数比较定理处理了该退化情形。后续 Poincaré 显式要求 R≥0。

令 u=φ、v=D_eφ、ψ=Lφ。由 L(e)=1 和乘法公式，代码证明

`⟨u,D_eψ⟩ = ‖u‖² + ⟨v,ψ⟩`。

把同一个 ψ 代入 u 的完整弱身份，再得到

`‖u‖² = −2⟨v,ψ⟩`。

`integral_add` 的两项通过真实 L2 内积可积性供应，a.e. 导数与函数代表也在积分中正确替换。Cauchy–Schwarz 和乘法界遂给 `‖u‖²≤2R‖v‖‖u‖`；代码将 ‖u‖=0 与 >0 分开，因此没有非法除以可能为零的范数。一般 e 不必单位长，因其长度已真实体现在 D_eφ 中；L(e)=1 是准确的尺度条件，不缺额外 ‖L‖ 或 ‖e‖ 因子。

## 真实 H₀¹ 闭包与全部梯度

已直接追查 `DirichletSpace.lean`：dirichletJetSpace 为全体真实测试 jet 的线性张成在弱 H¹ 图空间中的闭包；dirichletSubspace 为其真实 scalar value 在 L2 中的像。`mem_dirichletJetSpace_iff` 借唯一性保证只要一个 jet 的值属于该像，它就是对应 Dirichlet jet，因而没有在同一个 L2 值上附加不同梯度。

弱 jet 的图拓扑是有限乘积的 L2 拓扑；`SobolevHilbert.jetEquiv` 是其与平方和 Hilbert 实现之间的双向连续线性等价。故这里的闭包确为 H¹ 拓扑闭包，既不是仅 L2 闭包，也不是逐点收敛闭包。对原 Lipschitz 域，这正是原 H₀¹ 的闭包定义；本阶段没有增加未证明的点态零边界或节点刻画。

一阶 fiber 以 `Sym (Fin d) 1` 为指标；`Sym.oneEquiv` 将每个坐标 i 与 `Sym.cons i Sym.nil` 一一对应。`SpatialTest.sobolevJet_derivative` 核对了这个索引下的 jet 分量确为真实 D_iφ。Euclidean 分量点态模≤向量模，再经 Lp a.e. 范数比较给系数 1 的 L2 分量界，不引入 d 或其平方根因子。

取 L 为坐标投影、e 为同一坐标单位向量，L(e)=1。slab 测试估计因此给 `‖value φ‖≤2R‖field 1 φ‖`。满足该不等式的集合由两个真实连续线性字段映射和范数的连续性证明为闭集。先用测试线性闭合覆盖整个 span，再用 closure_minimal 得全部 dirichletJetSpace 中状态的同一估计，常数没有在闭包步骤改变。全过程没有假设 Poincaré、光滑逼近的目标误差界或任意网格状态已属于 H₀¹。

## 原梯度形式、范数与常数次序

DirichletEnergy 是既有 conformingHilbert 在真实 dirichletSubspace 上的实现。其元素映到弱 jet 的一阶场构成 `dirichletGradient`，该映射通过 subtype、已证连续的 SobolevHilbert.toJet 和 fieldCLM 复合而来。`dirichletForm` 直接为两个梯度在 Lp 中的内积；`innerSL` 与双线性复合供应连续性和双线性，不是另行输入某个待识别的形式或其有界常数。

实际积分公式展开 L2.inner_def 和 Euclidean 内积，恰为 `∫S Σ_i D_i u D_i v`；一阶 Sym 等价确保全坐标各出现一次。原梯度形式没有加入 `∫uv`，也没有将能量范数本身改称为梯度形式。对称性由真实实内积给出。

零阶只有一个空指标；其 Euclidean 模恰等于 scalar value 的绝对值，Lp 范数通过双向 a.e. 模比较严格相等。再展开 `SobolevHilbert.norm_sq` 的 Fin 2 求和，得到精确的

`‖u‖H1² = ‖u‖L2² + ‖∇u‖L2²`。

由 Poincaré 得 `‖u‖H1²≤((2R)²+1)‖∇u‖L2²`。分母 `(2R)²+1` 严格正，最终强制常数恰为其倒数；R=0 也不产生零分母。该常数是充分常数，并未声称最佳值。

`dirichletOriginalForm` 的 closed/dense/sobolev 字段来自已构造 Dirichlet 空间。已追查稠密性证明：L2 中与其正交的任意元素对所有真实 C_c∞ 测试配对为零，再由分布测试唯一性为零；没有假定一个未知的稠密子空间。OriginalForm 的 form/symmetric/coercive 字段则由本次梯度构造和 Poincaré 直接供应。

有界开集版的真实类型为 `IsOpen S → 0<d → Bornology.IsBounded S → ∃c>0,∀u,…`。从 hb 取得固定正范数半径 R，再选 i=0 的合法 Fin d 元素，利用 `|x_i|≤‖x‖≤R` 给 slab。R 和 c 都先于 u；只依赖固定域/坐标选择，不依赖时间、状态、网格、权、T 或方向。该结果不要求非空、连通或光滑边界，空域亦合法；d=0 的非空情形可能没有正梯度强制性，代码以 hd 排除，符合原 d≥1。

## 尚未清偿项与结论范围

尚未证明关联算子域等于 H²∩H₀¹、凸多面体/盒子的 H² 椭圆估计、完整原 A1 图正则性、原 A2/A3 的具体 Dirichlet 实现或连续热 CE。分片仿射节点函数/零延拓进入本闭包、H² 点值代表、具体网格、局部插值、投影稳定性、逆估计和数值误差也不能由本批形式构造直接推得。不得将本报告用作 P011/P012、完整解析实现或物理观测/控制覆盖的升级证据。

“真实 H₀¹ 与原形式已构造”仅指本报告明确的闭包和梯度形式；它不包含未证明的节点或边界迹等价。本阶段 AUXILIARY 定位与上述剩余义务一致，没有削弱原文结果以冒充完整覆盖。

## 固定依赖、构建及公理

四个新模块的 Carleman 导入闭包共 49 模块，45 个既有模块相对 base 全部逐字节未变；新模块均由固定 `Carleman.lean` 显式导入。原稿、Lean/mathlib pin、两个 CI 工作流相对 base 未变。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

全部 27 项与固定 C056/T040 清单、源码及显式 `#check`/`#print axioms` 一致。已逐项阅读实际类型，没有隐藏的 Poincaré、闭包逼近、形式强制性、有限网格或目标原估计前提。固定 `/tmp/carleman-poincare-local-axioms.txt` 为 1,235,338 bytes，SHA256 为 `daf2119e210979375997f5fd98f4aa9bfd1ce41ea845038a6404a34c4caf068c`。27/27 仅依赖正常基础公理 `propext`、`Classical.choice`、`Quot.sound`，末行是 `Axiom audit passed for all 4365 Carleman declarations.`。

审计工具遍历全部经 privateToUserName 归属 Carleman 的公开/私有声明，以 collectAxioms 递归收集依赖，仅允许上述三项基础公理；没有 sorryAx 或新数学公理。实际 `/tmp/carleman-poincare-full.log` 记录 `Build completed successfully (3558 jobs).`，随后完整公理审计通过。固定工具链为 Lean 4.35.0、mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`。

已独立通过 GitHub connector 读取 [main CI 39154628082 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39154628082/attempts/1)：main/push，`head_sha=4f669626b3228adea39a16fbf6c1d22313763331`，completed/success。实际三个 jobs 均成功：lean（117755420282）、state-check（117755420062）、dashboard / snapshot（117756086939）。Lean 的固定工具链、证明目标构建、checked-source 记录和声明公理上传步骤全部 success。

同次 artifact 元数据确认 `lean-ci-result`（12146487545）和 `lean-declaration-evidence`（12146482627）均绑定该 run 和同一 head SHA。已实际读取 `/tmp/carleman-poincare-main-ci/result.json`：status=PASS，`checked_sha=source_head_sha=4f669626b3228adea39a16fbf6c1d22313763331`，target=Carleman，`finished_at=2026-10-18T18:35:40.785623+00:00`，CI URL 对应上述 attempt 1。Lean 4.35.0（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）与 mathlib pin 均与固定源码一致。

正式 `/tmp/carleman-poincare-main-axioms/axioms.txt` 为 1,235,338 bytes，SHA256 为 `daf2119e210979375997f5fd98f4aa9bfd1ce41ea845038a6404a34c4caf068c`，与固定本机副本逐字节相同。另行核对其中 27/27 项完整类型和递归公理列表，只有上述三项正常基础公理；实际末行确认全部 4365 声明审计 PASS。此处没有把执行者陈述、另一提交的构建或后续草稿作为验收版本证据。

## 验收决定

**C056：PASS，可升级为 REVIEWED，scope 保留 AUXILIARY。** 27 项未发现需修复的数学、类型、代表、符号、常数或量词缺陷；同 SHA 实际 CI、完整类型和递归公理证据已齐备。仅在本报告所界定的真实 H₀¹、Poincaré 与原梯度形式范围内接受，原 A1 的图正则性及完整原文覆盖保持未清偿/原有状态，完成计数仍为 12/26。

本次仅写本报告，未修改证明、台账、原稿、root 导入或覆盖表，未 commit/push。
