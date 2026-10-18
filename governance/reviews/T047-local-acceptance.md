# T047 / C063 独立本机验收

- `checked_sha`: `ce719d2683c7509827e457ea2e15e0ce5451b487`
- `base_commit`: `0c632f37eadbcece6459555fef22a2bb4b3ca688`
- `semantic_checked_at`: `2026-10-18T19:35:03+00:00`
- `reviewed_at`: `2026-10-18T19:38:33+00:00`
- `result`: **PASS**；C063 可升 REVIEWED，范围保持 AUXILIARY
- `axiom_check`: **PASS**；同次远端原始产物与固定本机副本逐字节一致
- `scope`: **AUXILIARY**
- 范围：任意真实非退化全维单纯形的共同参考参数化，以及显式形状和单元权比较条件下的统一局部加权逆估计。不提升 P011/P012 或其他完整原文结果，原文仍为 12/26。

独立读取固定两个新模块全部证明、11 项实际展开类型、实际相关旧依赖及原论文 Section 6。规格和执行者说明只用于定位，不代替数学验收。后续 SubdomainRestriction 等工作区草稿不在本次范围。

## 全部 11 项声明

完整名称均加前缀 `Carleman.`；位置相对于固定提交的 `Carleman/Spatial/`。与 C063、T047 和交付 JSON 清单逐项一致，以下为逐项语义结论。

| # | 声明 | 位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `simplexCoordinateLinearEquiv` | `SimplexReferenceMap.lean:10` | PASS；两组实际顶点差线性基之间的等价，经有限维连续性得到真实连续线性等价。 |
| 2 | `simplexCoordinateLinearEquiv_sub` | `SimplexReferenceMap.lean:14` | PASS；对全部顶点 i 精确映射 Tᵢ−T₀ 到 Uᵢ−U₀，i=0 分支单独处理。 |
| 3 | `simplexCoordinateShift` | `SimplexReferenceMap.lean:25` | PASS；实际平移 U₀−A(T₀)，保证基点也准确对应。 |
| 4 | `affineSimplex_coordinate_eq` | `SimplexReferenceMap.lean:28` | PASS；逐顶点验证 Ax+b=Uᵢ 后用真实单纯形外延性得整个 affineSimplex 等于 U。 |
| 5 | `referenceSimplex` | `SimplexReferenceMap.lean:42` | PASS；仅以 n 为输入，从 Fin(n+1) 索引的实际 AffineBasis 选择固定非退化 n-simplex，含 n=0。 |
| 6 | `simplex_shape_inverse` | `SimplexReferenceMap.lean:48` | PASS；同一 referenceSimplex n 的已证形状逆界经精确参数化覆盖所有 U，常数先于单元、内球、尺度和系数。 |
| 7 | `simplex_weighted_shape_inverse` | `SimplexWeightedInverse.lean:12` | PASS；真实乘子上下界与无权逆界组合，局部正尺度 s 精确消去，C=W²R(n,κ)>0。 |
| 8 | `simplex_local_weighted_inverse` | `SimplexWeightedInverse.lean:42` | PASS；任意真实仿射 p 的全空间再现加两个 a.e. 身份，通过 Lp.ext 转到实际 u/g；未对任意 Lp 类取节点值。 |
| 9 | `simplexNodalLp_weighted_sq` | `SimplexWeightedInverse.lean:72` | PASS；真实乘子范数平方精确为单元上的 |w|²|p|² 积分。 |
| 10 | `simplexNodalGradientLp_weighted_sq` | `SimplexWeightedInverse.lean:81` | PASS；同一真实 fderiv 的全部一阶坐标 fiber 给 |w|²‖∇p‖² 积分。 |
| 11 | `simplex_weighted_inverse_integral` | `SimplexWeightedInverse.lean:91` | PASS；两侧非负时合法平方局部逆界，准确系数 (C/h)²，适用于全部真实仿射 p。 |

## 原文目标与本次实际范围

原 `paper/main.tex:1469–1485` 将 P1 空间定义为实际 H¹₀ 中逐单元为仿射多项式的函数，并取 h_K=diam K、统一形状正则单纯形网格。Section 6.1 Step 2（1523–1551）先证明 `eq:element-weight-comparison`，然后以局部逆估计和 ℓ_K≈h_K 推出 `eq:p1-weighted-inverse`：对全部 z_h∈V_h，‖σ∇z_h‖L²(Ω)≤C‖ℓ⁻¹σz_h‖L²(Ω)。

本次实质完成此前尚待的“任意物理单纯形来自同一参考单元”及“具有统一单元内比较常数的权可加入局部逆界”。最终定理中 U 是实际非退化全维单纯形，球包含和 h≤κr 是明确的几何输入；h 是任意满足条件的正尺度，未在本批定义为 diam U。与原文的 h_K 和 ℓ_K 识别、原 allowed 权族从 hq≤δ_num 推出 W 统一界、全 V_h 弱梯度限制及全网格求和均尚未清偿。

因此不能将本批解释为原 `eq:p1-weighted-inverse` 的完整全域证明。原文 d=2,3 的局部单纯形情形在这些声明的全部 n∈ℕ 范围内，但具体网格几何、允许权族和全局状态仍须正确实例化。`extra_hypotheses=[]` 只能针对上述公开范围的辅助目标理解。

## 共同参考单纯形与零维情形

对任意两个 `Affine.Simplex ℝ (SpatialCoordinates d) d`，simplexAffineBasis 利用 d+1 个实际仿射独立顶点和全维 affineSpan_eq_top 构造真实仿射基。固定 mathlib 的 `AffineBasis.basisOf 0` 以 `{i : Fin(d+1) // i≠0}` 为指标，元素精确是 Tᵢ−T₀；`Module.Basis.equiv` 经相同指标的 Equiv.refl 将这一基映射到 U 的对应基。这里没有任意矩阵或人为假设的“坐标等价”。其连续性来自有限维性，可逆性来自真正的 LinearEquiv。

第 2 项在 i≠0 时直接使用 `equiv_apply` 和 `basisOf_apply`；i=0 时两边为零。第 3 项的 b=U₀−A(T₀) 使第 4 项逐顶点计算为 A(Tᵢ−T₀)+U₀=Uᵢ。因此实际顶点标签全部保持，非仅凸包相同；后续相同节点系数的多项式和梯度无需额外置换。

referenceSimplex 的唯一显式参数为 n。固定 mathlib 的 `exists_affineBasis_of_finiteDimensional` 在 card Fin(n+1)=finrank(SpatialCoordinates n)+1 下给真实 AffineBasis；源码由它的实际点族和 affine independence 构成 simplex。选择发生在所有 U、κ、权和多项式之前，不会为每个物理单元更换参考形状。非构造性的 Classical.choice 是正常基础公理，其选择不影响最终常数的量词统一性。

当 n=0 时 Fin(n+1) 仍有顶点 0，删去它的基指标为空，模型空间确为零维；基等价与其有限维连续性仍成立。此前已证的 opNorm_le_of_unit_norm 不需要单位球面非空，实际导数 fiber 也是零维。最终定理仍明确输入 r,h>0，不把这里的 h 宣称为零维单元的零直径。因此没有隐藏 0<n 或非空单位球前提，也没有除以 n。

## 几何依赖、真实范数与统一常数

直接复核被调用的 affineSimplex_shape_inverse，而非只依据 [T046 验收报告](T046-local-acceptance.md)。该定理先由固定参考紧凸包选 R>0，再由实际内球中的 a 与 a+(r/2)x 的两点逆像得到 ‖A⁻¹‖≤4R/r；h≤κr 给 ≤4Rκ/h。参考局部 L² 逆界、真实 Fréchet 链式法则及 Lebesgue 换元在旧依赖中组合，Jacobian |det A|>0 在函数和梯度范数平方中一致消去。因此这个依赖不是把最终逆界或几何预算作为未证明输入。

亦直接复核 SimplexNodalLp、SimplexReferenceInverse、AffineSimplex、AffineSimplexNorm、DerivativeFiberNorm 的所用证明。simplexNodalLp 是真实凸包限制 Lebesgue 测度上的实际仿射多项式类；系数反界依赖真实多项式连续性、单元内部非空以及 a.e. 相等提升后恢复顶点系数。实际梯度来自每点 HasFDerivAt，derivativeOneFiber 对全部坐标正交基逐一求值，其 Euclidean fiber 范数平方含每个坐标恰一次。没有将 CLM 算子范数、任意抽象能量或单方向导数冒充全梯度。梯度的线性变换次序是 Dp_ref∘A⁻¹，符合真实链式法则。

第 6 项先对固定 referenceSimplex n 取得 C，随后才引入任意 U；通过第 4 项的实际 simplex 等式重写依赖的所有对象。因此新常数仅允许依赖 n 和先置 κ，不再依赖任意参考 T、U、a、r、h 或节点 c。固定参考选择虽不指定标准顶点，其参考半径和参考逆界均已成为 n 的函数，量词结论仍准确。

## 加权比较和局部归一化的精确消去

权 w 是真实单元测度上的 BoundedMultiplier，包含实际函数、a.e. 强可测性及有限 a.e. 绝对值上界。WeightedL2 的 map 以已证 MemLp.toLp 构造真实乘法类，其代表身份只在 a.e. 意义下使用；seminorm 等于此乘法类的实际 L² 范数。MultiplierAlgebra.one 给真实常值 1 乘子及其范数等式。

第 7 项在 n、κ>0、W>0 之后，立即取无权 R(n,κ)>0 并选 C=W²R，之后才引入 U,a,r,h,w,s,c。显式输入为 s>0 与单元 a.e. 比较 |w|≤Ws、s≤W|w|。它先用真实乘子比较定理取得

`‖w∇p‖ ≤ Ws‖∇p‖`，`‖p‖ ≤ (W/s)‖wp‖`。

第二步除以 s 的方向由 s>0 保证；再插入 ‖∇p‖≤(R/h)‖p‖，正因子允许传递不等式，最终 `Ws·(R/h)·(W/s)=W²R/h`。s 可随单元和权变化，但在最终 C 中完全消失。代码没有用 w.bound 选择统一常数，也未除以 p、其范数或梯度范数；零系数和常数多项式均包含。

所需比较用绝对值，因此局部辅助定理还允许符号变化的非退化实权；这不会自动扩大原允许权族，应用原文时仍须从该族实际构造 w 并证明上述比较。两个平方积分身份本身不要求比较或 s>0，也适用于可消失的有界乘子；最终逆界则保留下界，未遗漏非退化条件。W>0 而非 W≥1 不构成漏洞：任何实际满足双边比较的数据才是最终定理的输入，证明不使用额外 W≥1。

## 任意仿射多项式、a.e. 类与积分形式

第 8 项输入真实 AffineMap p 和实际 L² 类 u、g，并明确假设 u a.e. 等于 p，g a.e. 等于 derivativeOneFiber(fderiv p)。取 cᵢ=p(Uᵢ) 是在真实连续仿射多项式上取节点值；全空间仿射再现给 simplexNodalInterpolant U c=p。两个已证 toLp a.e. 身份与输入身份经 Lp.ext 分别识别 u 与节点多项式类、g 与其真实梯度类。没有对任意 Lp 所选代表或 Sobolev 等价类直接读取节点。

这里 g 的局部梯度身份是公开前提，不能误读为已经证明任意全局 V_h 弱梯度限制的身份；后者正是保留的后续义务。其余输入也没有包含目标逆估计或某种可任取的能量等式。

第 9–10 项从实际 `seminorm_sq_integral` 和各自 a.e. 代表公式导出真实受限 Lebesgue 积分。底层 BoundedMultiplier.memLp_smul 与 integrable_density 保证这些平方密度实际可积；没有依赖不可积 Bochner 积分的默认值。第 11 项再次对任意真实 p 选择其实际节点系数，用两侧非负性合法平方第 7 项，mul_pow 给准确 (C/h)²，再代入第 9–10 项及全空间多项式再现。无遗漏平方、单元体积或坐标项。

## 尚未清偿的原文义务

尚需证明任意完整 V_h 状态的全局弱梯度在单元 a.e. 等于局部仿射导数，使用真实 a.e. 分区完成全网格求和，提供原形状正则网格与 h_K/ℓ_K 的具体尺度输入，并从原 allowed 权及 hq≤δ_num 统一推出单元比较 W。H² 点值代表、局部 h/h² 插值误差、加权投影稳定、超逼近、椭圆正则性和连续热 CE 等亦未因本批完成。C063 必须保留 AUXILIARY，原文覆盖保持 12/26。

## 固定依赖、构建和公理证据

两新模块的 Carleman 导入闭包共 47 模块，其中 45 个旧模块相对 base 逐字节未变，固定 Carleman.lean 显式导入两新模块。11 项与固定 state 的 C063/T047 清单及交付 JSON 逐项一致。已读取 [T045 参考局部逆界验收](T045-local-acceptance.md) 和 [T046 真实仿射尺度验收](T046-local-acceptance.md)，并直接检查本次关键调用及证明，没有仅继承旧 PASS 标签。

原稿、治理协议、Lean/mathlib pin、两工作流与 base 未变。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本机实际 mathlib HEAD 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，工作树干净；已读取所用 AffineBasis.basisOf、Module.Basis.equiv 与有限维 AffineBasis 存在定理的固定源码。Lean pin 为 4.35.0。

固定审计脚本对 11 项执行 `#check @...` 和 `#print axioms ...`；末尾枚举 privateToUserName 归属 Carleman 的全部公开/私有声明，递归 collectAxioms，仅允许 propext、Classical.choice、Quot.sound。实际 11/11 展开类型已逐项读取，均无隐藏目标逆界、额外参考表示或正维前提；公理集合均恰为这三项正常基础公理。

固定 `/tmp/carleman-weighted-simplex-local-axioms.txt` 实际为 1,302,668 bytes，SHA256 `7087394d06358bea67b90c32d38167f6aa64a89e8804d0dddcd376eed9fe6c5e`，末行 `Axiom audit passed for all 4671 Carleman declarations.`。实际 `/tmp/carleman-weighted-simplex-full.log` 含 `Build completed successfully (3585 jobs).` 和同一全局公理审计 PASS；没有 sorryAx 或未批准数学公理。

已独立通过 GitHub connector 核实同 SHA 的 [main CI 39159308167 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39159308167/attempts/1)：main/push，head_sha 为 `ce719d2683c7509827e457ea2e15e0ce5451b487`，run completed/success；`lean`（117769049157）、`state-check`（117769048976）、`dashboard / snapshot`（117769619275）三个 jobs 均 completed/success。Lean pin、证明目标构建、checked-source 记录及两份证据上传步骤全部成功。

同次 `lean-ci-result` artifact（12148496073）和 `lean-declaration-evidence` artifact（12147734530）的元数据均绑定该 run 与固定 SHA。独立读取实际 `/tmp/carleman-weighted-simplex-main-ci/result.json`：status PASS，checked_sha=source_head_sha=`ce719d2683c7509827e457ea2e15e0ce5451b487`，CI URL 与上述 attempt 1 一致，finished_at=`2026-10-18T19:35:01.827299+00:00`，target 为 Carleman，Lean 4.35.0（提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）和 mathlib pin 与固定源码一致。

实际 `/tmp/carleman-weighted-simplex-main-axioms/axioms.txt` 已独立与固定本机文件逐字节比较，完全相同：1,302,668 bytes，SHA256 `7087394d06358bea67b90c32d38167f6aa64a89e8804d0dddcd376eed9fe6c5e`。另逐名核对其中全部 11 项实际展开类型及递归公理列表，恰为上述三项标准基础公理；末行确认全部 4671 Carleman 声明审计 PASS。未混用后续工作区代码或其他运行的产物。

## 验收决定

**C063：PASS，可升级为 REVIEWED，scope 保持 AUXILIARY。** 11 项未发现需修复的数学、实际类型、代表、导数、权归一化、量词或统一性缺陷；固定版本语义、展开类型、递归公理和同 SHA 三项 CI 均已独立核实。仅接受本报告界定的任意单纯形统一局部加权逆估计，保留全部全局组装及原允许权比较义务；原文完成保持 12/26。

本次仅写本报告，未修改数学源码、台账、root 导入、原稿或覆盖表，未 commit/push。
