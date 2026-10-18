# T045 / C061 独立本机验收

- `checked_sha`: `6cbca2eb3813801b491d54b7f442834ded59d83c`
- `base_commit`: `50ea3111057c5d7b796cca799c10a9a900d14caf`
- `reviewed_at`: `2026-10-18T19:22:55+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：真实固定非退化单纯形的节点多项式 L² 类、系数可辨识性及反界、实际全坐标梯度和固定单元逆估计。**常数可依赖固定 T；不包含仿射缩放、形状正则族统一性或原加权逆估计。原文完成仍为 12/26。**

本次从固定提交导出源码，独立读取两模块全部证明、15 项完整展开类型和相关实际依赖，对照原 `paper/main.tex` Section 6 的 P1 局部逆估计及 `eq:p1-weighted-inverse`。规格和构建记录没有代替数学验收；工作区后续 AffineChangeVolume 等草稿不属于本报告。

## 全部 15 项声明

完整名称均以前缀 `Carleman.` 开始。位置属于固定提交的 `Carleman/Spatial/`，声明顺序与 C061、T045 及交付 JSON 一致。

| # | 声明（省略 Carleman.） | 位置 | 独立数学核对 |
|---|---|---|---|
| 1 | `simplexCell_finiteMeasure` | `SimplexNodalLp.lean:15` | PASS；实际有限顶点凸包的紧性证明受限 Lebesgue 测度有限。 |
| 2 | `simplexCell_subset_closure_interior` | `SimplexNodalLp.lean:18` | PASS；真实非退化 d-simplex 内部非空，凸性给整个单元包含于内部闭包。 |
| 3 | `simplexNodalInterpolant_memLp` | `SimplexNodalLp.lean:24` | PASS；真实连续仿射多项式可测，重心坐标界给单元内绝对值≤系数的有限乘积范数。 |
| 4 | `simplexNodalLp` | `SimplexNodalLp.lean:30` | PASS；以已证 MemLp.toLp 构造实际节点多项式的受限 L² 类。 |
| 5 | `simplexNodalLp_ae` | `SimplexNodalLp.lean:33` | PASS；所选 L² 代表与真实仿射多项式在单元受限测度下 a.e. 相等。 |
| 6 | `simplexNodalLpLinear` | `SimplexNodalLp.lean:37` | PASS；由多项式有限和及 Lp.ext、a.e. 运算公式证明系数到 L² 类的实际线性性。 |
| 7 | `simplexNodalLp_injective` | `SimplexNodalLp.lean:53` | PASS；连续多项式的 a.e. 相等经开集正性和内部稠密性提升至整个单元，再用实际顶点值恢复全部系数。 |
| 8 | `simplexNodalLp_coefficient_bound` | `SimplexNodalLp.lean:65` | PASS；真实单射有限维线性映射的反 Lipschitz 界给 B(T)>0，先于任意系数 c。 |
| 9 | `simplexBarycentricDerivative` | `SimplexReferenceInverse.lean:15` | PASS；每个真实连续重心仿射坐标的 contLinear，不是任意导数输入。 |
| 10 | `simplexNodalDerivativeLinear` | `SimplexReferenceInverse.lean:19` | PASS；系数对这些实际 CLM 导数的有限线性组合，线性性内部证明。 |
| 11 | `simplexNodalInterpolant_hasFDerivAt` | `SimplexReferenceInverse.lean:26` | PASS；仿射求导与常数倍／有限和法则证明每一点的真实 Fréchet 导数。 |
| 12 | `simplexNodalGradientLp` | `SimplexReferenceInverse.lean:37` | PASS；真实一阶 Euclidean fiber 常值场在单元上的 L² 类，有限测度由第 1 项供应。 |
| 13 | `simplexNodalGradientLp_ae` | `SimplexReferenceInverse.lean:43` | PASS；该场 a.e. 精确等于实际 fderiv 的全部一阶坐标 fiber。 |
| 14 | `simplexNodalGradientLinear` | `SimplexReferenceInverse.lean:51` | PASS；实际梯度 L² 类随全部节点系数线性变化，商空间运算通过 a.e. 身份证明。 |
| 15 | `simplex_reference_inverse` | `SimplexReferenceInverse.lean:71` | PASS；内部选择 C(T)=‖G(T)‖B(T)+1>0，先于全部 c，得到实际全梯度 L² 对实际多项式 L² 的界。 |

## 真实单元、L² 类及合法的节点恢复

T 的类型为 `Affine.Simplex ℝ (SpatialCoordinates d) d`，其 d+1 个实际顶点仿射独立；既有 simplexAffineBasis 用实际全维仿射张成构造 AffineBasis。simplicialCell 是这些顶点的真实凸包，不是一个给定质量矩阵或人为赋予范数的系数空间。有限顶点凸包紧性使其 Lebesgue 体积有限；非退化全维性经真实 affineSpan_eq_top 给非空内部。凸集非空内部的闭包等于整个集的闭包，因而每个单元点，包括所有顶点，都在内部闭包中。

节点多项式 `p_c=Σ c_i λ_i` 使用实际重心仿射坐标。它全空间连续；在单元内 λ_i≥0 且 Σλ_i=1，所以 `|p_c|≤max_i|c_i|=‖c‖`，其中系数空间使用 Lean 有限函数空间的最大值范数。有限受限测度与真实 a.e. 上界给 MemLp，随后 toLp 给实际 L² 类。线性性逐项利用这个多项式公式和 Lp 的 a.e. 加法／数乘公式，不对 L² 所选代表声称逐点运算恒等。

单射性是关键：从两个 L² 类相等，先通过各自的 toLp a.e. 身份得到两个实际连续多项式在 `volume.restrict cell` 下 a.e. 相等。调用的 `Measure.eqOn_of_ae_eq` 使用的是**环境 volume 的开集正性**，不是错误地要求受限测度对环境所有开集均为正。该 mathlib 定理先在单元内部利用连续性和开集正性得到逐点相等，再由单元包含于内部闭包及两函数在单元上的连续性，扩张到整个单元。

此后才在实际顶点处对这两个连续仿射多项式求值；顶点属于真实凸包，已有精确节点公式 `p_c(T.points i)=c_i` 给 c_i=e_i。没有在任意 L² 代表上取顶点值，也没有把边界顶点处的 a.e. 信息直接当成逐点信息。非退化条件不是可省略的装饰：它在内部非空和稠密步骤实际使用，排除了低维零体积单元上的伪单射。

已有 `simplexNodalInterpolant_reproduces` 对任意真实 AffineMap p，取系数 `c_i=p(T.points i)` 后在全空间精确再现 p。因此任意系数的最终结论覆盖所有仿射多项式，没有隐藏的边界节点零、均值零或谱截断限制。

## 系数反界、实际全部梯度和常数次序

simplexNodalLpLinear 的定义是刚构造的真实 L² 映射。其定义域 `Fin(d+1)→ℝ` 有限维，单射性已内部证明。固定 mathlib 的 injective_iff_antilipschitz 由该线性映射到其 range 的连续线性等价及逆映射范数推出反 Lipschitz 常数；不是把目标 L² 系数界设为输入。通过 f(0)=0 的反 Lipschitz 范数形式得到 `‖c‖≤B(T)‖p_c‖L²`，存在的正常数在 c 之前，但可以依赖 T 和维数。

每个 simplexBarycentricDerivative 是真实重心 AffineMap 的连续线性部分。每个重心函数在任意环境点的 HasFDerivAt 都由实际连续仿射映射的导数定理给出；对 c_i 倍及有限和使用求导规则，再以节点插值的真实求和公式识别原函数，得到常值实际导数 `A_c=Σc_i Dλ_i`。没有只声明“形式导数”，也没有漏掉常数项：常数函数的线性部分自然为零。

simplexNodalGradientLp 是实际 `derivativeOneFiber A_c` 的常值 L² 类。已直接检查 derivativeOneFiber：它对每个 `Sym (Fin d) 1` 指标，通过单元素 Sym 等价恰取一个正交坐标向量上的 CLM 求值。该 fiber 是实际 EuclideanSpace，故范数平方是全部 d 个坐标方向导数的平方和，每个方向出现一次；不是 CLM 算子范数、单一方向或一个任意能量替身。借助刚证明的每点 HasFDerivAt，a.e. 身份把这个 L² 场精确识别为原 p_c 的真实 fderiv 的一阶 fiber。这里是单元上的梯度限制，没有声称多项式的单元外零延拓具有同一个全空间弱导数。

该真实梯度 L² 映射 G 对系数线性；有限维定义域给其连续线性映射和有限算子范数。证明先固定 T，选择上述 B(T)，定义 G(T)，再选择 `C(T)=‖G(T)‖B(T)+1`，最后引入任意 c。实际计算为 `‖∇p_c‖=‖G c‖≤‖G‖‖c‖≤‖G‖B‖p_c‖≤C‖p_c‖`。正性由 +1 保证，不除以 ‖G‖、梯度范数或 c；零系数、常数多项式和 d=0 的零梯度情况均合法。没有遗漏 c 对常数选择的量词依赖。

## 原文对应与范围边界

原 Section 6 Step 2 的 `eq:p1-weighted-inverse` 要求对完整 V_h 中的 z_h 有 `‖σ∇z_h‖L²(Ω)≤C‖ℓ⁻¹σz_h‖L²(Ω)`，其常数须结合形状正则、局部尺度与权比较统一。本批证明的是对每个固定非退化单纯形 T 存在 C(T)，对所有仿射 p 的不加权局部逆估计。该参考单元步骤正确且实质完成，但 C(T) 允许随单元大小、退化程度和维数变化。

尚未在本批证明真实可逆仿射变换下的体积换元、导数变换和 L² 尺度，尚未把 C(T) 转为形状正则族的统一 `C h_K⁻¹`，也未完成权比较、单元求和及原完整状态上的加权逆界。没有从此局部有限维范数等价推断网格统一性。H² 点值代表、局部插值误差、椭圆正则性、加权投影及连续热 CE 等后续义务亦未因此清偿。

C061 的 scope 必须保留 AUXILIARY，不能据此提升 P011 或其他具名原文结果；原文仍 12/26。`extra_hypotheses=[]` 只能针对这项真实固定单纯形辅助目标理解，不能用来扩大为已实现原统一加权逆估计。

## 固定依赖、构建及公理

导入闭包包含 33 个 Carleman 模块，其中 31 个既有模块与基线逐字节相同，新增恰为本次两模块；固定 Carleman.lean 显式导入两者。直接复核了实际单纯形、重心插值、仿射再现、内部非空及一阶 fiber 构造。原稿、治理协议、工具链和 CI 工作流与基线一致，MATH_SPEC 增加本阶段说明；原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

本机 mathlib HEAD 实际为固定 `56a005855ea17e0b0958f73ec801ae140b0a1679`，工作树干净。已读取该版本 OpenPos 的实际 a.e.→EqOn 证明、凸集内部闭包定理及有限维单射反 Lipschitz 定理；调用的测度、连续性、稠密性和有限维条件均得到满足。Lean pin 为 4.35.0。

固定 CheckAxioms 对本次 15 项逐名执行 `#check @...` 和 `#print axioms ...`，再遍历以 privateToUserName 识别的所有 Carleman 声明，递归 collectAxioms 并仅允许 `propext`、`Classical.choice`、`Quot.sound`。已逐名核对固定本地 15/15 展开类型，各项公理集合恰为这三项正常基础公理；C061/T045 及交付 JSON 的完整清单顺序一致。

固定 `/tmp/carleman-reference-inverse-full.log` 实际包含 `Build completed successfully (3577 jobs).` 和 `Axiom audit passed for all 4620 Carleman declarations.`。固定本地 `/tmp/carleman-reference-inverse-local-axioms.txt` 实际为 **1,282,412 bytes**，SHA256 **`e198f2b30bd49906d02fa5105e16555c880e0e2624b0ed61a689dad26593f98a`**。

已独立通过 GitHub connector 核实 [main CI 39158171521 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39158171521/attempts/1)：main/push、head SHA 为固定 `6cbca2eb3813801b491d54b7f442834ded59d83c`，completed/success。lean（117765635673）、state-check（117765635829）、dashboard / snapshot（117766284970）三项 jobs 均 success；Lean pin、root 构建、checked source 记录及两份证据上传步骤全部成功。同 run 的 lean-ci-result artifact（12147453478）和 lean-declaration-evidence artifact（12147652862）均绑定该固定 SHA。

已实际读取 `/tmp/carleman-reference-inverse-main-ci/result.json`：status PASS，`checked_sha=source_head_sha=6cbca2eb3813801b491d54b7f442834ded59d83c`，targets 为 Carleman，`finished_at=2026-10-18T19:20:20.239225+00:00`，ci_url 与上述 run/attempt 完全一致。Lean 4.35.0 提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` 与 mathlib pin 正确。

原始远端 `/tmp/carleman-reference-inverse-main-axioms/axioms.txt` 与固定本地副本已逐字节比较，完全相同：**1,282,412 bytes**，SHA256 **`e198f2b30bd49906d02fa5105e16555c880e0e2624b0ed61a689dad26593f98a`**。另逐名核对远端 15/15 完整类型和正常基础公理集合，末行实际为 **`Axiom audit passed for all 4620 Carleman declarations.`**。无 sorryAx 或未批准数学公理，未混用后续源码或产物。

## 验收决定

**C061：PASS，可升级为 REVIEWED，scope 保持 AUXILIARY。** 固定版本 15 项未发现需要修复的陈述、AE／节点身份、梯度、可积性或量词缺陷；完整展开类型、递归公理及同 SHA 正式 main CI 均已独立核实。范围仅为固定单纯形参考逆估计，仿射尺度、形状正则族统一性及原加权逆估计仍待，原文计数保持 12/26。

本次仅写本报告，没有修改数学源码、台账、覆盖表、原稿或 root 导入，没有 commit/push。
