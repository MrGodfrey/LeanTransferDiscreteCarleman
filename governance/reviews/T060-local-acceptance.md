# T060 / C076 独立本机验收

- `checked_sha`: `021696bbeb403adab3172f24294db01af5a2ab4e`
- `base_commit`: `daf0c9e455f04bf5d7eff4e4ecde1729e01f6a92`
- `semantic_checked_at`: `2026-10-18T21:11:18+00:00`
- `reviewed_at`: `2026-10-18T21:14:45+00:00`
- `result`: **PASS**。
- `axiom_check`: **PASS**。
- 范围：**AUXILIARY**。真实闭单元内在导数的一阶 Taylor 与节点误差，及真实标量权乘仿射函数的导数字段和节点误差。尚未实例化允许权 σ²、把仿射函数上界 P 转成单元 L² 量，或完成原全域加权超逼近；完整原文覆盖保持 12/26。

本报告直接读取固定提交的两模块、全部 13 项完整类型和证明、实际依赖及原 `paper/main.tex`，对照 `governance/analysis/T060-within-affine-product.md`。执行者说明、旧验收报告和 CI 成功不替代数学语义核查。后续工作树中的 Squared* 模块不在本次范围内。

## 全部 13 项声明

名称均加前缀 `Carleman.`；源码位置相对于固定提交的 `Carleman/Spatial/`。

| # | 声明 | 源码位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `affineJetPolynomial` | `SimplexWithinInterpolation.lean:13` | PASS；真实仿射映射，常数部分 v−A(a)，线性部分真实 CLM A。 |
| 2 | `affineJetPolynomial_apply` | `SimplexWithinInterpolation.lean:17` | PASS；精确值 v+A(x−a)，锚点和符号正确。 |
| 3 | `affineJetPolynomial_derivative` | `SimplexWithinInterpolation.lean:23` | PASS；从真实 HasFDerivAt 及唯一性识别 affineScalarDerivative=A。 |
| 4 | `withinFirstOrder_remainder` | `SimplexWithinInterpolation.lean:31` | PASS；实际凸集上、每点与 f 相连的域内导数 F 给 Lh² 值余项及 Lh 导数字段余项。 |
| 5 | `simplexNodal_within_value_error` | `SimplexWithinInterpolation.lean:55` | PASS；实际闭单元所有节点的 f 值构成插值，误差 2Lh²。 |
| 6 | `simplexNodal_within_gradient_error` | `SimplexWithinInterpolation.lean:71` | PASS；实际内球及 h≤κr 给字段到节点插值真实 CLM 导数的误差 (1+4κ)Lh。 |
| 7 | `affineProductDerivative` | `AffineProductDerivative.lean:13` | PASS；字段准确为 w(x)Dp+p(x)W(x)。 |
| 8 | `affineProduct_hasFDerivWithinAt` | `AffineProductDerivative.lean:18` | PASS；由真实乘积法则把该字段连接到实际函数 w·p。 |
| 9 | `affineProductDerivative_lipschitzOn` | `AffineProductDerivative.lean:26` | PASS；常数 P L₂+2‖Dp‖L₁，两个交叉项均保留。 |
| 10 | `affineProduct_nodal_value_error` | `AffineProductDerivative.lean:61` | PASS；真实节点值 w(vᵢ)p(vᵢ)，值误差 2(P L₂+2‖Dp‖L₁)h²。 |
| 11 | `affineProduct_nodal_gradient_error` | `AffineProductDerivative.lean:79` | PASS；真实乘积导数字段到插值 CLM 导数的误差 (1+4κ)(P L₂+2‖Dp‖L₁)h。 |
| 12 | `affineProduct_derivative_interior` | `AffineProductDerivative.lean:99` | PASS；仅在 K 内部把域内字段识别为 w·p 的实际 fderiv，未声称边界外可微。 |
| 13 | `derivativeField_lipschitzOn_of_within_bound` | `AffineProductDerivative.lean:106` | PASS；实际 HasFDerivWithinAt W(Hx) 和 ‖Hx‖≤L，经凸集均值定理供应 W 的 L-Lipschitz 界。 |

## 原文对应和未清偿项

原 `paper/main.tex:1523–1598` 的 P1 论证包含一般 H² 函数的节点插值估计 `eq:p1-interpolation`，以及 Step 3 对 σ²z_h 的超逼近。后者使用真实仿射 z_h 的二阶导数为零，以及 σ² 的一、二阶导数界，得到 q|∇z_h| 和 q²|z_h| 两类项，再进入单元 L² 与全域求和。这里的函数名 w 是将来拟取 σ² 的标量权，不是原文中记作 w 的插值误差。

本批证明上述路线中的闭单元经典微分和乘积节点误差步骤。原允许 profile 只在闭域上给定光滑性，因此保留每一点的 HasFDerivWithinAt，比要求边界外可微更适合后续实例。尚未提供 σ² 的实际字段 W/H 及统一 L₁/L₂ 界、P 的真实单元 L² 控制、单元内部导数到实际弱梯度的 a.e. 识别及全域加权求和。一般弱 H² 函数的连续代表和原 H² 插值误差也没有由这些较强经典微分假设自动得到。不能将本批登记为完整 `eq:p1-interpolation`、原超逼近或 `prop:p1` 的完成。

## 闭单元、实际导数字段与 Taylor 余项

`withinFirstOrder_remainder` 量化任意真实凸集 K、函数 f 和 CLM 字段 F，并明确要求每个 x∈K 都有 `HasFDerivWithinAt f (F x) K x`。Lipschitz 假设作用于同一字段 F；没有以自由场、假定余项或目标误差替代真实微分关系。锚点 a 属于 K，h≥0，所有 x∈K 满足 dist(x,a)≤h。

实际仿射多项式 p(x)=f(a)+F(a)(x−a) 的导数经唯一性证明等于 F(a)。Lipschitz 界先给 ‖F(y)−F(a)‖≤Lh，再使用固定 mathlib 的 `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'` 得 |f(x)−f(a)−F(a)(x−a)|≤Lh‖x−a‖≤Lh²。已查看该均值定理的实际声明及线段证明：其前提就是凸集内逐点的真实域内导数和界，不要求全空间可微、开集、UniqueDiff 或外部延拓。导数字段余项 Lh 直接来自同一 Lipschitz 界。

真实单纯形 `Affine.Simplex ℝ (SpatialCoordinates d) d` 有 d+1 个实际仿射独立顶点，`simplicialCell` 是其真实闭凸包。锚点选实际顶点 0；所有节点都属于闭单元，故余项适用于边界节点。已有真实重心坐标插值的非负性、和为一及仿射再现给插值余项≤Lh²，和函数余项相加得 2Lh²。没有把仅内部 a.e. 的函数值拿到节点上使用。

梯度估计对 I−p 使用真实仿射再现和节点余项，得到在真实内球 B(a,r) 上 |I−p|≤Lh²。已核对依赖 `affineScalarDerivative_inball_bound`：比较 a 与 a+(r/2)e 的实际仿射值，给 ‖D(I−p)‖≤4Lh²/r。真实导数唯一性给 D(I−p)=DI−Dp。用 r>0 和 h≤κr 得 4Lh²/r≤4κLh，再加 ‖F(x)−Dp‖≤Lh，准确得到 (1+4κ)Lh。

这里所有数值因子都是显式常数；没有隐藏对单元、函数或网格的选择。h 可以为 0，证明只除以正 r，不除以 h。κ 虽未另列非负假设，但由 h≥0、r>0、h≤κr 已蕴含 κ≥0。维数 d=0 也被覆盖：顶点 0 仍存在，CLM 为零空间；内球导数界依赖的单位向量论证采用通用 opNorm 判据，没有偷偷要求正维或构造不存在的单位向量。梯度结论在闭单元边界比较的是合法域内字段 F，不是未经证明存在的边界 fderiv。

## 乘积导数、常数和内部身份

令 Dp 为真实仿射函数 p 的恒定 CLM 导数。`affineProduct_hasFDerivWithinAt` 使用 `hw.mul` 和 p 的真实全空间导数，确立 G(x)=w(x)Dp+p(x)W(x) 是 w·p 的域内导数。参数和乘法次序正确。

在同一凸集上假设 |p|≤P、‖W‖≤L₁、W 为 L₂-Lipschitz，且 W 每一点确为 w 的域内导数。真实凸集均值定理内部给 w 的 L₁-Lipschitz 界，p 的真实仿射导数给 |p(x)−p(y)|≤‖Dp‖dist(x,y)。证明精确分解

`G(x)−G(y)=(w(x)−w(y))Dp+p(x)(W(x)−W(y))+(p(x)−p(y))W(y)`。

三项分别贡献 L₁‖Dp‖、P L₂、‖Dp‖L₁，因此总常数是 P L₂+2‖Dp‖L₁。没有遗漏任何交叉项；Dp 恒定，所以不需要额外的 |w| 绝对值界。NNReal 常数到实际实数范数的转换准确，P/L₁/L₂ 为零的情形没有被排除。

两个乘积节点估计直接把真实 w·p、实际字段 G 和刚证明的 Lipschitz 常数送入闭单元估计，插值节点确为 w(vᵢ)p(vᵢ)。梯度范数是实际 CLM 算子范数，报告不把它擅自登记成已完成的弱 H¹/L² 估计。内部身份定理保留 x∈interior K，并由 K 是 x 的邻域把域内导数转为真实 HasFDerivAt，再取 fderiv；没有在边界强加外部导数。

最后的二阶字段定理要求实际 `HasFDerivWithinAt W (H x) K x`，而非给任意命名为 Hessian 的字段加界。一般 Banach 值凸集均值定理从 ‖H‖≤L 供应 W 的 Lipschitz 性；与先前 hw 合用时才得到某个标量 w 的真实二阶信息。该辅助定理自身不声称任意 W 都来自某个标量势函数。

## 固定版本、依赖和本机公理证据

两新模块的 Carleman 导入闭包共 76 个模块，其中 74 个既有模块相对 base 逐字节不变；root 明确导入两新模块。实际检查了 `SimplexNodalInterpolation`、`SimplexNodalRemainder`、`SimplexTaylorInterpolation`、`AffineWeakGradient` 及 mathlib 凸集域内均值定理。新证明没有借用旧全空间可微条件来扩大结论，也没有新增目标估计公理。

AGENTS、流程规则、原论文、Lean/mathlib pin 和 CI 流程在该差异中未改。原论文 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。`tools/CheckAxioms.lean` 仅增加这 13 项实际完整类型和递归公理的显式打印；最终遍历所有 Carleman 声明的审计代码不变，递归 `collectAxioms` 只允许 `propext`、`Classical.choice`、`Quot.sound`。

固定 `/tmp/carleman-within-product-full.log` 实际包含 `Build completed successfully (3634 jobs).`。固定 `/tmp/carleman-within-product-local-axioms.txt` 的全部 13 项完整类型与源码一致，13 项递归公理检查均通过。产物中 1368 项不同显式打印声明的公理集合扫描也全部属于上述基础白名单，末行确认全部 4929 个 Carleman 声明（包括内部生成声明）的递归审计通过，无 sorry 或额外数学公理。

本机固定产物为 1,413,416 bytes，SHA256 `08b05b6606591db84448cf81c8509587b11911a85085bc583f277dea34618356`。工具链为 Lean 4.35.0，mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`。

## 远端证据和最终签发

已独立读取真实 [main/push run 39166449091](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39166449091/attempts/1)，attempt 1，head SHA 精确匹配 checked SHA，顶层 completed/success。三项 jobs 均 completed/success：lean `117790278816`、state-check `117790278961`、dashboard / snapshot `117790846574`。

已独立读取同次 artifact 元数据：`lean-ci-result` id `12150877220` 和 `lean-declaration-evidence` id `12150553410` 均绑定该 run、main 和同一 head SHA。实际读取 `/tmp/carleman-within-product-main-ci/result.json`，status=PASS，checked_sha/source_head_sha 均为 `021696bbeb403adab3172f24294db01af5a2ab4e`，ci_url 精确对应该 run/attempt，finished_at=`2026-10-18T21:09:25.529415+00:00`，target 为 `Carleman`。Lean 4.35.0（commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）及 mathlib pin 均匹配。

实际读取 `/tmp/carleman-within-product-main-axioms/axioms.txt`，与固定本机产物逐字节完全相同，1,413,416 bytes，SHA256 `08b05b6606591db84448cf81c8509587b11911a85085bc583f277dea34618356`。远端产物中再次核对全部 13 项实际完整类型和递归公理集合，并扫描全部 1368 项不同显式打印的公理集合，均只有正常基础公理。末行确认全部 4929 项递归审计通过。

最终结论：**T060 / C076 PASS，可以将 C076 升为 REVIEWED，保留 AUXILIARY。** 13 项及所声称范围通过，未发现数学缺陷。σ² 实例、P→单元 L²、原全域加权超逼近和一般 H² 插值义务仍待，不提升完整原文覆盖，完成计数保持 12/26。本 Agent 仅写本报告，未修改证明、台账、root 导入或原稿，未 commit/push。
