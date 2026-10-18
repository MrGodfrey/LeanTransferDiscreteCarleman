# T061 / C077 独立本机验收

- checked_sha: `05aadb86ef406e8e1f843a74ddace902041d79e9`
- base_commit: `021696bbeb403adab3172f24294db01af5a2ab4e`
- reviewer: 独立本机数学验收 Agent `/root/accept_spatial_lemma`
- result: `PASS`
- axiom_check: `PASS`
- reviewed_at: `2026-10-18T21:21:20+00:00`
- scope: `AUXILIARY`。原实际允许权平方的域内一、二阶导数、单元统一比较及乘仿射状态的点态节点误差。原文完成数保持 **12/26**，不标为原完整加权超逼近或一般 H² 插值结论。

## 版本、范围与方法

依仓库 `AGENTS.md`、`governance/PROJECT_OPERATIONS.md`、`state/README.md`，直接读取固定提交的三模块全部证明、10 项完整展开类型和递归公理输出，以及原 `paper/main.tex` 的允许权定义、`eq:allowed-weight-derivatives` 与 Section 6 Step 3。对照 `governance/analysis/T061-squared-weight-errors.md`，但未以规格、自检或 CI 成功代替语义检查；后续工作树文件不参与此次验收。

三个模块均在 `Carleman/Weights/`：`SquaredWithinDerivatives.lean`（6 项）、`SquaredCellDerivatives.lean`（3 项）、`SquaredNodalError.lean`（1 项）。10 项逐名对应固定 C077 的 `lean_declarations`、`/tmp/carleman-squared-weights-declarations.json` 和实际声明；固定 `Carleman.lean` 导入全部三模块。递归项目 import 闭包共 81 模块，其中 78 个既有模块相对基线逐字节不变。

原论文 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean 固定 `leanprover/lean4:v4.35.0`；mathlib 固定 `56a005855ea17e0b0958f73ec801ae140b0a1679`，已核实实际 mathlib HEAD 相同且工作树干净。治理协议、CI 工作流、构建与结果记录脚本相对基线未改。

## 全部 10 项声明

下表给完整名称。每项数学语义及本机递归公理核查均 PASS，实际前提及范围如下。

| 声明 | 实际类型和证明核对 |
| --- | --- |
| `Carleman.allowedSquaredWeight` | 定义正是 `(q^τ exp(qηρ(x)))²`；没有另选一个只满足形式上界的权。 |
| `Carleman.allowedSquaredWeight_eq` | 在 q>0 下，函数级恒等于 `q^(2τ) exp(qη(2ρ(x)))`。真实 `rpow_add`、`exp_add` 和代数恒等式给出两个因子的准确倍数。 |
| `Carleman.allowedSquaredWeight_contDiffOn` | 固定域内 ρ 为 C²，则该实际平方权亦 C²。通过真实常数乘、指数复合及平方构造；此光滑性项自身不需 q 正值。 |
| `Carleman.allowedSquaredWeight_hasFDerivWithinAt` | 逐点证明实际 `fderivWithin` 是该平方权的域内 Fréchet 导数，来自实际 C² 函数的一阶可微性。 |
| `Carleman.allowedSquaredWeight_secondWithin` | C² 加 `UniqueDiffOn` 给同一一阶 `fderivWithin` 场的真实域内导数，候选恰为再次 `fderivWithin`。不是任意命名 Hessian 场。 |
| `Carleman.allowedSquaredWeight_within_derivatives_uniform` | 固定紧域、C² profile 和 UniqueDiff 后先选 C>0，再对所有 q≥1、实 τ、`|η|=1`、域点给 `‖Dσ²‖≤Cqσ²` 和 `‖D(Dσ²)‖≤Cq²σ²`。二阶 CLM 范数与实际二阶迭代导数范数的转换有真实等距身份依据。 |
| `Carleman.allowedSquaredWeight_cell_le` | q>0、D≥0、`hq≤1`、`|ρ(x)-ρ(a)|≤Dh` 给实际 `σ²(x)≤exp(2D)σ²(a)`。空间常数 q^(2τ) 不参与导数或比较损失，指数中的 2 保留。 |
| `Carleman.allowedSquaredWeight_local_derivative_data` | 开凸域、紧闭包及闭包上的 C² profile 内部供应 UniqueDiff 和 profile 的 Lipschitz 常数。统一 C 先于真实单纯形、q、τ、η、h；给锚点 0 归一化的一阶场界及该同一场的 `Cq²σ²(a)`-Lipschitz 性。 |
| `Carleman.allowedSquaredWeight_multiplier_value` | 任意实际 SpatialProfile、TimeWeight、τ、t、η、x 下，定义精确等于实际 `((ρ.scaled η).multiplier w τ t).value x` 的平方。未只证明 a.e. 或把时刻参数遗漏。 |
| `Carleman.allowedSquaredWeight_product_errors` | 实际闭单元上任意仿射 p 及公开点态界 `|p|≤P`，给真实节点值误差 `2Cσ²(a)(q²P+2q‖Dp‖)h²`；真实内球与形状关系再给域内导数字段误差 `(1+4κ)Cσ²(a)(q²P+2q‖Dp‖)h`。P 为 NNReal，两个乘积交叉项均保留，节点取真实函数值。 |

## 真实平方权及一、二阶域内导数

原论文在 `paper/main.tex:291–302` 固定光滑 profile，要求 `q(t)≥1`，允许 `q^τ exp(±qρ)`；Section 6 Step 3 实际操作的是其平方乘 P₁ 状态。当前定义就是该权的真实平方，`allowedSquaredWeight_multiplier_value` 对同一实际 SpatialProfile/TimeWeight 乘子逐点给出恒等式，故没有脱离原乘子接口。

对 q>0，实幂 `q^(τ+τ)=q^τq^τ` 与指数加法给平方等于 `q^(2τ) exp(qη(2ρ))`。后续导数证明只将**固定** profile 2ρ 和指数 2τ 代入已证的空间导数估计。该依赖本来对任意实指数成立，且常数只取决于固定 profile 的有限阶真实导数界。没有把 2ρ 或 2τ 宣称为新的原数值允许权，也没有调用要求固定原权族的 CE/转移结论；原 `|τ|≤τ_*` 是此空间辅助定理全实 τ 的合法子集。

一阶字段始终是 `fderivWithin ℝ σ² K`，二阶字段始终是 `fderivWithin ℝ (fderivWithin ℝ σ² K) K`。C² 函数的一阶可微性提供第一项 HasFDerivWithinAt；固定 mathlib 的 `ContDiffOn.fderivWithin` 在 UniqueDiffOn 下给一阶场 C¹，继而给第二项 HasFDerivWithinAt。无域外延拓、无另给的任意导数字段，也没有从不可微处的默认 fderiv 值推导结论。

统一界调用 `allowedWeight_spatial_derivatives_uniform`，该实际依赖通过紧集上固定 2ρ 的有限阶导数上界、真实指数复合导数和空间常数 q^(2τ) 的线性缩放得到。j=1、j=2 分别转换为所需实际 CLM 范数：已直接核查 mathlib 的 `norm_iteratedFDerivWithin_one` 与 `norm_iteratedFDerivWithin_fderivWithin`，在同一 K 的 UniqueDiffOn 和 x∈K 下是由 curry 线性等距给出的范数等式。二阶算子空间没有被错误替换成单一方向导数或未经证明相等的坐标范数。

`UniqueDiffOn (closure S)` 由真实开凸域内部供应：非空分支用凸集非空内部，空分支直接消去成员，不偷偷添加 S 非空前提。它针对闭域，故所有边界点的域内导数与后续节点值都在定理范围内。

## 单元比较、真实 Lipschitz 供应与量词

固定 profile 的 `smooth_profile_lipschitz` 从闭域 C¹、紧性、真实域内导数界和凸集均值定理供应 D≥1。对闭单元内 x 与实际顶点 a=T.points 0，完整两点距离条件给 `|ρ(x)-ρ(a)|≤Dh`。`|η|=1` 后乘正 q，结合 hq≤1，精确得到指数差 `2qη(ρ(x)-ρ(a))≤2D`；从而有 `σ²(x)≤exp(2D)σ²(a)`。证明不除以可能为零的权或 h，且没有忘记平方权带来的指数因子 2。

以该真实比较归一化一、二阶界，得到 `C₀ exp(2D) q σ²(a)` 与 `C₀ exp(2D) q² σ²(a)`。随后把二阶 HasFDerivWithinAt 从 closure S **限制到真实闭单元**，通过已有 `derivativeField_lipschitzOn_of_within_bound` 的凸集均值定理证明一阶场 W 的 Lipschitz 性。这里只需每点真实域内导数及界；不要求 W 在域外可微。已直接检查其 mathlib 均值定理的线段及端点前提，调用正确。

`Real.toNNReal` 仅把已经证明非负的 `Cqσ²(a)`、`Cq²σ²(a)` 包装为 Lipschitz 参数。所有使用处都以实际非负证明改写 `coe_toNNReal`，没有利用截断负数至零来改变估计。C>0、q≥1 和 σ²≥0 是这些符号证明的来源。

最终 C 选为 `C₀ exp(2D)`，在单元 T、q、τ、η、h、仿射 p、P、x、内球中心/r/κ 之前。它仅可依赖固定 d、域和 profile 的既定数据，没有网格、时刻、qmax、τ 或状态依赖。将 q 取实际 `TimeWeight.q t` 时，真实 `TimeWeight.lower` 在所有 t 给 q≥1；乘子身份适用于任意 t，因此同一 C 可用于全部时刻，无需逐时重选常数。hq≤1 仍是公开的小尺度条件，本阶段没有把它从任意网格自动推出或声称已完成网格上 qmax 条件的全域组装。

## 乘积导数、节点误差与边界情形

实际字段 `affineProductDerivative w W p(x)=w(x)Dp+p(x)W(x)` 由真实 HasFDerivWithinAt 乘积法则连接到 w·p，其中 w=σ²、W 是上述闭域真实一阶字段，经 mono 限制到单元。它不是只按这个名字定义后便称作导数：调用链内确有逐点域内微分身份证明。

直接复核 T060 的差值分解：

`G(x)-G(y)=(w(x)-w(y))Dp+p(x)(W(x)-W(y))+(p(x)-p(y))W(y)`。

第一项给 `L₁‖Dp‖`，第二项给 `PL₂`，第三项再给 `‖Dp‖L₁`，总量准确为 `PL₂+2‖Dp‖L₁`。w 的 Lipschitz 性本身也由真实域内 W 上界内部推得。代入 `L₁=Cqσ²(a)`、`L₂=Cq²σ²(a)`，精确整理为 `Cσ²(a)(q²P+2q‖Dp‖)`；没有漏掉另一个交叉项，也无需对常仿射 Dp 再假设二阶导数。

真实闭单元的 Taylor/节点再现引理用实际顶点值 `σ²(v_i)p(v_i)`，给值误差因子 2。梯度经真实内球仿射导数界和 `h≤κr` 给 `1+4κ`，从未把节点权平方误作插值函数平方。所有这些是在真实单纯形凸包上的全点结论，不对 L² 等价类求顶点值。

梯度左端在**闭单元边界**比较的是合法域内字段 G 与真实节点仿射导数，不能未经证明解释成边界外普通 fderiv。已有 `affineProduct_derivative_interior` 仅在单元内部将 G 识别为 σ²p 的真实普通 fderiv；该前提和方向已核对。弱梯度的 a.e. 转换及 L² 估计仍是下游义务，不在此冒称完成。

最终定理从 `dist(x,x)=0≤h` 内部取得 h≥0；不要求 h>0。r>0 是唯一几何除法的正性条件，h≤κr 因而蕴含 κ≥0；P 是 NNReal，允许 P=0。维数 d=0、h=0 均未被排除，顶点 0 仍存在，内球导数依赖使用不要求存在单位向量的通用算子范数判据。空域时不存在包含于 closure ∅ 的真实单纯形，量词蕴含正常，没有从空域选择空间点。

## 原文范围与未完成义务

本阶段清偿 Section 6 Step 3（`paper/main.tex:1572` 起）中实际 σ² 的闭单元导数供应以及乘真实仿射状态的点态节点误差。原文 `9.26-eq10`、`9.26-eq11` 是对完整 V_h 状态的真实加权 L²/梯度范数估计，当前定理尚未给出这些结论。

尤其 `|p(x)|≤P` 是显式的**单元点态**上界，P 在 C 之后量化；不能因单元有限维或已存在某个 P，就把右端 P 直接改写成不带体积/尺度因子的 L² 范数。仍须证明统一的真实单元 L² 控制并保留体积和形状因子，再处理 σ⁻¹ 加权、完整弱梯度 a.e. 身份及全域有限元求和。此处的点态 CLM 导数误差亦不是已经建立的弱 H¹ 范数界。

原一般 H² 状态的连续代表、节点插值与以 L² Hessian 为右端的 `eq:p1-interpolation` / `eq:p1-interpolation-energy` 没有由本阶段的光滑固定权和仿射状态自动完成；原完整 `prop:p1`、N3/N4 超逼近及下游完整命题均不能因本报告提升。保持 AUXILIARY 与原文 12/26。

## 实际依赖与本机证据

本次直接检查 `SpatialDerivatives` 中紧集 profile 导数供应、指数复合和统一允许权导数估计；`SpatialComparison` 的真实 UniqueDiff/Lipschitz 推导和实际乘子定义；`SimplexWithinInterpolation` 的闭单元 Taylor、仿射再现及真实内球误差；`AffineProductDerivative` 的真实乘积导数、两个交叉项、内部 fderiv 身份及二阶域内场的 Lipschitz 推导。亦读取 [T060 独立验收](T060-local-acceptance.md)，其 checked SHA 正是本次基线；既有依赖未改，且本次实际使用符合其前提。基础空间比较与高阶权导数的既有报告可见 [T050](T050-local-acceptance.md)、[T005](T005.md)，没有仅凭旧报告跳过实际依赖核对。

固定 `/tmp/carleman-squared-weights-full.log` 实际记录 `Build completed successfully (3637 jobs)` 和全部 4940 个 Carleman 声明递归审计通过。固定 `/tmp/carleman-squared-weights-local-axioms.txt` 实测 **1,422,034 bytes**，SHA256 **`0da8d4003158758e4b6532e7569f5cea36622fd375ebc77afcd8c08fcf83e726`**。已逐名读取全部 10 项展开类型并解析递归公理输出，每项恰为 `propext`、`Classical.choice`、`Quot.sound`；无 sorryAx 或额外数学公理。固定 `CheckAxioms` 逐项打印后还遍历所有 Carleman 声明执行递归 collectAxioms，不限于这 10 个表面入口。

## 同 SHA 远端证据与最终决定

已独立通过 GitHub API 读取实际 main/push [CI run 39167125090 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39167125090/attempts/1)：head SHA 精确为本次固定 SHA，整体 completed/success。三项 job 均绑定相同 SHA 且 completed/success：`state-check`（117792289257，完成 `2026-10-18T21:17:02Z`）、`lean`（117792289532，完成 `2026-10-18T21:19:30Z`）、`dashboard / snapshot`（117792877898，完成 `2026-10-18T21:19:40Z`）。实际 artifact API 确认 `lean-ci-result`（12150579520）及 `lean-declaration-evidence`（12150788782）均来自此 run/此 SHA，且均未过期。

已实际读取 `/tmp/carleman-squared-weights-main-ci/result.json`：status PASS，`checked_sha=source_head_sha=05aadb86ef406e8e1f843a74ddace902041d79e9`，targets 为 `Carleman`，ci_url 精确匹配上述 run/attempt，`finished_at=2026-10-18T21:18:32.893364+00:00`。Lean 4.35.0（提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）与 mathlib pin 均正确；结果生成时间与 job 上传/收尾完成时间分别核实，没有混淆。

已独立逐字节比较 `/tmp/carleman-squared-weights-main-axioms/axioms.txt` 和上述固定本机副本：完全相同，均为 **1,422,034 bytes**，SHA256 均为 **`0da8d4003158758e4b6532e7569f5cea36622fd375ebc77afcd8c08fcf83e726`**。再次从原始远端文本逐项解析 10 个声明的公理列表，均精确为三项标准基础公理；实际末行确认全部 **4940** 声明递归审计通过。

最终结论：**T061 / C077 PASS；10 声明可升 `REVIEWED / AUXILIARY`。** 未发现本次实际平方权、域内导数、常数量词、闭单元比较、乘积交叉项、节点误差或公理依赖方面需修复的缺陷。P→真实单元 L²、σ⁻¹ 加权、弱梯度 a.e. 转换、全域超逼近及一般 H² 插值仍不在完成范围，原文保持 12/26。

本次仅写此报告，没有修改证明源码、台账、root 导入或原论文，未 commit/push。
