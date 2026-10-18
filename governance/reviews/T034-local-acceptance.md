# T034 / C050 独立本机验收

- `checked_sha`: `27c5e0e5a60b860f08e4c74c5d7de81f7498781f`
- `base_commit`: `d999e5b3779aa82efee2da8e162b86148dc1f715`
- `reviewed_at`: `2026-10-18T17:25:25+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- 范围：**CONDITIONAL**，仅验收从实际插值、加权投影稳定性和梯度逆估计推导原 N3、特定投影测试的 N4 空间超逼近，并组装实际数值数据。**不提升 P011 / Proposition 6.1、P014 / Theorem 7.2、P015 / Theorem 7.3。**

本报告独立读取固定提交导出的六个新模块、25 项展开类型、相关依赖与原 `paper/main.tex` Section 6 P1 Step 2–3。执行者的分析说明用于确定验收范围，没有替代实际证明检查。没有读取后续未提交数学草稿作为本次证据。

## 全部 25 项声明

名称均加前缀 `Carleman.Physical.`。位置为固定提交下的 `Carleman/Control/` 文件；表中 PASS 是逐项语义结论。

| # | 声明 | 源码位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `conformingProjector` | `ConformingProjectionError.lean:14` | PASS；真实 L2 正交投影后包含回 V 的线性映射。 |
| 2 | `conformingProjector_eq_Q` | `ConformingProjectionError.lean:17` | PASS；与实际 reconstruction.Q 在 V 上精确相等。 |
| 3 | `conformingProjector_inclusion` | `ConformingProjectionError.lean:20` | PASS；对每个 X 状态的包含保持恒等。 |
| 4 | `conformingProjector_error_decomposition` | `ConformingProjectionError.lean:25` | PASS；对任意 v∈V、x∈X，准确证明 `(Id−P)v=(Id−P)(v−Rx)`。 |
| 5 | `conformingProjector_l2_error` | `ConformingProjectionError.lean:31` | PASS；实际乘子 L2 误差由投影稳定性得到常数 `1+Cp`。 |
| 6 | `conformingProjector_energy_error` | `ConformingProjectionError.lean:46` | PASS；任意 V 半范数的误差由辅助权稳定性和逆估计得到 `p(e)+CI*Cp*‖ζe‖`。 |
| 7 | `ConformingInterpolationBounds` | `ConformingInterpolation.lean:22` | PASS / 条件接口；字段是实际插值误差、投影稳定性和逆估计，没有假定目标投影误差。 |
| 8 | `conformingWeightedApproximation_of_interpolation` | `ConformingInterpolation.lean:44` | PASS；得到真实 N3，`aE=(CE+CI*Cp*Cζ)h`、`a0=(1+Cp)C0 h²`。 |
| 9 | `GalerkinSuperapproxInterpolation` | `GalerkinSuperapproxInterpolation.lean:19` | PASS / 条件接口；对实际 V 内 σ²z 的插值误差，以逆权能量衡量。 |
| 10 | `galerkinSuperapprox_of_interpolation` | `GalerkinSuperapproxInterpolation.lean:42` | PASS；识别实际 Π(σ²z)，通过半范数差对称性得到原方向的误差，常数 `CE+CI*Cp*Cζ`。 |
| 11 | `conformingHeatGradient` | `ConformingHeatGradient.lean:15` | PASS；唯一弱 Sobolev jet 的一阶 Euclidean L2 导数场的真实加权范数。 |
| 12 | `conformingHeatGradient_nonneg` | `ConformingHeatGradient.lean:18` | PASS；真实半范数的非负性。 |
| 13 | `conformingHeatNorm_le` | `ConformingHeatGradient.lean:21` | PASS；展开 m=1 的实际 N 范数，给 `Nσ(v)≤q‖σv‖+‖σ∇v‖`，无维数因子。 |
| 14 | `scaled_seminorm_le_auxiliary` | `ConformingHeatGradient.lean:36` | PASS；由 a.e. `q|σ|≤|ζ|` 得真实 L2 范数比较，`q>0` 保证倒数步骤合法。 |
| 15 | `conformingHeatNorm_le_auxiliary` | `ConformingHeatGradient.lean:44` | PASS；零阶项被辅助权预算控制，得到梯度与辅助 L2 的和。 |
| 16 | `conformingHeatInverse_of_gradient` | `ConformingHeatGradient.lean:52` | PASS；梯度逆界转为完整能量逆界，常数准确为 `1+CI`。 |
| 17 | `HeatInterpolationData` | `HeatInterpolationData.lean:21` | PASS / 条件接口；原 Step 2 的实际梯度、辅助 L2 和 L2 插值预算均显式。 |
| 18 | `HeatInterpolationData.toBounds` | `HeatInterpolationData.lean:42` | PASS；把联合预算分为能量和辅助误差，CI 改为 `1+CI`，两误差系数均用 CE。 |
| 19 | `HeatInterpolationData.approximation` | `HeatInterpolationData.lean:59` | PASS；得到 `aE=(CE+(1+CI)Cp CE)h` 及原 h² 的 L2 阶。 |
| 20 | `HeatSuperapproxData` | `HeatInterpolationData.lean:70` | PASS / 条件接口；真实 σ²z 插值的逆权梯度加辅助 L2 预算，尺度为 `h*qmax`。 |
| 21 | `HeatSuperapproxData.toBounds` | `HeatInterpolationData.lean:88` | PASS；同一预算给逆权能量与辅助误差，未额外假定投影超逼近。 |
| 22 | `HeatSuperapproxData.superapprox` | `HeatInterpolationData.lean:105` | PASS；特定测试的空间 N4，常数 `CE+(1+CI)Cp CE`。 |
| 23 | `heatInterpolationErrors` | `InterpolatedHeatNumericalData.lean:11` | PASS；真实 ηA=0，非负输入给合法 ErrorScales，未制造正缺陷。 |
| 24 | `heatInterpolationErrors_orders` | `InterpolatedHeatNumericalData.lean:21` | PASS；显式 Cap 为两系数的 max，同时推出 aE≤Cap*h、a0+ηA≤Cap*h²。 |
| 25 | `interpolatedHeatNumericalData` | `InterpolatedHeatNumericalData.lean:43` | PASS；完整两符号/全部允许 τ 的局部数据构造实际 NumericalData，N3/N4 均为上述推导的输出。 |

## 真实投影、范数及 Step 2

令 R 为 X→V 包含，P 为 V 中表示的 L2 正交投影。P 的定义直接使用 `X.orthogonalProjectionOnto`，并证明 `P=Q|V` 及 `PR=R`；没有使用任意幂等替身或 Ritz 投影。对 e=v−Rx，线性性给出 `v−Pv=e−Pe`。L2 半范数的三角不等式与实际加权投影稳定性给 `(1+Cp)‖σe‖`。

能量推导分别在 X 的状态 `Πe` 上应用逆界，再用 ζ 加权投影稳定性：`p(Pe)≤CI‖ζΠe‖≤CI*Cp‖ζe‖`。CI 的非负性用于乘法；接入插值辅助误差时再用 Cp≥0。因此并非借助未知的能量投影稳定性，也没有将所要证明的 N3 重新命名为前提。

`ConformingInterpolationBounds` 的插值器是实际函数 `I:D→X`，不是任意误差标量；其误差均为原函数减去 I v 的实际包含。D 是原域子空间，要求 D≤H^(2m)、D≤V；能量采用 `conformingWeightedSeminorm` 并通过其已证等式转换为原 `conformingWeightedNorm`，参数范数来自 D 的唯一弱 jet。推导对每个 t∈[0,T]、每个 v∈D 成立，没有把原闭区间条件缩成节点或 a.e. 时间条件。

普通插值输入的三个误差系数产生

`aE = (CE+CI*Cp*Cζ)h`, `a0 = (1+Cp)C0 h²`。

热输入的梯度加辅助误差预算进一步给 `Cζ=CE` 和能量逆系数 `1+CI`，因此最终热误差确为

`aE = (CE+(1+CI)Cp CE)h`, `a0 = (1+Cp)C0 h²`, `ηA=0`。

## 一阶弱梯度与辅助权

已直接追查 `domainSobolevJet`、`sobolevJetEquiv` 和 `WeakSobolevJet.value_injective`：该 jet 由原 L2 类唯一恢复，field 1 满足每个坐标方向的分布弱导数恒等式。导数纤维为 `EuclideanSpace ℝ (Sym (Fin d) 1)`，每个一阶坐标恰出现一次。因此 `conformingHeatGradient` 是 `‖σ∇v‖L2`，没有输入自由命名的梯度、给不同 v 任意选择导数，或使用比原梯度更弱的数值量。

m=1 时原能量平方为 `(q‖σv‖)²+‖σ∇v‖²`。证明展开 `Fin 2` 并用真实零阶场与 v 的加权范数恒等式，得 N≤两项之和；系数为 1，没有引入 d、X 维数、节点数或 T 因子。

`scaled_seminorm_le_auxiliary` 使用实际乘子 a.e. 比较。由正 q 将 `q|σ|≤|ζ|` 改写为 `|σ|≤q⁻¹|ζ|`，应用真实 Lp 范数界后乘回 q；`w.pos t` 在调用点保证严格正性。于是完整能量被梯度加 `‖ζv‖` 控制，梯度逆常数 CI 给完整逆常数 `1+CI`。联合插值预算中的梯度项非负，因此同一 CE 也控制辅助 L2 项，无漏加系数。

ζ、ξ 仍是显式 `BoundedMultiplier`，本阶段没有构造网格尺度 ℓ，也没有证明它们已经等于 `ℓ⁻¹σ` 或 `ℓ⁻¹σ⁻¹`。这种具体选择下，支配条件由 `qℓ≤1` 供应；从网格分级、ℓ 与 h 的比较及足够小的 hqmax 推出此条件，仍属于具体实例义务。现有证明没有把此义务当作已完成。

## Step 3 的逆权、双乘法与差的符号

`GalerkinSuperapproxInterpolation` 和 `HeatSuperapproxData` 中待插值对象均为

`v = σ(σ(Rz)) ∈ V`。

两次实际 `conformingWeight` 使用原 V 的乘法保持见证 hw。没有要求 σ 保持 X，也没有把双乘法换成两次投影，更没有扩大原允许指数范围到 2τ。外层逆权准确为 `ρ.neg.multiplier w (-τ)`，同时反转空间符号和 q 指数，正是 σ⁻¹。

证明在 V 内验证 `Pv=R(galerkinWeightedTest z)`，再对 v−Pv 应用真实能量投影误差。原 N4 要求的是相反符号 `R(Tz)−σ²Rz`；末尾用同一个实际加权半范数的 `map_sub_rev` 精确翻转，非绝对值遗漏或符号误认。所得常数为 `(CE+CI*Cp*Cζ)`，热梯度预算下是 `CS+(1+CI)*Cp*CS`，尺度恰为 `h*qmax*Nσ(Rz)`。

原稿 Step 3 另列零阶 h²qmax² 界。本次条件推导利用 `q|σ⁻¹|≤|ξ|` 和原梯度加辅助 L2 预算直接控制零阶项，因此不必再次输入该更细的单独界；没有由此损失原所需 hqmax 超逼近阶。该推导依赖的支配条件显式保留。

J 的类型为 V→X，但局部超逼近预算仅约束上述双乘法状态上的 J 值。没有声明所有 H1 函数拥有节点值，或已构造全 H1 上的节点插值器；也没有要求 I、J 线性。具体实现仍须给出合法插值函数及预算；I 可用于原 H2 域，J 可在实际连续双乘法状态集合上实现节点插值并在其他 V 元素上扩展。

超逼近对每个 hw 是条件式陈述；本次孤立 NumericalData 构造不供应 A2 保持性。应用到完整热转移时仍须供应原 AllowedFamily，其 form_preserving 提供 hw，不能利用没有 hw 而空真来宣称 P1 实例已成立。

## 原数值数据组装、量词与边界

`interpolatedHeatNumericalData` 量化全部 `e:Bool`、全部 `|τ|≤τStar`，使用同一组 CI/Cp/CE/C0/CS、实际 I/J，以及允许随符号、τ、时刻变化的辅助乘子 ζ/ξ。两个 Bool 分支的 `ρ.signed e` 具有同一 `ρ.bound`，故时间常数准确为 `2β(τStar+ρ.bound)`。真实 `TimeWeightRegularity` 用于 T033 的已证明二次型导数、端点、对称非负和时间界，不是由局部空间插值预算假定这些时间结论。

新 N3 与特定测试空间超逼近填入既有 `galerkinNumericalData`；实际刚度为从原形式构造的 `galerkinStiffness`，缺陷为零，R/J/Γ/lift 和观察仍为实际包含、正交投影、恒等普通 lift 与真实 ambient 伴随，Cnum=1。N1 中额外的单射/自伴非负、N2 的物理右逆以及 N4 的精确测试能量恒等式由既有实际构造定理提供；NumericalData 不是重新宣称自身包含这些未列出的字段。

`heatInterpolationErrors_orders` 的 Cap 是显式公式

`max (CE+(1+CI)*Cp*CE) ((1+Cp)*C0)`，

不含 mesh、q、qmax、T 或 X。所有新误差证明只做固定时刻空间范数计算，未出现时间积分或节点求和，因此没有额外 T 或节点数因子。非负 CI、Cp、CE、C0 和 mesh 允许零值，误差构造与 max 比较均无零分母问题。空间超逼近常数保留其给定 CS；构造 NumericalData 本身没有另加 Csuper 的正性字段，后续调用统一转移定理时仍须供应其要求的非负常数。

这里的统一性是：若某个离散化族能以共同局部常数供应这些数据，输出公式仍使用这些共同常数。代码不从每个 X 或网格另行选择常数，但也没有证明任意 X 都具有统一局部估计。此阶段结束于实际 NumericalData，没有新增从具体网格到物理控制的完整总定理，更没有单独清偿连续 A4。

尚待证明的实例包括：P1 网格与 ℓ、原分级条件、四个权的投影稳定性、实际插值和局部 L2/梯度/辅助误差、逆估计及双乘法状态的局部超逼近；此外原 Dirichlet 形式、连续解析条件和连续热 CE 仍需实例化。上述条件不能因本次组装成功而删除。

## 固定依赖、构建与公理

最终新模块的 Carleman 导入闭包为 293 个模块，其中 287 个既有模块相对基线逐字节未变，新增恰为本次六模块。六模块全部在固定 `Carleman.lean` 中显式导入。原稿、治理协议、Lean/mathlib pin、CI 工作流均未变；原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

逐项检查本机实际展开类型和公理输出，25/25 与源码及固定 C050/T034 清单一致，均只依赖 `propext`、`Classical.choice`、`Quot.sound`。本机 `/tmp/carleman-projection-errors-full.log` 记载完整构建 `3524 jobs` 成功。固定 `/tmp/carleman-projection-errors-local-axioms.txt` 为 1,153,323 bytes，SHA256 为 `6f6b15415444a46ed9af8cc56428cca56470cf1a4eb28ee8f7e699f2036a09ac`，实际末行是 `Axiom audit passed for all 3964 Carleman declarations.`。

固定审计工具遍历所有经 `privateToUserName` 归属 Carleman 的公开/私有声明，并用 `collectAxioms` 递归收集依赖，只准许上述三项正常基础公理。没有 sorryAx 或新数学公理。

已独立通过 GitHub connector 读取 [main CI 39149104207 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39149104207/attempts/1)：head SHA 为本次固定 SHA，main/push、completed/success。三个实际 jobs 均成功：lean（117738913784）、state-check（117738913974）、dashboard / snapshot（117739538150）。Lean job 的 pin、root build、checked-source 记录和公理产物上传步骤均 success。

同次 artifact 元数据确认 `lean-ci-result`（12144273288）和 `lean-declaration-evidence`（12144487549）均绑定 run 39149104207 及固定 head SHA。原始 `/tmp/carleman-projection-errors-main-ci/result.json` 已实际读取：PASS，`checked_sha=source_head_sha=27c5e0e5a60b860f08e4c74c5d7de81f7498781f`，target=Carleman，`finished_at=2026-10-18T17:22:03.805694+00:00`。工具链 Lean 4.35.0（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）及 mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 与固定源码一致。

正式远端 `/tmp/carleman-projection-errors-main-axioms/axioms.txt` 为 1,153,323 bytes，SHA256 为 `6f6b15415444a46ed9af8cc56428cca56470cf1a4eb28ee8f7e699f2036a09ac`，已与上述固定本机副本逐字节比较，相同。再次核对远端文件中 25/25 项的完整类型与三项标准公理，以及 3964 声明的递归审计 PASS。没有用后续 PiecewiseAffine 草稿或其他提交的产物替代证据。

## 验收决定

**C050：PASS，可升级为 REVIEWED，scope 保留 CONDITIONAL。** 本次全部 25 项声明未发现需要修复的数学、符号、常数或量词缺陷。该结论只覆盖所列实际投影误差、插值预算到 N3/空间 N4 的推导及数值数据组装；具体网格与局部解析估计仍未供应，不提升 P011/P014/P015。

本次仅写本报告，未修改数学代码、台账、原稿、root 导入或覆盖表，未 commit/push。
