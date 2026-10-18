# T051 / C067 独立本机验收

- `checked_sha`: `51e67cf2b206b1e754d90a53ccd03c6e80e570fc`
- `base_commit`: `9ea552502177ccffb3f50593567578fc207c2568`
- `reviewed_at`: `2026-10-18T20:05:58+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：原 Section 6 Step 1 中四类实际权的统一共享顶点邻接分级。**不包含 DST 加权 L² 正交投影稳定性，原文完成仍为 12/26。**

本次独立读取固定提交的四个新模块全部证明、16 项完整展开类型和相关实际依赖，对照原 `paper/main.tex` 的 `eq:grading`、`eq:fourweights` 及 Proposition 6.1 Step 1。执行者说明和 CI 均未代替数学审查；后续工作区增量不属于本报告。

## 全部 16 项声明

完整名称均以前缀 `Carleman.` 开始。位置相对于 `Carleman/`，顺序与固定 C067、T051 和交付声明 JSON 完全一致。

| # | 声明（省略 Carleman.） | 固定位置 | 独立数学核对 |
|---|---|---|---|
| 1 | `SimplicialPartition.VertexNeighbors` | `Spatial/SimplicialNeighbors.lean:12` | PASS；存在两个实际 simplex 顶点且其空间坐标相等，未用任意邻接标签替代几何。 |
| 2 | `SimplicialPartition.VertexNeighbors.symm` | `Spatial/SimplicialNeighbors.lean:15` | PASS；交换两顶点及等式方向，真实邻接对称。 |
| 3 | `SimplicialPartition.vertexNeighbors_dist_le` | `Spatial/SimplicialNeighbors.lean:19` | PASS；共享顶点属于两闭凸包，三角不等式给任意两单元点间距离≤两真实直径之和。 |
| 4 | `SimplicialPartition.vertexNeighbors_dist_le_max` | `Spatial/SimplicialNeighbors.lean:32` | PASS；真实有限最大直径给≤2h，无邻接数或单元数因子。 |
| 5 | `exists_weight_grading_threshold` | `Weights/GradingThreshold.lean:9` | PASS；正γ<Γ、正L给δ=min(1,log((γ+Γ)/(2γ))/(2L))>0，及所需非严格指数界和严格Γ余量。 |
| 6 | `SpatialProfile.scaled_multiplier_inverse_value` | `Spatial/NeighborWeightComparison.lean:14` | PASS；实际乘子的倒数恰对应τ与η同时取负。 |
| 7 | `SimplicialPartition.scale_grading_from_ratios` | `Spatial/NeighborWeightComparison.lean:28` | PASS；原正ℓ双侧比值条件在反向邻接上给ℓⱼ≤γℓᵢ，分母严格正。 |
| 8 | `SimplicialPartition.allowedWeight_neighbor_le` | `Spatial/NeighborWeightComparison.lean:34` | PASS；闭域Lipschitz界和真实2h距离界给实际σ(x)≤exp(2Lhq)σ(y)，τ完全消去。 |
| 9 | `SimplicialPartition.gradedWeight` | `Spatial/NeighborWeightComparison.lean:47` | PASS；实际 BoundedMultiplier，按 Bool 选择w或实际 inverseWeight ℓ w。 |
| 10 | `SimplicialPartition.gradedWeight_on_cell` | `Spatial/NeighborWeightComparison.lean:50` | PASS；在完整闭单元的受限体积测度下a.e.等于w或ℓᵢ⁻¹w，没有错误断言共享面上的逐点身份。 |
| 11 | `SimplicialPartition.gradedWeight_neighbor_le` | `Spatial/NeighborWeightComparison.lean:61` | PASS；正尺度因子与γ≥1给两种分支统一比较，所得双层单元a.e.不等式作用于实际权的绝对值。 |
| 12 | `p1GradingLimit` | `Spatial/UniformNeighborGrading.lean:12` | PASS；定义恰为原Γ_d=(sqrt(d+2)+1)/(sqrt(d+2)−1)。 |
| 13 | `p1GradingLimit_gt_one` | `Spatial/UniformNeighborGrading.lean:14` | PASS；对所有自然维数d，sqrt(d+2)>1保证分母正和Γ_d>1。 |
| 14 | `p1GradingLimit_two` | `Spatial/UniformNeighborGrading.lean:20` | PASS；Γ₂=3，实际平方根值经证明代入。 |
| 15 | `p1GradingLimit_three` | `Spatial/UniformNeighborGrading.lean:25` | PASS；实际非零分母及sqrt(5)平方身份给Γ₃=(3+sqrt5)/2。 |
| 16 | `allowed_weights_uniform_neighbor_grading` | `Spatial/UniformNeighborGrading.lean:34` | PASS；固定C¹ profile内部供应L，δ先于所有网格／正尺度／TimeWeight／τ／时刻／符号／分支；hqmax≤δ给四权的固定等级(γ+Γ_d)/2<Γ_d。 |

## 真实几何、原尺度条件与 a.e. 单元身份

SimplicialPartition 中每个 simplex 是实际非退化 d 单纯形，cell 是实际顶点凸包；inside 只要求 cell⊆closure S。VertexNeighbors 恰为两个实际顶点相等，且对称。共享顶点通过 subset_convexHull 同时进入两单元，随后使用真实 Metric.diam 与紧单元的有界性。整个几何证明对任意 x∈K、y∈K′成立，不要求这些点已在开域 S。有限最大直径由非负实数的 Finset.sup 定义，故 dist≤diam(K)+diam(K′)≤2h；空索引情形没有待证明的邻接对，也没有额外非空假设。

原双侧条件 γ⁻¹≤ℓᵢ/ℓⱼ≤γ 对所有共享顶点单元成立。scale_grading_from_ratios 在反向邻接 (j,i) 使用上界，再以ℓᵢ>0乘回，得到最终定理要求的ℓⱼ≤γℓᵢ。它没有错误地颠倒一个未经证明的比值不等式；双侧条件的下界虽无需直接调用，但在对称邻接及正尺度下与反向上界一致。最终全称单侧条件可按此已证引理从原条件供给，并未新增原文未清偿前提。ℓ与h_K的双侧可比性及形状正则性是原P1实现的其他条件，在当前邻接分级子结论中无需使用。

inverseScale 是真实有限和 Σᵢ1_{Kᵢ}ℓᵢ⁻¹。共享面上的和可能包含多个单元，故不能逐点声称等于任一侧尺度。代码调用真实 a.e. 分区定理，先在 volume.restrict S 下得到“若x∈Kᵢ则值为ℓᵢ⁻¹”。再由开凸 S、单元内部包含于 S、单元零测边界得到 volume.restrict Kᵢ≤volume.restrict S，正确向小测度转移a.e.身份，并用闭单元a.e.成员事实解除蕴含。gradedWeight_on_cell 因而恰在完整闭单元测度下成立。已直接复核 inverseScale、inverseWeight、ae_partition 和所用 cell_measure_le_domain；没有以全局逐点分片身份回避共享面问题。

gradedWeight 的 false 分支系数为1，true分支为ℓᵢ⁻¹。两者均严格正；前者由γ≥1得aᵢ≤γaⱼ，后者由ℓⱼ≤γℓᵢ及两个正分母得同一不等式。结合实际σ的正性后，分别对Kᵢ和Kⱼ合并a.e.身份，推出双层 `∀ᵐ x ∂volume.restrict Kᵢ, ∀ᵐ y ∂volume.restrict Kⱼ` 的实际绝对值比较。有限单元边界不产生附加项或常数。

## 四类实际权、反演和统一量词

底层实际权为 σ_{τ,η}(t,x)=q(t)^τ exp(ηρ(x)q(t))；TimeWeight 的 lower 给q≥1，故所有实数τ下均严格正。固定时刻两点比值中的q^τ准确消去，只剩exp(η(ρ(x)−ρ(y))q)。|η|=1、闭域profile的Lipschitz界及dist≤2h给exp(2Lhq)上界；涉及闭单元的ρ比较合法使用inside进入closure S，未擅自进入S。τ不进入这个常数。

scaled_multiplier_inverse_value 对所有实数η、τ逐点证明 σ_{−τ,−η}=σ_{τ,η}⁻¹；q非负保证Real.rpow_neg可用，exp_neg和乘积取逆也已明确处理。原σ取任一允许τ和η=±1后，σ⁻¹对应同时取负的τ、η；加上inverseSize=false/true，恰给σ、σ⁻¹、ℓ⁻¹σ、ℓ⁻¹σ⁻¹四类实际乘子。最终允许全部实τ的结论蕴含原有限允许指数族上的结论，没有把数值主定理权族扩张作为新假设，也未把仅η取负的q^τ exp(−ηρq)误认成整个σ的倒数。

最终定理的完整类型先固定维数d、开凸S、紧closure S、固定SpatialProfile及其闭域C¹性、固定1≤γ<Γ_d，然后才存在δ。smooth_profile_lipschitz 使用开凸闭包的真实UniqueDiffOn和紧集上的连续一阶导数界，内部产生L≥1；未把任意变化权族的Lipschitz常数输入为待清偿前提。空S分支也在该UniqueDiffOn证明中处理。原有界凸多面体与光滑固定ρ满足这里的条件。

设R=(γ+Γ_d)/(2γ)>1，故log R>0。证明实际选择δ=min(1,log R/(2L))，得到0<δ≤1、2Lδ≤log R及γexp(2Lδ)≤(γ+Γ_d)/2；γ<Γ_d另给严格余量。之后才全称量化索引类型、有限网格、ℓ、所有TimeWeight、τ、t、η、逆尺度选项和邻接对。非负h与TimeWeight.upper给hq(t)≤hqmax≤δ，再由指数单调性得到固定等级。δ仅依赖固定域/profile、d和γ，分级常数只依赖d、γ；二者均不依赖T、qmax、τ、时刻、网格单元数、邻接数、最小单元尺度或具体ℓ。

Γ_d确为原公式，且代码单独核对了原d=2、3的精确数值。一般自然维数上的几何分级结论更广，但没有声称所有维数的完整P1实现。原目标这一子步骤的量词及严格Γ余量得到保留。

## 固定依赖、构建与公理

导入闭包含94个Carleman模块，其中90个旧模块与基线逐字节一致，新增恰为本次四模块。C066的已验收声明版本即本次base；另针对C065实际使用的CellwiseInverseWeight导入闭包86模块，与其已验收版本 `99694c20834ac8d3b712f5e2d071a4e4ccfc308b` 全部逐字节一致。固定Carleman.lean显式导入本次四模块。已实际阅读相关几何、分区、尺度乘子、Lipschitz来源和真实allowed权定义，未仅沿用旧报告结论。

原稿、治理协议、Lean/mathlib pin和CI工作流与base一致。原稿SHA256为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean pin为4.35.0；本机实际mathlib HEAD为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，其工作树干净。

固定CheckAxioms对16项逐一执行 `#check @...` 和 `#print axioms ...`，再按privateToUserName遍历全部Carleman声明并递归collectAxioms，仅许可 `propext`、`Classical.choice`、`Quot.sound`。16项完整类型已逐名核对，公理集合均恰为这三项正常基础公理。固定本地证据全部1259条显式公理输出也未发现其他公理；递归末行实际为 `Axiom audit passed for all 4777 Carleman declarations.`，无sorryAx。

`/tmp/carleman-neighbor-grading-full.log` 实际包含 `Build completed successfully (3600 jobs).` 和上述4777声明审计。固定 `/tmp/carleman-neighbor-grading-local-axioms.txt` 为 **1,335,979 bytes**，SHA256 **`7cb4201f8a25ed807e9ff332dad7f8d249487bd3af144a936821067c5f282b9d`**。交付声明JSON与固定C067/T051清单16/16顺序相同。

已独立通过 GitHub connector 读取 [main CI 39161391239 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39161391239/attempts/1)：main/push，head SHA 为固定 `51e67cf2b206b1e754d90a53ccd03c6e80e570fc`，completed/success。lean（117775259134）、state-check（117775259217）、dashboard / snapshot（117775840851）三项 jobs 均 completed/success；工具链准备、root 构建、checked source 记录、两份证据上传和同次快照生成步骤均 success。同 run 的 lean-ci-result artifact（12148459922）及 lean-declaration-evidence artifact（12148544324）均绑定该固定 SHA。

已实际读取 `/tmp/carleman-neighbor-grading-main-ci/result.json`：status PASS，`checked_sha=source_head_sha=51e67cf2b206b1e754d90a53ccd03c6e80e570fc`，targets 为 Carleman，`finished_at=2026-10-18T20:03:02.111484+00:00`，ci_url 与上述 run/attempt 完全一致。实际 Lean 4.35.0 提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib 为上述 pin。

原始远端 `/tmp/carleman-neighbor-grading-main-axioms/axioms.txt` 与固定本地副本已独立逐字节比较，完全相同：**1,335,979 bytes**，SHA256 **`7cb4201f8a25ed807e9ff332dad7f8d249487bd3af144a936821067c5f282b9d`**。另逐名核对远端16/16完整类型及每项正常基础公理集合，末行实际为 **`Axiom audit passed for all 4777 Carleman declarations.`**，无sorryAx或未批准数学公理。未混用其他提交或后续工作区产物。

## 验收决定

**C067：PASS，可升级为 REVIEWED，scope 保持 AUXILIARY。** 固定版本16项未发现需要修复的实际权身份、几何、测度、反演符号、尺度比值或统一量词缺陷；完整类型、递归公理和同SHA正式main CI均已独立核实。

尚未证明由此分级条件推出DST的实际一致质量L²正交投影稳定性，也没有因此完成原P1命题的H²插值、超逼近、椭圆正则性和连续热CE等剩余义务。不能提升P011/P014/P015或其他完整原文结果，原文仍12/26。

本次仅写本报告，没有修改数学代码、台账、覆盖表、原稿或root导入，没有commit/push。
