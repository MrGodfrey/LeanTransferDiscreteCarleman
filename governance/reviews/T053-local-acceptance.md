# T053 / C069 独立本机验收

- `checked_sha`: `24509632c6ae2b1a3bb9e30eca790c82decec4e3`
- `base_commit`: `df8b853f9203194295be90f39ef5f797af31b9b3`
- `semantic_checked_at`: `2026-10-18T20:18:37+00:00`
- `reviewed_at`: `2026-10-18T20:21:32+00:00`
- `result`: **PASS**；C069 可升 REVIEWED，范围保持 AUXILIARY
- `axiom_check`: **PASS**；同次远端原始产物与固定本机副本逐字节一致
- `scope`: **AUXILIARY**
- 范围：真实全维单纯形上重心坐标的超水平集、Lebesgue 分布和一阶矩。二阶矩、质量矩阵积分身份、完整节点表示及加权投影均未完成，不提升具名原文结果，计数仍为 12/26。

独立读取固定模块全部证明、7 项实际展开类型、关键实际依赖、固定 mathlib 源码以及原 `paper/main.tex` Section 6。执行者说明仅用于定位；后续 BoundedSecondMoment 等工作区草稿不在本次范围。

## 全部 7 项声明

名称均加前缀 `Carleman.`；行号相对于固定提交的 `Carleman/Spatial/SimplexBarycentricDistribution.lean`。与固定 C069、T053 及交付 JSON 清单逐项一致。

| # | 声明 | 行 | 独立核查结论 |
|---|---|---|---|
| 1 | `mem_simplexCell_iff_barycentric` | 13 | PASS；实际全维 AffineBasis 的凸包身份给成员当且仅当所有实际重心坐标非负。 |
| 2 | `simplexBarycentric_homothety` | 20 | PASS；真实顶点中心 homothety 上的坐标为 rλ_j+(1−r)δ_ji，对任意实 r、全部空间点成立。 |
| 3 | `simplexBarycentric_superlevel_image` | 27 | PASS；0≤t<1 时以顶点 i 为中心、比例 1−t 的实际单元像，恰为 K∩{λ_i≥t}。 |
| 4 | `simplexBarycentric_superlevel_volume` | 61 | PASS；真实 Haar/Lebesgue 缩放给 ofReal((1−t)^d)·volume(K)，维数及缩放方向准确。 |
| 5 | `simplexBarycentric_superlevel_real` | 68 | PASS；真实受限测度与可测超水平集的 real 值恰为 (1−t)^d·volume.real(K)。 |
| 6 | `simplexBarycentric_le_one` | 78 | PASS；非负坐标之和恰为 1 给每个坐标≤1，无额外点态或 a.e. 假设。 |
| 7 | `integral_simplexBarycentric` | 83 | PASS；实际连续可积坐标经真实 layer-cake、参数端点排除与幂积分得到 vol(K)/(d+1)，包含 d=0。 |

## 原文定位与范围

原 Section 6.1（`paper/main.tex:1469–1485`）使用真实一致质量 P1 空间及 L² 内积；Step 1（1506–1521）要求原四类权下的 L² 投影稳定性。当前模块为把已有有限系数强制性与真实单元积分联系起来提供重心坐标分布及一阶矩。它是这一证明路线的数学辅助步骤，原文没有单独具名的“重心一阶矩定理”可据此提升完成计数。

本批声明的 T 类型为 `Affine.Simplex ℝ (SpatialCoordinates d) d`：d+1 个实际仿射独立顶点，环境为真实 d 维 EuclideanSpace；K 是真实顶点凸包。原 d=2,3 的非退化单纯形是其直接特例；全部 d∈ℕ 的扩展没有削弱原目标。最终一阶矩等式对每个 T 和每个顶点指标 i 成立，无形状正则、尺度、网格、权、状态或已有积分公式前提。

已读取 [T052 系数型强制性验收](T052-local-acceptance.md) 以核对阶段边界。当前模块没有将 p1CoefficientForm 声称为真实质量积分，也未证明 ∫λ_iλ_j、二阶矩、完整 V_h 节点对应、加权节点测试或 L² 投影稳定性。那些义务仍待，C069 保持 AUXILIARY，原文计数 12/26 不变。

## 实际重心坐标与双向集合等式

直接检查 SimplexNodalInterpolation 中的定义：simplexAffineBasis 由 T 的实际仿射独立与全维张成构成，simplexBarycentric 是该真实 AffineBasis 的 coord。已有顶点身份 λ_j(T_i)=δ_ji 及全空间坐标和 Σλ_j=1 均在本次实际使用。第 1 项调用真实 `convexHull_eq_nonneg_coord`，所以非负坐标刻画的是 K 本身，没有额外抽象概率空间或预设“分布”。

第 2 项展开 homothety 为 r(x−T_i)+T_i，对真实 AffineMap 使用 map_vadd、map_smul 和 linear_apply_vsub，再代入顶点坐标。其结果是 `rλ_j(x)+(1−r)δ_ji`，平移项、特殊指标和乘法次序均准确；该式不只在 K 上成立，也不要求 r 正。

第 3 项才使用 0≤t<1，令 r=1−t>0。正向：对每个 j，rλ_j(y)+tδ_ji≥0，故像点在 K；i 坐标又≥t。反向：给 x∈K 且 λ_i(x)≥t，实际取逆 homothety 比例 r⁻¹。j≠i 的坐标是 r⁻¹λ_j(x)≥0；j=i 的坐标精确化为 `(λ_i(x)−t)/(1−t)≥0`。因所有坐标非负，逆像属于 K。最后用同中心 homothety 的真实复合身份及 r≠0 得原像点恰为 x。

因此是双向真实集合等式，包含超水平面边界，使用的是 ≥ 而非 >。t=0 正常给恒等变换；t=1 不在这三个分布声明的适用范围内，证明没有对零比例强行求逆。

## Lebesgue 缩放、可测性和 real 测度

已直接读取固定 mathlib 的 `Measure.addHaar_image_homothety` 及底层 `addHaar_smul`。它将同心缩放拆成真实平移、标量缩放、平移，以 Haar 平移不变性和维数缩放得到

`volume(H_{T_i,r}(K)) = ofReal(|r^finrank|) * volume(K)`。

这是像集合的体积乘因子 r^d，不是推前测度中的倒数。SpatialCoordinates d 的 finrank 精确为 d；r=1−t>0 使绝对值等于 (1−t)^d，无 d 与 d+1 的指数混淆。没有引入独立指定的质量或 Jacobian 常数。

超水平集由真实连续仿射坐标和常数比较构成，可测。第 5 项先展开 `(volume.restrict K).real`，通过 restrict_apply 得到超水平集与 K 的交，再按 inter_comm 对齐第 4 项。ENNReal.toReal_mul 和非负 (1−t)^d 的 toReal_ofReal 给准确实数乘积。K 的紧性和环境 volume 的局部有限性保证这里的体积有限，故不是利用无限测度 toReal=0 得到空洞公式。

本次直接核对 simplicialCell 的真实有限顶点凸包、紧性和可测性依赖。固定模块导入 AffineChangeVolume 以取得相关实际空间/测度依赖，但新的分布证明使用的是上述真实 homothety Haar 定理，不依赖一个未证明的单元分布输入。

## layer-cake、一阶矩与端点

λ_i 在 K 上非负，且由 Σ_jλ_j=1、各项非负及有限和单项界得 λ_i≤1。其连续性和 K 紧性先供应真实 Integrable。使用 ae_restrict_mem 将这些点态单元性质转成受限测度下的 0≤λ_i≤1 a.e.，随后才应用固定 mathlib 的 `Integrable.integral_eq_integral_Ioc_meas_le`。

已阅读该 layer-cake 定理的实际证明：从非负可积实函数的真实分布积分公式出发，保留 `{λ_i≥t}` 的尾集合，并利用 λ_i≤1 将 t>1 的尾测度消去。由此得到

`∫_K λ_i = ∫_(0,1] (volume|K).real {λ_i≥t} dt`。

第 3–5 项只对 t<1 有效，而参数积分区间包含 1。代码在这里明确使用 `Measure.ae_ne (volume : Measure ℝ) 1`，再向实参数区间限制；与 t∈(0,1] 合并得到 t<1，才代入分布公式。所排除的是**一维实参数轴上的单个端点**，不是空间中的顶点或 λ_i=1 的空间集合。没有把分布公式在 t=1 的空间结论偷偷作为假设。

之后实际实值积分为 `volume.real(K) * ∫_(0,1] (1−t)^d dt`。integral_mul_const 的常数提出、Ioc 与正向 intervalIntegral 的转换以及 `integral_comp_sub_left` 的换元均准确；后者将 0..1、1−t 换为同一正向 0..1 的幂积分，没有遗失负号。固定 `integral_pow` 给 `(1^(d+1)−0^(d+1))/(d+1)=1/(d+1)`，其中 d+1≠0，最终结果为 vol(K)/(d+1)。没有误乘 d!、遗漏体积或把第一矩归一化为一个与体积无关的数。

## d=0、完整量词和剩余结论

所有七项的实际完整类型都只以 d∈ℕ、真实 d-simplex T、顶点指标以及明示的 t 范围为输入，没有 0<d 或空间 Nonatomic 前提。d=0 时 Fin(d+1) 只有一个指标，坐标恒为 1，K 是零维空间的整个单点；其 volume 并不需要为零。对 0≤t<1，比例仍正，(1−t)^0=1，故分布恰为完整 K 的体积；一阶矩自然是同一体积除以 1。

mathlib 的 Haar 标量缩放证明本身在零维单独处理 Subsingleton 分支，并未普遍假设单点零测。本模块最终积分只在参数空间 ℝ 使用无原子性，因此不会把正维空间的单点零测错误传播到 d=0。虽然分布声明没有包含 t=1，最终积分覆盖整个 (0,1]，仅用合法的参数 a.e. 修改，结论没有缺口。

相对于本批辅助目标，没有发现新增未清偿数学前提。结论是精确等式，因子仅为 1/(d+1)，对所有单元几何和所有顶点相同；无 T 时间、网格、qmax、权或状态依赖问题。它仍不包含二阶重心矩、真实质量矩阵、加权投影或原 Proposition 6.1 的完整证明。

## 固定版本、构建与递归公理

固定模块的 Carleman 导入闭包共 35 模块，其中 34 个旧模块相对 base 逐字节未变；唯一新增模块已被固定 Carleman.lean 显式导入。7 项与固定 C069/T053、源码及交付 JSON 顺序一致。AGENTS、治理协议、原论文、Lean/mathlib pin 和两 CI 工作流相对 base 不变；原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

本机 mathlib HEAD 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，工作树干净，Lean pin 为 4.35.0。所读 layer-cake、Haar 缩放、真实区间换元和幂积分源码均来自该固定版本。

固定 CheckAxioms 对七项执行完整 `#check @...` 和 `#print axioms ...`，随后以 privateToUserName 识别所有 Carleman 公开/私有声明并递归 collectAxioms，仅允许 propext、Classical.choice、Quot.sound。7/7 实际展开类型已独立阅读，递归公理集合均恰为这三项正常基础公理，无隐藏积分身份或分布假设。

固定 `/tmp/carleman-barycentric-distribution-local-axioms.txt` 实际为 1,341,795 bytes，SHA256 `dab9591a0213156c5d338221a7eae0b8885b1be5b5860900455b422825b37426`，末行 `Axiom audit passed for all 4794 Carleman declarations.`。实际 `/tmp/carleman-barycentric-distribution-full.log` 含 `Build completed successfully (3609 jobs).` 和同一全局审计 PASS，无 sorryAx 或未批准数学公理。

已独立通过 GitHub connector 核实同 SHA 的 [main CI 39162631089 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39162631089/attempts/1)：main/push，head_sha=`24509632c6ae2b1a3bb9e30eca790c82decec4e3`，顶层 completed/success。`lean`（117778946936）、`state-check`（117778947063）、`dashboard / snapshot`（117779760149）三个 jobs 均 completed/success。Lean pin、证明目标构建、checked-source 记录及两项证据上传步骤成功，缓存收尾亦完成。

同 run 的 `lean-ci-result` artifact 12148604316 和 `lean-declaration-evidence` artifact 12149381936 元数据均绑定本次固定 SHA。独立读取实际 `/tmp/carleman-barycentric-distribution-main-ci/result.json`：status PASS，checked_sha=source_head_sha=`24509632c6ae2b1a3bb9e30eca790c82decec4e3`，ci_url 精确对应上述 run/attempt，finished_at=`2026-10-18T20:20:08.265888+00:00`，target 为 Carleman，Lean 4.35.0（提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）与 mathlib pin 均吻合。

实际 `/tmp/carleman-barycentric-distribution-main-axioms/axioms.txt` 与固定本机副本独立逐字节比较，完全相同：1,341,795 bytes，SHA256 `dab9591a0213156c5d338221a7eae0b8885b1be5b5860900455b422825b37426`。另逐名复核全部七项实际展开类型和标准三公理集合，末行确认全部 4794 项递归审计 PASS。没有混用后续源码、其他 SHA 或其他运行的产物。

## 验收决定

**C069：PASS，可升级为 REVIEWED，scope 保持 AUXILIARY。** 七项未发现需修复的集合等式、测度方向、可积性、端点、零维、量词或公理缺陷；固定版本语义、实际类型、递归公理及同 SHA 三项 CI 均已独立核实。接受范围只限真实重心分布与一阶矩，二阶矩/质量积分/投影仍待，原文完成计数保持 12/26。

本次仅写本报告，未修改数学源码、台账、root 导入、原稿或覆盖表，未 commit/push。
