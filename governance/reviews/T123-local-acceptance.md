# T123 / C139 独立本机验收

- `checked_sha`: `e56df9d1895554e8cdfacc7e52c86bac51a08e6c`
- `base_commit`: `b40c6b3a3e783529e21adc5a699f4d4d19c4edbe`
- `reviewed_at`: `2026-10-19T05:57:16+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：全部原弱 H²∩H¹₀ 状态的同一闭包连续边界零代表、实际 conforming 节点插值、真实 H¹₀ 误差 jet，以及每个闭单元上的值和完整弱梯度误差界。全域允许权、网格尺度求和及投影组合尚待，P011 不提升，原文保持 **14/26**。

本 Agent 从固定 git 对象读取三模块全部证明、8项完整展开类型、原 `paper/main.tex` Section 6 P1 定义与 Step 2（1466–1489、1530–1548）、T123 分析、MATH_SPEC 及 C139/T123 条目，并独立检查实际依赖。规格、执行者自检和 CI 未替代数学审查。未来 T124 加权模块、变化中的工作树和 `.ci/axioms.txt` 均未用作本次依据。

## 全部八项声明

名称省略公共前缀 `Carleman.`，位置以 `Carleman/Spatial/` 为根；顺序与交付 JSON、固定 C139/T123 清单完全一致。

| # | 声明 | 固定位置 | 独立结论 |
|---|---|---|---|
| 1 | `SimplicialPartition.nodalSobolevJet_mem_dirichlet` | `H2NodalErrorJet.lean:19` | PASS；同一真实节点 jet 的 value 是已证 H¹₀ 的 nodalLp，完整弱导数唯一性将其提升为原 H¹ 图闭包成员。 |
| 2 | `SimplicialPartition.nodalH2ErrorJet` | `H2NodalErrorJet.lean:27` | PASS；实际 def 是原弱 H² jet 一阶截断减去同一节点 Sobolev jet，返回完整弱 H¹ jet。 |
| 3 | `SimplicialPartition.nodalH2ErrorJet_value` | `H2NodalErrorJet.lean:33` | PASS；原 L² 类中严格等于 value u−nodalLp f，减法方向正确。 |
| 4 | `SimplicialPartition.nodalH2ErrorJet_mem_dirichlet` | `H2NodalErrorJet.lean:40` | PASS；原 H¹₀ 成员的截断及节点 jet 的 H¹₀ 成员经真实子空间减法给出误差成员。 |
| 5 | `SimplicialPartition.nodalH2ErrorJet_value_on_cell` | `H2NodalErrorJet.lean:51` | PASS；在真实闭单元受限 Lebesgue 测度下，误差值 a.e. 等于 f−同一局部节点仿射多项式。 |
| 6 | `SimplicialPartition.nodalH2ErrorJet_gradient_on_cell` | `H2NodalErrorJet.lean:66` | PASS；整个一阶 DerivativeFiber 等于原真实弱梯度减局部仿射函数的真实导数纤维，无候选梯度输入。 |
| 7 | `SimplicialPartition.nodalH2ErrorJet_cell_integral_bounds` | `H2NodalCellError.lean:13` | PASS；把已证局部分析界严格转为原误差 jet 的平方积分，右侧保留同一闭单元的原 field₂ 能量。 |
| 8 | `SimplicialPartition.exists_weak_h2_conforming_nodal_error` | `WeakH2ConformingNodal.lean:14` | PASS；对任意原弱 H²∩H¹₀ 内部供应同一 f、完整 conforming 成员和真实 H¹₀ 误差 e，然后同时覆盖全部单元和合法形状尺度。 |

## 原全部状态、同一代表与真实有限元空间

最终输入是任意 `WeakSobolevJet d 2 (volume.restrict S) S` 和 `value u ∈ dirichletSubspace S`，不是光滑数据子空间。该 jet 的每阶字段均为真实 L² 类，具有原全部 SpatialTest 的相邻阶弱导数身份。`dirichletJetSpace S` 是原紧支光滑测试 jet 的线性张成在完整 H¹ 图拓扑中的闭包；`dirichletSubspace S` 是其真实 value 映像，并非将点态边界零值作为定义。

最终证明调用 C138 的 `exists_dirichlet_closure_representative`，从上述原状态、开凸有界域及 d≤3，内部得到同一个全空间函数 f：在 closure S 上连续，与 value u 在 S 上 a.e. 相等，且对每个 x∈frontier S 有 f(x)=0。已直接复核 `DirichletContinuousBoundary`：该边界结论来自原 H¹₀ 零延拓的全部弱导数、真实弱链式法则和每个边界点内外开集上的正测度矛盾；没有假定原函数点态边界值或光滑代表。最终只把已经证明的全边界零值用于各边界顶点，不另选第二个代表。

已展开 `SimplicialPartition`、`FaceMatching` 和 `BoundaryFitted`。分区由真实非退化 d-simplex 构成，闭单元包含于 closure S、覆盖 S、内部两两不交。FaceMatching 要求公共部分由公共顶点的凸包生成，BoundaryFitted 要求单元边界部分由其实际边界顶点生成；它们是原 conforming、边界贴合网格的几何条件，没有把目标插值资格或误差估计藏入结构。

`localNodal f i` 是真实 AffineBasis 节点仿射插值；公共面上的一致性来自同一节点值和仿射再现，得到原 `nodalFunction`，其真实 L² 类为 `nodalLp`。`conformingSpace (dirichletSubspace S)` 展开为真实逐片仿射 L² 空间与原 H¹₀ 值空间的交。其成员刻画使用每个单元上的实际仿射多项式 a.e. 身份，未将原 Vh 替换为一个额外指定的较小节点子空间。

已复核 C060 的 `nodalLp_mem_dirichletConformingSpace` 和其 H¹₀ 来源：零边界节点函数的连续零延拓具有真实弱 jet；内缩给严格域内紧支，再经真实光滑卷积强 H¹ 逼近和原图闭包闭性得到 H¹₀。该证明不是从边界点态零值直接宣称 H¹₀。最终同一个 nodalLp 的逐片仿射成员与 H¹₀ 成员组成上述完整交空间成员。

## 真实误差 jet、弱导数唯一性与闭单元测度

误差 def 严格为 `truncate (1≤2) u − M.nodalSobolevJet … f hf`。`truncate` 保留原零阶和一阶 L² 字段及其全部弱身份；`nodalSobolevJet` 使用真实节点值类、真实节点导数类和完整弱导数证明。减法在原 WeakSobolevJet 子空间中进行，因此 e 从定义起就是真正的弱 H¹ 状态，而不是预先选一个值类再随意附加梯度。

`mem_dirichletJetSpace_iff` 已直接读取：反向由已有 H¹₀ jet v 的 value 与当前 jet 相等，再用开域上的完整 `WeakSobolevJet.value_injective` 识别二者。故第1项可从同一 nodalLp 的成员资格推得节点 jet 的 H¹₀ 成员；第4项同理把原 u 的 H¹₀ 值成员传给其一阶截断，再作原闭子空间中的减法。这里没有把标量 L² 拓扑闭性冒充 H¹ 图拓扑闭性，也没有附加任意代表的正则性。

闭单元 K 可能包含 ∂S，证明没有使用错误的 K⊆S。已直接读取 `SimplicialLocalGradient`：真实单纯形边界零测给 K 与 interior K 在 volume 下 a.e. 相同；开凸 S 的 interior(closure S)=S 和 M.inside 给 interior K⊆S，故 `volume.restrict K ≤ volume.restrict S`。空域分支单独处理。所有原域 L² 代表身份、Lp 减法 a.e. 身份、节点类 a.e. 身份均通过这个真实测度比较传至闭单元。

第5项因此得到 value e=f−localNodal f i 的闭单元 a.e. 身份。第6项先将真实节点弱 jet 限制到 interior K，用全部弱测试的导数唯一性识别其梯度为实际局部仿射函数的 fderiv，再利用 K 与 interior K 的测度一致返回闭单元。已读取 `AffineWeakGradient`：每个坐标方向由完整弱身份和仿射函数的真实 Lipschitz 导数确定，最后经 `Sym.oneEquiv` 覆盖整个一阶纤维；没有遗漏坐标或只取部分梯度。

随后 field 的线性性和原 L² 减法给 `field₁ e = field₁ u − derivativeOneFiber(affineScalarDerivative(localNodal f i))`。局部仿射导数恰为实际 fderiv，减法方向与 e 的 value 身份一致。第6项作为代数性身份本身不要求 f 表示 u；第7、8项在使用真实误差估计时明确提供同一个 f 的 a.e. 原值身份，未漏接这一条件。

## 同单元原 Hessian、可积性和统一常数

第7项使用 C135/C136 已证明的原弱 H² 局部值、全梯度界。将记号写为 K=M.cell i、C_d=tensorCoordinateBound d 2、E_K=∫K‖field₂u‖²，实际输出为

\[
\int_K |\operatorname{value}e|^2\le 16D^4 C_d^2d^2 E_K,
\]
\[
\int_K\|\operatorname{field}_1e\|^2\le
\bigl(2^d d+128\kappa^2\|\operatorname{derivativeOneFiber}_d\|^2\bigr)D^2 C_d^2d^2 E_K.
\]

这里 C_d 是固定维数二阶张量重构常数，d² 来自全部有序二阶坐标的实际计数；一阶纤维范数是原全部梯度的真实 Euclidean 范数。局部分析的有限维节点导数连续性仅用于传递极限，未将依赖单元的算子范数放入统一误差常数。继承的局部界适用于原全部弱 H² 状态及其真实闭包连续代表，没有光滑、近似序列、节点收敛或目标误差前提。

该批把 C135/C136 中零延拓字段的表达式精确改写为原域字段：`zeroExtendLp_ae_restrict` 先在 S 上给真实 a.e. 相等，再由闭单元测度比较传至 K。`integral_congr_ae` 得到原 Hessian 能量以及值、完整梯度误差积分的三条精确等式，代入原局部界后不新增三角不等式损失。零延拓仅用于代表识别，未声称一般 H² 状态的零延拓具有全空间 H² 正则性。

相关平方积分均真实可积：原 u、e 各字段是 L²，受限测度被原域测度控制，故闭单元限制仍为 L²；真实仿射导数是常数，闭单元紧且测度有限。f 与局部多项式之差通过已证 a.e. 身份对应同一 L² 误差类。证明不依赖不可积积分的默认零值，也没有把右侧替换为全域、扩大邻域或另一个候选 Hessian。

几何输入仅为 r>0、D≥0、真实 B(a,r)⊆K、D≤κr 及 K 中任意两点距离≤D。κ 无须另加符号条件，因为这些前提已蕴含 κ≥0。D 可取原 h_K；d≥1 的非退化单元有正直径，d=0 与 D=0 仍由已证明的完整类型覆盖，未除以 d 或 D。原 d=2、3 时这些显式系数为正，并只依赖维数和形状常数。

## 最终量词、额外实例和范围边界

最终第8项按顺序选择一个 f，再选择实际 e，随后才量化所有 i、a、r、D、κ 及其合法几何条件。f、同一个节点 L² 类和 e 不随单元或形状尺度重新选择。常数公式不含 S、网格数目、状态或代表；本批没有时间权参数，也未借节点函数成员资格所需的个别 Lipschitz 常数产生误差常数。

最终输入保留 `[IsFiniteMeasure (volume.restrict S)]` 类型类实例。本批没有在结论内部自动构造该实例，不能把这一实际类型参数省略不报；但原 hb:IsBounded S 已由 Euclidean 空间的 `Bornology.IsBounded.measure_lt_top` 推出 volume S<∞，从而供应它。另有限紧单元覆盖也给 closure S 紧。因此它是可由原几何条件清偿的接口实例，不是额外实质数学假设。原论文的有界凸多面体、d∈{2,3}、conforming 形状正则网格均满足本辅助结论的公开条件。

空域时连续代表与边界结论来自已处理空域的 C134/C138，实际 nodalLp 的 H¹₀ 成员来自 C060 的空域零类分支；非退化单元不能包含于空闭包，故全部单元估计无伪造中心。结论不另要求 S 或索引类型非空。f 在 closure S 之外的取值未被约束，也不被用来读取任意 Lp 类的点值。

本批清偿 P1 Step 2 的真实节点资格、同一 H¹₀ 误差和原无权局部 h_K²/h_K 阶界。原 `eq:p1-interpolation` 与 `eq:p1-interpolation-energy` 还需要实际允许权比较、全域求和和网格尺度；随后还要与原 L² 投影及数值接口组合。本报告不把这些后续结论、完整 prop:p1 或 P011 宣称完成，C139 保持 AUXILIARY，原文仍为14/26。

## 固定依赖、构建和公理

依赖验收门槛已通过并核对正确调用：[C138 / T122](T122-local-acceptance.md) 供应原全部弱 H²∩H¹₀ 的同一闭包连续边界零代表；[C136 / T120](T120-local-acceptance.md) 及其 C135 依赖供应同单元真实弱值和全梯度界；[C060 / T044](T044-local-acceptance.md) 供应同一节点插值的实际 H¹₀ 和完整 conforming 成员。本次另直接读取其关键源码、原 Dirichlet 空间与弱导数唯一性、SobolevTruncation、节点弱 jet、局部仿射梯度识别，未仅引用 PASS 标签。

三新模块的 Carleman 导入闭包共207模块，其中204旧模块与 base 逐字节不变。C138 `DirichletContinuousBoundary` 的173模块闭包相对 base 不变；C136 `WeakH2NodalGradient` 的180模块闭包相对 `a26158d00376e85866c536aa366239af41c83f97` 不变；C060 `NodalDirichletMembership` 的113模块闭包相对 `50ea3111057c5d7b796cca799c10a9a900d14caf` 不变。没有混用未经复审的旧依赖版本。

原稿和已读治理协议自 T120 不变，原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean固定4.35.0，mathlib pin及本机实际干净HEAD为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。固定root显式导入全部3模块；固定 CheckAxioms 对8项分别输出完整类型与公理，再通过 privateToUserName 和递归 collectAxioms 审计全部 Carleman 声明，只允许三项标准基础公理。

实际读取固定 `/tmp/carleman-weak-conforming-target.log` 的3385 jobs成功记录和 `-full.log` 的3879 jobs成功记录，后者末行为6727声明递归审计PASS。固定本机 `-local-axioms.txt` 为 **2,048,003 bytes**，SHA256 **`96644cbd6bedaa524424eb33abbd3c3e8c73062b4515ea547d5382f9f7707a8b`**。全部8项的实际展开类型已逐项核对，均仅依赖 `propext`、`Classical.choice`、`Quot.sound`；全文2339条非空及8条无公理记录未发现其他公理。新增源码无 sorry/admit/新增 axiom。

## 同 SHA 正式 CI 与独立下载的原始产物

本 Agent 经 GitHub connector 自行查询 [main CI 39206744043 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39206744043/attempts/1)。实际run为main/push，head SHA精确匹配，最终completed/success，updated_at为 `2026-10-19T05:56:38Z`。三job全部completed/success：lean **117911132282**、state-check **117911132515**、dashboard / snapshot **117912272251**。Lean的pin、证明构建、结果记录和两份证据保存步骤均成功；未因产物提前可下载便假定job已完成。

同run原始artifact：`lean-ci-result` **12165742507**，压缩产物492 bytes，digest `sha256:4fcbf2d5c7c120d23eda9e361197ca6deba319a4d1a7279274ac9045ad1f2e4e`；`lean-declaration-evidence` **12165682696**，压缩产物187911 bytes，digest `sha256:99c6e0a17d43f654af11a241058c01a3ffee319aa24d6a60ba0fcb7de99cfc7f`。两份workflow_run元数据均绑定上述run、main和精确SHA。本 Agent 自行用 `gh run download 39206744043` 下载至约定的 `-main-ci` 和 `-main-axioms` 目录。

实际 `/tmp/carleman-weak-conforming-main-ci/result.json` 为 **PASS**，`checked_sha=source_head_sha=e56df9d1895554e8cdfacc7e52c86bac51a08e6c`，targets为Carleman，`finished_at=2026-10-19T05:54:51.147742+00:00`，ci_url为上述run/attempt。Lean提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib为上述pin。解压result为537 bytes，SHA256 `b134df15007e89cbe465637f39ff659331e94243a2bb5d9c54741bdb0faa13aa`。

独立逐字节比较实际远端 `/tmp/carleman-weak-conforming-main-axioms/axioms.txt` 与固定本机副本，完全一致：**2,048,003 bytes**、SHA256 **`96644cbd6bedaa524424eb33abbd3c3e8c73062b4515ea547d5382f9f7707a8b`**，末行实际为 **6727项全声明递归审计PASS**。8项声明的完整类型和三项基础公理均在此同版本原始文件中；没有引用其他SHA或后续工作树的公理产物。

## 验收决定

**C139：PASS，可升级为REVIEWED，scope保持AUXILIARY。** 8项声明未发现需修复的数学缺陷。全部原弱 H²∩H¹₀、同一边界零代表、原完整 conforming 空间成员、真实 H¹₀ 误差 jet、闭单元 a.e. 身份、全梯度和同单元原 Hessian 能量，以及 f/e 在全部单元和尺度之前的量词均已核实；同SHA三项正式CI和自行下载的原始公理证据一致。

P011不提升，原文保持 **14/26**。本次仅新增本报告，未修改实现、台账、原稿或root导入，未commit/push。签发UTC如上固定；最终核对并通知主Agent后冻结本报告内容和时间戳。
