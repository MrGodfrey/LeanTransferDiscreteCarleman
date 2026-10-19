# T093 / C109 独立本机验收

- `checked_sha`: `ba9aa5d2a3caf655bba037695fe733a3f292d952`
- `base_commit`: `1c3da9ffc54b5624f27760db5368aa05cbdfc0a5`
- `reviewed_at`: `2026-10-19T01:55:44+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**（固定本机与同次远端原始产物逐字节一致）
- `scope`: **AUXILIARY**
- 范围：原真实 Q_h=R_hJ_h 的局部 L² 稳定性与局部性，实际裁剪开盒宽度、重数和活动帽非零支撑包含。具体块采用明确加宽后裁剪的证明路线，未声称等于原最小 B_K；完整 B.2/FD 未完成，原文保持 **13/26**。

独立以 `git show` 读取固定四模块全部证明、22项实际展开类型与关键依赖，对照原 `paper/main.tex` Section 6 的 R_h、J_h、Q_h 定义及 Appendix B 的 `eq:fd-projection-stability`（TeX2783–2789）和局部到全域 B.2 证明（TeX2854–2869）。执行者规格及 CI 不替代语义核对；后续工作树不属于本次范围。

## 全部22项声明

名称省略公共前缀 `Carleman.`；位置以固定 `Carleman/` 为根，顺序与交付清单及固定 C109/T093 台账一致。

| # | 声明 | 固定位置 | 独立结论 |
|---|---|---|---|
| 1 | `cartesianKuhnMoment_local_integral` | `Spatial/CartesianKuhnMomentBounds.lean:14` | PASS；实际帽函数在 Ω\B 为零，将原归一化矩精确限制到任意实际支撑容纳集 B⊆Ω。 |
| 2 | `cartesianKuhnMoment_local_sq_bound` | `Spatial/CartesianKuhnMomentBounds.lean:31` | PASS；真实质量、0≤φ≤1和实际 L² Cauchy–Schwarz 给 ω\|(J_hu)_a\|²≤∫B\|u\|²。 |
| 3 | `cartesianKuhnMoment_local_congr` | `Spatial/CartesianKuhnMomentBounds.lean:65` | PASS；两个原 L² 状态仅在 B 上 a.e. 相同，就有该实际节点矩相同。 |
| 4 | `cartesianKuhnProjection` | `Spatial/CartesianKuhnProjection.lean:14` | PASS；定义严格为真实有限帽和 R_h 与原归一化矩 J_h 的复合。 |
| 5 | `cartesianKuhnProjectionLp` | `Spatial/CartesianKuhnProjection.lean:20` | PASS；同一重构的真实原域 L² 类；没有另换投影算子。 |
| 6 | `cartesianKuhn_cell_volume_le` | `Spatial/CartesianKuhnProjection.lean:26` | PASS；真实单元平移体积与整个单盒的排列体积和给 \|K\|≤ω。 |
| 7 | `cartesianKuhnProjection_local_sq_bound` | `Spatial/CartesianKuhnProjection.lean:35` | PASS；实际局部 P1 质量界、活动节点矩界及 d+1 顶点求和抵消，得到常数1的真平方积分界。 |
| 8 | `cartesianKuhnProjection_local_congr` | `Spatial/CartesianKuhnProjection.lean:81` | PASS；活动节点矩相同、非活动帽在整个闭单元为零，得到 K 上逐点 Q_h 一致。 |
| 9 | `cartesianKuhnProjection_local_norm_bound` | `Spatial/CartesianKuhnProjection.lean:99` | PASS；两边真实 MemLp 资格及平方积分身份给实际局部 L² 范数界。 |
| 10 | `cartesianClippedPatchLower` | `Geometry/CartesianClippedPatch.lean:12` | PASS；具体裁剪下端点为原域下端点与半径2格点块下端点的 max。 |
| 11 | `cartesianClippedPatchUpper` | `Geometry/CartesianClippedPatch.lean:15` | PASS；具体裁剪上端点为原域上端点与半径2格点块上端点的 min。 |
| 12 | `cartesianClippedPatch` | `Geometry/CartesianClippedPatch.lean:18` | PASS；实际集合为 Ω 与以单元整数原点为中心的半径2开格点块之交。 |
| 13 | `cartesianClippedPatch_eq_box` | `Geometry/CartesianClippedPatch.lean:23` | PASS；逐坐标 max/min 的严格不等式给精确开盒等式。 |
| 14 | `cartesianClippedPatch_width_bounds` | `Geometry/CartesianClippedPatch.lean:39` | PASS；合法有限格点包含自身一个网格盒，故各轴宽度在 δ_j 与5δ_j之间。 |
| 15 | `cartesianClippedPatch_isOpen` | `Geometry/CartesianClippedPatch.lean:53` | PASS；两个实际开盒相交仍开，没有闭盒替代。 |
| 16 | `cartesianClippedPatch_subset_domain` | `Geometry/CartesianClippedPatch.lean:57` | PASS；实际裁剪集合确实包含于原物理开域。 |
| 17 | `cartesianClippedPatch_contains_cell` | `Geometry/CartesianClippedPatch.lean:60` | PASS；整个单元与 Ω 的交集包含于该开邻域，未错误包括物理边界点。 |
| 18 | `cartesianClippedPatch_multiplicity_le` | `Geometry/CartesianClippedPatch.lean:68` | PASS；真实有限格点／排列索引注入、floor 窗口计数给全部点的重数≤5^d d!。 |
| 19 | `cartesianKuhnHat_support_subset_clippedPatch` | `Spatial/CartesianKuhnPatchProjection.lean:13` | PASS；活动内部帽的真实非零支撑属于 Ω，并经节点星进入半径2格点块，内部清偿支撑前提。 |
| 20 | `cartesianKuhnProjection_patch_sq_bound` | `Spatial/CartesianKuhnPatchProjection.lean:25` | PASS；对全部原 L² 状态和全部实际单元，无外留支撑条件的具体邻域平方积分界。 |
| 21 | `cartesianKuhnProjection_patch_norm_bound` | `Spatial/CartesianKuhnPatchProjection.lean:34` | PASS；同一具体裁剪邻域上的真实 L² 范数界，常数严格为1。 |
| 22 | `cartesianKuhnProjection_patch_congr` | `Spatial/CartesianKuhnPatchProjection.lean:44` | PASS；具体邻域上的 a.e. 数据一致推出整个闭单元上实际 Q_h 逐点一致。 |

## 原算子、全部状态与真实局部矩

新 `cartesianKuhnProjection` 严格定义为 `cartesianKuhnReconstruction … (cartesianKuhnMoment … u)`。已直接读取两个依赖：R_hf=Σ_a f_aφ_a 是完整内部索引上的真实有限帽函数和；(J_hu)_a=ω⁻¹∫Ωuφ_a，ω=∏δ_j，是原物理质量归一化的真实积分。输入 u 是全部原域 `Lp ℝ 2`，未要求 H¹/H²、连续代表、节点值或光滑性。新 Lp 对象就是该同一重构的真实 L² 类，旧 `cartesianKuhnReconstructionLp_ae` 给相同点态函数的 a.e. 代表身份。

这里的“Projection”名称对应原 Q_h=R_hJ_h；没有额外假设 Q_h²=Q_h，也没有换成 L² 正交投影。J_h 使用原帽函数而非由稳定性目标反向定义的对偶测试。

一般局部矩声明只要求 B⊆Ω 且 `Function.support φ_a⊆B`。于是 Ω\B 上 φ_a=0，从真实积分去掉该部分，准确得到原矩等于 ω⁻¹∫B uφ_a。实际 mathlib `setIntegral_eq_of_subset_of_forall_sdiff_eq_zero` 已读取：只需外层 Ω 可测，内层 B 无须另添可测性；这里的 Ω 是实际开盒。具体应用中的 B 自身已证明为开盒。这个接口没有假设目标局部估计，B 也不必等于整个 Ω。

u 在 B 上的 L² 资格由 B⊆Ω 的测度单调性给出。φ_a 在 B 上的 L² 资格来自真实帽函数 Lp 类及其 a.e. 身份，而其 L¹ 资格来自实际连续紧支内部帽函数。由全空间点态0≤φ_a≤1，真实积分单调性给

\[
\int_B\phi_a^2\le\int_B\phi_a\le\int_\Omega\phi_a=\omega.
\]

各积分在相应测度下真正可积；没有依赖总化积分的不可积分支。实际 `integral_mul_sq_le` 用两个 MemLp.toLp 的 a.e. 身份把积分识别为真实 Hilbert L² 内积，再用 Cauchy–Schwarz，得到 `(∫B uφ_a)²≤(∫B u²)ω`。ω>0 由各正步长内部供应，归一化后恰为 `ω|(J_hu)_a|²≤∫B u²`，没有少乘或多乘 ω。相同局部积分身份和积分 a.e. 同余也给出局部矩一致性。

## 常数1及单元顶点数的准确抵消

对真实单元 K 的每个实际顶点 v_k，局部重构系数是 `c_k=cartesianInteriorData (J_hu)(v_k)`。若它等于一个原内部节点，实际节点映射单射与节点数据恢复给 c_k=(J_hu)_a，并使用该活动节点的支撑前提供应局部矩界。若不存在这样的内部节点，原有限 Kronecker 和每项均为零，c_k=0；不要求边界节点有额外数据。任意混合符号系数均允许。

因此对 k=0,…,d 的每个系数都有 ωc_k²≤I_B，其中 I_B=∫B u²≥0。这里只在单个单元的 d+1 个顶点上求和，给 ωΣ_kc_k²≤(d+1)I_B，绝未在全网格内部节点集上作这一上界求和。

此次读取的实际局部 P1 质量界给 `∫K(R_hJ_hu)²≤|K|/(d+1) Σ_kc_k²`；其证明把原闭单元上的真实重构精确识别为原节点仿射插值，再调用真实单纯形质量积分。新体积界 `|K|≤ω` 来自同排列单元的真实平移不变性，以及全部排列的非负单元体积之和等于一个实际格点盒体积 ω；不需要未证的每个单元体积等于 ω/d!。

于是逐步得到

\[
\int_K|Q_hu|^2
\le\frac{|K|}{d+1}\sum_{k=0}^d c_k^2
\le\frac{|K|}{\omega}I_B
\le I_B.
\]

d+1 和 ω 的消去合法，体积非负及 I_B 非负也已供应。最终常数严格为1，不依赖 d、N、网格总节点数、平移、步长、长宽比、单元、B 或状态。没有把某个固定网格上的有限维范数等价常数冒充统一常数。

范数版本先证明实际点态 Q_h 在该单元上 MemLp（由真实连续紧支重构的全空间 MemLp 限制），u 在 B 上 MemLp，然后使用真实平方积分与 `bochnerL2Norm` 平方身份。该范数在 MemLp 条件下正是 L² 范数，不存在无穷 eLpNorm 取 toReal 后塌成零的问题。两边非负后从平方不等式得到原范数不等式。

## 局部 a.e. 数据与 K 上逐点一致

若两个原 L² 状态仅在 B 上 a.e. 相同，每个活动内部节点的实际矩通过局部矩同余相等。对非活动节点，真实帽函数在整个闭单元 K 上恒零。把有限帽和逐项比较，得到对所有 x∈K 的点态 `Q_hu(x)=Q_hv(x)`，包括单元面和边。

这不是从 u、v 的 a.e. 相同直接推断其逐点相同；先比较真实积分系数，再使用确定的连续分片仿射输出。输入仍为原等价类，不使用任何输入节点求值或额外正则性。新的具体邻域局部性定理保留同样量词。

## 裁剪开盒、边界和实际重数

对有限单元索引 i 的整数格点原点 z，具体块是

\[
B_i=\Omega\cap\prod_j(o_j+(z_j-2)\delta_j,\ o_j+(z_j+3)\delta_j).
\]

`cartesianClippedPatch_eq_box` 按坐标的严格不等式证明它恰等于下端点 max(o_j,o_j+(z_j−2)δ_j)、上端点 min(o_j+N_jδ_j,o_j+(z_j+3)δ_j) 的实际开盒。没有把开区间改为闭区间，也没有假设块完全位于物理域内再忽略裁剪。

有限格点合法性给0≤z_j及 z_j+1≤N_j，正 δ_j 保证裁剪下端点不大于自身网格盒下端点，上端点不小于自身网格盒上端点。因此宽度至少 δ_j；它又不超过未裁剪宽度5δ_j。证明包括第一格点盒、最后格点盒以及 N_j=1 时整轴只剩一个网格步长的情形。新包含结论是 `K∩Ω⊆B_i`，未错误声称开 B_i 包含 K 上的物理边界点；闭单元边界对原 L² 积分的零测处理沿用实际分区依赖。

重数使用实际有限格点／排列索引到整数格点×Perm(Fin d) 的注入。已读取原 floor 窗口证明：若 x 属于一个半径2开块，则每个 z_j 在归一化坐标 floor 周围[−2,2]的5项整数窗口内；坐标函数积有5^d项，全部排列有 d!项。裁剪仅减小集合，所以对全部 x 的真实 `finiteCoverMultiplicity` 得到 `≤5^d d!`，没有依赖网格总范围或丢失边界点。无需再乘 d+1 的活动顶点数。

新活动帽支撑证明严格区分 `Function.support` 与 `tsupport`。帽函数非零则由内部节点零延拓定理必在 Ω；另一方面非零点属于其拓扑支撑，已验收的实际节点星／共享顶点星包含将其送入半径2开块。两者组合给非零支撑⊆B_i，恰为一般局部定理所需。第一层内部帽的拓扑支撑可能触及物理边界，不能声称整个 tsupport⊆这个裁剪开盒；代码和结论均没有这一错误。

d>0且某 N_j=0 时没有单元索引，关于 i 的结论为空量化；N_j=1 时可能有单元但内部节点空间为空，Q_h恒零，局部界仍成立。d=0时唯一点、唯一标签与空坐标约束保留，重数5^0·0!=1，宽度语句空量化。原 d≥1、N_j≥2 的全部网格均包含。

## 原最小 B_K 与当前证明路线

原 TeX2789 选择包含 K 和活动支撑的最小轴平行矩形块。当前具体 B_i 是固定半径2加宽后与 Ω 相交的开矩形；代码未证明、也未宣称它等于原最小 B_K。规格明确记载这一差别，符合项目允许保持最终结论的证明路线调整。

一般局部定理仍保留任意 B⊆Ω，只要活动非零支撑被容纳，故没有把原局部现象缩成只对全域 Ω 成立。具体加宽块的宽度在 δ_j和5δ_j之间；在原各轴步长可比前提下，这些明确几何事实提供后续所需的 O(h) 尺寸与统一长宽比来源，而实际重叠常数已证明。当前登记的正式几何声明是逐坐标宽度和重数，不另冒称所有后续尺度／边界仿射接口已完成。

原 B.2 还需局部仿射再现、实际弱梯度误差与逆界组合、允许权在块上的统一比较和全域求和。新定理只供应实际 Q_h 的局部 L² 稳定性和局部作用；它没有证明这些余项，也没有把局部界冒称为完整 B.2 或完整 FD。原文仍13/26，P012/P026不提升。

## 固定依赖和本机构建

四新模块 Carleman 导入闭包共186模块，其中182旧模块相对基线逐字不变。另递归比较关键已验收版本：CartesianKuhnLpNorm 的182模块闭包与 [T091](T091-local-acceptance.md) 固定 `c5ac12749281c37710ade58c454fe9945273c7ec` 一致；CartesianKuhnLoadLift 的177模块闭包与 [T090](T090-local-acceptance.md) 固定 `340cab6232ac4c81515d19b523fec6e7a031df75` 一致；CartesianKuhnHatSupport 的140模块闭包与 [T087](T087-local-acceptance.md) 固定 `7b2627620e04ad9b44e6bee31fab8a241d4f4d1a` 一致；CartesianPatchOverlap 的87模块闭包与 [T084](T084-local-acceptance.md) 固定 `d8ccc85628961e226550d9fea095eac9710ed969` 一致。本次另直接读取真实重构、局部质量上界、L²积分／Cauchy–Schwarz、实际块计数，以及所用 mathlib 集积分限制定理，核实实际调用条件。

实际 `/tmp/carleman-kuhn-projection-target.log` 为3361 jobs成功，随后 `/tmp/carleman-kuhn-patch-projection-target.log` 为完整定向3363 jobs成功；`/tmp/carleman-kuhn-local-projection-full.log` 为3780 jobs成功，并实际记录 `Axiom audit passed for all 6104 Carleman declarations.`。固定 `/tmp/carleman-kuhn-local-projection-local-axioms.txt` 为 **1,799,120 bytes**，SHA256 **`f9e78b8ffbc60d8e8b21093c62c61b04866d63cfa70069fd65fe389b5653dbcf`**。

22/22项完整展开类型与源码相符，每项各有一条公理记录，均只依赖 `propext`、`Classical.choice`、`Quot.sound` 的子集。全文件1998条显式记录中1992条列出基础公理、6条无公理，共1994个不同声明，无白名单外公理或 sorryAx。递归审计涵盖生成辅助声明。新模块无 sorry/admit/axiom/unsafe，root 明确导入四模块，CheckAxioms 只增22项 #check/#print，原审计未削弱；清单与固定 C109/T093 台账一致。

原稿、已读 AGENTS／治理协议、工具链 pin 与 CI 工作流相对基线不变。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`；Lean 4.35.0，mathlib 实际 HEAD 为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且工作树干净。

## 同 SHA 远端证据

已独立通过 GitHub API 核实 [main CI 39187182886 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39187182886/attempts/1)：main/push，head SHA 精确为固定证明版本，run completed/success。state-check `117851959993`（01:50:48Z）、lean `117851960267`（01:53:24Z）、dashboard / snapshot `117852559723`（01:53:37Z）均绑定同 SHA，全部 completed/success。

实际 artifact 元数据确认 `lean-ci-result`（`12158527666`）和 `lean-declaration-evidence`（`12158756794`）属于同 run、main 分支及固定 head SHA，均未过期。独立读取 `/tmp/carleman-kuhn-local-projection-main-ci/result.json`：status=PASS，checked_sha=source_head_sha=`ba9aa5d2a3caf655bba037695fe733a3f292d952`，finished_at=`2026-10-19T01:52:27.801108+00:00`，targets 为 Carleman，ci_url 对应上述 run/attempt；实际 Lean 4.35.0 与 mathlib pin 一致。

已独立将 `/tmp/carleman-kuhn-local-projection-main-axioms/axioms.txt` 与固定本机副本逐字节比较，完全相同：**1,799,120 bytes**，SHA256 **`f9e78b8ffbc60d8e8b21093c62c61b04866d63cfa70069fd65fe389b5653dbcf`**。远端22/22项完整类型及各自公理记录逐名核对通过，全部1998条显式记录重新扫描无非基础公理；末行确认全部 **6104** 声明递归审计通过。未使用其他 SHA 或后续工作树构建替代本次证据。

## 验收决定

**C109：PASS，可按 AUXILIARY 升为 REVIEWED。** 22项语义核对未发现真实 Q_h、完整 L² 状态、局部可积性、质量与常数1、非零支撑、边界裁剪、宽度、重数或局部性方面的缺陷。同 SHA 三项最终 CI 与原始产物已独立核实。具体加宽裁剪块与原最小 B_K 的区别如上记录，不提升完整 B.2/P026、FD/P012 或其他未完成原文命题，原文仍 **13/26**。

本次仅写本报告，未改实现、台账、root 或原稿，未 commit/push。范围保持 AUXILIARY，原文保持13/26。
