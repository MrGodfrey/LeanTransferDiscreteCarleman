# T138 / C154 独立本机验收

- `checked_sha`: `d1dca8884990c684f923a4938e40a6cc88e1645f`
- `base_commit`: `ac30cc21022f162809fdd7f88550a3fd58e5ad35`
- `reviewed_at`: `2026-10-19T08:19:51+00:00`
- `reviewer`: `/root/accept_spatial_lemma`
- `result`: **PASS**；`axiom_check`: **PASS**。
- `scope`: **AUXILIARY**。C154 可登记为 REVIEWED；不提升 P023 或其他 PAPER，固定台账已有的原文完成数 **16/26** 保持不变。

本 Agent 从固定 Git 对象直接读取三模块全部证明、十项实际展开类型、分析/MATH_SPEC/台账、原论文和关键依赖，另独立核实同 SHA 三项正式 CI、自行下载同 run 原始结果与公理文本。执行者说明、旧验收标签及 CI 未替代语义审查；后续工作树与动态 `.ci/axioms.txt` 不属于本批证据。

## 全部十项声明

下表省略公共前缀 `Carleman.`，固定源码以 `Carleman/Spatial/` 为根。顺序与 `/tmp/carleman-t138-boundary-declarations.json`、modules JSON及固定 C154/T138 精确对应。

| # | 声明 | 固定源码位置 | 独立结论 |
|---|---|---|---|
| 1 | `inward_fderiv_tendsto_of_contDiffAt` | `PiecewiseSmoothContraction.lean:13` | PASS；在实际 C¹ 点，由逆内缩点趋于原点、最终可微性和真实导数连续性得到真实 fderiv 极限。 |
| 2 | `compactLipschitz_inward_tendsto_H1` | `PiecewiseSmoothContraction.lean:30` | PASS；紧支 Lipschitz 且 a.e.C¹ 的实际函数，在共同紧支撑和值/导数界下得到完整弱 H¹ 图拓扑的强收敛。 |
| 3 | `piecewiseSmooth_mem_dirichletJetSpace` | `PiecewiseSmoothContraction.lean:56` | PASS；每个内缩函数支持严格进入域内，由真实卷积逼近取得测试闭包成员，再以完整 H¹ 强极限闭性通过极限。 |
| 4 | `zeroBoundary_indicator_lipschitz` | `ZeroBoundaryIndicator.lean:14` | PASS；边界零值与实际最近边界点给跨边界距离界，indicator 保持同一个 Lipschitz 常数。 |
| 5 | `indicator_tsupport_subset_closure` | `ZeroBoundaryIndicator.lean:36` | PASS；真实拓扑支持包含 closure S，不假设支持已经在 S 内。 |
| 6 | `indicator_hasCompactSupport` | `ZeroBoundaryIndicator.lean:41` | PASS；实际 indicator 的支持包含原函数支持，保留紧支性，无新紧支持输入。 |
| 7 | `indicator_contDiffAt_off_frontier` | `ZeroBoundaryIndicator.lean:49` | PASS；域内局部等于原函数，closure S 外局部等于0；只在边界外证明 C¹。 |
| 8 | `indicator_contDiffAt_ae` | `ZeroBoundaryIndicator.lean:64` | PASS；实际凸集边界的 Lebesgue 零测定理给 a.e.C¹，不假设跨边界可微。 |
| 9 | `smooth_boundary_zero_mem_dirichletJetSpace` | `SmoothBoundaryDirichlet.lean:13` | PASS；任意原 H¹ jet，只要其值 a.e. 为所给全空间光滑边界零函数，即由原值单射识别为构造的原 H¹₀ 极限。 |
| 10 | `smooth_boundary_test_mem_dirichletJetSpace` | `SmoothBoundaryDirichlet.lean:37` | PASS；同一全空间 SpatialTest 的实际完整子域限制满足上项条件，直接得到原 H¹₀ 成员，无另行 H¹/零迹资格输入。 |

## 原文定位和实际前提

已对照固定 `paper/main.tex:2657–2664` 的实际 Dirichlet Laplacian、V=H¹₀ 及 P023 / `prop:analytic-realizations`。原结果仍须证明 H² 算子域识别与椭圆正则估计。T138 提供可用于后续盒面反射弱 Poisson 论证的合法 H¹₀ 测试资格，不是原完整 P023，也不宣称反射后的弱方程、边界 H² 正则性、凸域统一 Hessian 界或连续 CE 已完成。Section6 的原 H¹₀ 变分空间也使用同一闭包对象。

最终第9、10项明确量化任意 d、S 开且凸、有界、**非空**，全空间紧支 C∞ 测试 φ，并要求 φ 在 frontier S 的每一点为0。第9项还输入实际原弱 H¹ jet u 及其 value 与 φ 的 a.e. 等式；第10项直接构造为原 φ.sobolevJet 的实际限制，所以没有要求调用者再提供 u 或它的弱 H¹ 资格。

这些是本辅助引理实际范围：没有把“只在闭域 C∞ 且无全空间延拓”的函数也算入本批，没有将一般 Sobolev 迹零等同于已给点态边界零。相反，φ 的真实全空间紧支光滑性、边界零值都是明确前提。最终不要求 tsupport φ⊆S，不要求法向导数在边界为零；φ 可在域外非零。也未声称最终非空域定理包含空域分支。原物理有界凸域及盒子符合所需非空条件，非空性用于选择实际内缩中心。

第1项不需 Lipschitz 或域假设，只使用指定点 C¹；第2、3项保留 a.e.C¹ 前提，不错误声称任意 Lipschitz 函数的导数沿内缩点逐点收敛。最终 indicator 场景由第7、8项内部供应这项前提。没有预设强 H¹ 收敛、H¹₀ 成员或目标测试闭包。

## 跨边界真实 Lipschitz 与支持

第4项适用于任意集合 S，不需先加开性、凸性或有界性。对 x∈S、y∉S，y 已保证 S≠univ；pinned mathlib 的 `exists_mem_frontier_infDist_compl_eq_dist` 在实际有限维 Euclidean 空间提供 z∈frontier S，使 dist(x,z)=infDist(x,Sᶜ)。因 y∈Sᶜ，dist(x,z)≤dist(x,y)。因此

\[
|f(x)|=|f(x)-f(z)|\le C\,|x-z|\le C\,|x-y|.
\]

源码真实使用 hzero z；同在 S 的情况用原 Lipschitz 界，同在补集时均为0，反向跨界用距离对称性。该结论不是由连续性猜测 Lipschitz，也未使用未经证明的线段首次过界点。最近边界点定理的实际类型和证明已读取，允许 x 本身在边界；此时 hzero 仍合法，距离可为0。

第5项从实际函数支持包含 S 后取闭包，得到 tsupport(S.indicator f)⊆closure S。第6项从 indicator 非零只能发生在 f 非零处，证明原支持包含，再由原紧支性得到紧拓扑支持。这里无需把 φ 的原支持限制在 S，也没有新增零延拓紧支假设。

第7项只在 x∉frontier S 证明局部 C¹。若 x∈S，开性给邻域内 indicator f=f；若 x∉S 且不在边界，则 x∉closure S，closure S 的开补集给邻域内 indicator f=0。第8项实际调用 `Convex.addHaar_frontier volume`。该 pinned 定理对有限维实空间凸集证明 frontier 的 Haar 测度为0，包括低维凸集情形；volume 为原 Lebesgue 测度。因而仅排除真实零测边界，未要求零延拓跨边界 C¹ 或导数连续。

## 内缩的真实导数和强 H¹ 极限

既有 `centeredDilation a r` 是 x↦a+r(x−a) 的实际同胚，反映射为 x↦a+r⁻¹(x−a)。`contractedFunction` 定义为 f 与反映射复合，因此函数支持实际向内缩小。真实支撑等式为 tsupport(f_r)=centeredDilation a r '' tsupport f，未将内缩方向弄反。

序列 r_n=(1+n)/(2+n) 满足 1/2≤r_n<1、r_n>0、r_n→1、r_n⁻¹≤2。对第1项指定的 C¹ 点 x，逆内缩点 a+r_n⁻¹(x−a)→x；ContDiffAt 的局部性质供应这些点处最终可微。实际链式法则给

\[
D f_{r_n}(x)=r_n^{-1}D f\bigl(a+r_n^{-1}(x-a)\bigr)
\]

最终成立，再由 C¹ 点处真实 fderiv 连续性得到导数算子范数收敛至 Df(x)。没有只凭 f 在 x 可微就假设周围导数收敛，也没有微分一个仅在单点成立的等式。

第2项从 f 的真实紧支性和连续性选全局值界 B≥0。各内缩函数沿反映射取值，保留同一 B；Lipschitz 常数为 C‖r_n⁻¹‖≤2C，故真实 fderiv 具有同一算子范数界2C。原函数的导数界 C 也不超过2C。S 有界保证 closure S 实际紧且 Lebesgue 体积有限；凸性、a∈S 和 r_n<1 把原支持 closure S 中的每一点送入 S，因此所有函数及其导数共同支撑在 closure S。

函数逐点收敛由真实连续 f 和逆内缩点极限给出。导数 a.e. 收敛由 hreg 逐点应用第1项给出；每个点的最终指标允许不同，未非法要求一个对全部点统一的指标，也未交换不可数个零测例外。

已读取 `compactLipschitzSobolevJet_tendsto` 与 `lp_two_tendsto_of_bounded_support`：对真实标量 L² 类及 CLM 值导数 L² 类分别使用平方差的可积控制函数 `(closure S).indicator ((2B)²)`、相应导数界，再由原 L² 范数平方=真实积分得到**强**收敛。各 n 的 a.e. 代表一致性通过可数 `ae_all_iff` 处理。随后实际连续的0阶/1阶字段装配得到整个弱 H¹ jet 图拓扑的收敛，并非只收敛数值范数或值字段。

`compactLipschitzSobolevJet` 本身由真实 Rademacher a.e. 可微性、实际 fderiv 的 MemLp 资格和完整原弱分部积分构造。非可微点的 fderiv 默认值不会替代弱导数证明；相关等式在实际 a.e. 可微集合上建立。该拓扑包括值和全部一阶分量，正是原 H¹₀ 定义使用的图拓扑。

## 严格域内测试逼近及原闭包

第3项并不假设每个内缩函数光滑。实际支撑严格位于开 S 且紧，于是 `compactLipschitz_mem_dirichletJetSpace` 从紧支撑与开域选正距离缓冲。对这个固定内缩函数，真实非负单位光滑核的半径趋于0，所有充分小的卷积支持位于 S；构造的每个 φ_n 满足原 SpatialTest 的全部字段。

既有实际卷积分析给真实 fderiv 卷积身份及完整 H¹ 强逼近，`restrictedJet_eq_test` 用原值单射将卷积的实际弱 jet 精确识别为该原测试 jet。故每个内缩函数的域限制确实属于由全部原 SpatialTest 张成空间取闭包得到的 dirichletJetSpace。

内缩序列的全空间强 H¹ 极限经真实 L² 字段限制连续性传到域内。`Submodule.isClosed_topologicalClosure` 再把成员资格传给极限。这里是两次真实闭包论证：先固定内缩函数做光滑卷积，再让内缩参数趋于1；不需要额外假设一个统一卷积半径，也没有直接把支持可触边界的原函数当成 SpatialTest S。

本次实际读取 `CompactConvolutionDerivative`：卷积导数为真实 CLM 值 fderiv 的卷积，证明经原弱链及可积向量值积分，而非代设梯度。`CompactMollificationLimit` 的 a.e. 导数逼近和 L² 控制给原完整强极限；所调用的是这些已证明结果，不是节点表示、网格形状或新的 Sobolev 近似输入。

## 同一原限制 jet 的身份

第9项先将 φ 的 C∞ 紧支性转换为实际全局 LipschitzWith C，再对 F=S.indicator φ.value 供应保持常数的 Lipschitz、真实紧支、closure S 支撑以及 a.e.C¹。第3项于是给其实际全空间弱 H¹ jet U 的域限制属于原 dirichletJetSpace。

随后证明 restrictDomain S U 与给定 u **整个 jet 严格相等**。证明展开真实 L² 限制的 a.e. 代表、U 的实际 indicator 值、已给 hu 以及 ae_restrict_mem；在几乎所有域内点 indicator φ=φ，得到两者 value 的 L² 类等式。开放域和原完整测试族下的 `WeakSobolevJet.value_injective` 将该值等式提升为全部弱字段相等。成员资格因此属于原给定 u，并未悄悄更换梯度或 H¹ 状态。

第10项取 u 为 `restrictSubdomain (subset_univ S) φ.sobolevJet`，并由真实 `restrictSubdomain_test_value_ae` 内部供应 hu。其 φ.sobolevJet 是原全空间紧支光滑函数的真实 H¹ jet；子域限制逐字段保留原弱身份。最终输出的是这个指定 jet 的 H¹₀ 成员资格，不是仅存在某个同名对象。

没有输入 H²、边界法向导数零、零延拓全局 C¹、逆估计或 CE。法向导数非零时，indicator 仍可仅 Lipschitz、边界处不可微；本证明允许这一情形。所有维数均被量化，d=0 无非法坐标选择；内缩中心非空性明确保留。最终不含统一误差率或网格常数主张，逼近界 B、C 和中心可依赖给定实际函数/域。

## 固定依赖、原稿及公理

三模块 Carleman 导入闭包共 **118** 模块，其中 **115** 个旧模块与 base 逐字节相同。关键已验收版本闭包亦逐一一致：C058 `ContractedNodalSobolev` 的47模块与 `0df65a77f4a13fdab4641c30a3843f02bd8b1af8`；C059 `NodalContractionLimit` 的54模块与 `28e1f4df08f31b4337f32bd20b61dbe566762f15`；C060 `NodalDirichletMembership` 的113模块与 `50ea3111057c5d7b796cca799c10a9a900d14caf`；C098 `SubdomainContinuity` 的66模块与 `59452751f05398e3446ed5305638a1e20dc89061` 全部一致。

已读取对应旧验收范围及实际调用源码，另外复核 pinned mathlib 最近边界点定理与凸集边界零测定理的完整类型和证明。C147 是后续 Dirichlet 弱解/穷竭的使用背景，不是本批据以假设 H² 或 H¹₀ 目标结论的输入；实际成员资格由上述闭包链完成。没有把旧验收套用于改变后的依赖。

治理协议、原稿及工具链 pin 与此前已读版本一致。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean 固定4.35.0；mathlib pin与本机实际干净 checkout 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。三个模块由固定 root 导入，十项均在固定 CheckAxioms 中实际打印完整类型和依赖公理。

实际读取固定 target/full 日志，分别为 **3288 jobs**、**3944 jobs** 构建成功；本验收核对固定日志，未声称重新运行全库。固定 `/tmp/carleman-t138-boundary-local-axioms.txt` 为 **2,170,082 bytes**，SHA256 **`ffec1eaeb88c52c1c7ac0dc447090b13ed64a14de9d0e0df5729f8f76f06be66`**。

10/10项实际展开类型与已读源码一致，仅使用 `propext`、`Classical.choice`、`Quot.sound`。完整文本2502条非空公理记录和9条无公理记录均无异常集合；末行 **7052项全声明递归审计 PASS**。显式打印条数与递归总数分别记录，三模块无 sorry/admit/新增数学 axiom。

## 独立同 SHA 正式 CI 及原始产物

本 Agent 自行经 GitHub connector 查询 [run 39221552762 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39221552762/attempts/1)：main/push，head 精确匹配 checked_sha，最终 completed/success，updated_at=`2026-10-19T08:19:10Z`。三项 job 全部 completed/success：state-check **117957784047**（08:16:13Z）、lean **117957784263**（08:18:59Z）、dashboard / snapshot **117958899729**（08:19:09Z）。Lean pin、实际构建、结果记录、产物保存及 post 步骤均成功。

同 run 原始 artifact：`lean-ci-result` **12171464394**，ZIP492 bytes，digest `sha256:81c3d9320c3a9191140057c6bdc9bc7f696193438c16e5dca6b850aa2914c4f0`；`lean-declaration-evidence` **12171973277**，ZIP200800 bytes，digest `sha256:2211526a044db4c02f981d27aedb5f312ccb58438fd3ec2d3fb30e1460cbf37a`。两份 workflow_run 元数据均绑定本 run、main、精确 proof SHA。

本 Agent 自行 `gh run download 39221552762` 下载至唯一前缀 `/tmp/carleman-t138-boundary-main-ci/result.json` 和 `/tmp/carleman-t138-boundary-main-axioms/axioms.txt`。result 实际 **PASS**，`checked_sha=source_head_sha=d1dca8884990c684f923a4938e40a6cc88e1645f`，target=Carleman，`finished_at=2026-10-19T08:18:00.328801+00:00`。远端编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib 与固定 pin 一致。解压 result 为537 bytes，SHA256 `38a4ccb5603c5c06400087a61f11416bc26f4483953fccaf3be6369695384963`。

远端 raw 与固定本机副本独立逐字节比较完全一致：**2,170,082 bytes**，SHA256 **`ffec1eaeb88c52c1c7ac0dc447090b13ed64a14de9d0e0df5729f8f76f06be66`**，末行7052项递归审计通过。未混用其他阶段或动态 `.ci`；原始文本摘要和 artifact ZIP 摘要分别记录。

## 验收决定

**C154：PASS，可登记为 REVIEWED / AUXILIARY。** 十项声明未发现需修复的数学、完整类型、跨边界逻辑、a.e. 集合、支撑、强 H¹ 极限、原闭包或唯一性缺陷；同 SHA 正式三项 CI 与独立原始产物全部核验通过。

已完成所声明的非空有界开凸域上，全空间紧支光滑且真实边界零函数的原限制 H¹₀ 资格。一般边界 H² 正则性、全局二阶估计、反射 Poisson 方程和完整 P023/CE 尚未由本批清偿；原文保持 **16/26**。本次仅新增本报告，未改实现、台账、原稿或 root，未 commit/push。最终一致性检查并通知主 Agent 后，冻结上述 reviewed_at 和全部报告内容。
