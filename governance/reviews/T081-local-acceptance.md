# T081 / C097 / P025 独立本机验收

- `checked_sha`: `e71006a89160b4a22833727048495aff3f9d2016`
- `base_commit`: `68b77bdd9b152ba18e226a6a093892f548c2d90f`
- `semantic_checked_at`: `2026-10-18T23:59:39+00:00`
- `reviewed_at`: `2026-10-19T00:04:34+00:00`
- `result`: **PASS**；原完整 B.1 / P025 数学语义与同 SHA 远端证据均通过。
- `axiom_check`: **PASS**；本机与远端原始产物逐字节一致，5708 项递归审计通过。
- 范围判定：**PAPER — 原完整 Lemma B.1 / P025**，含证明末尾的两非平行面仿射核为零及角点齐次界。不是把已验收的辅助引理直接当成完整原文覆盖。

本报告直接核对固定提交六模块的全部 15 项完整类型、证明和实际相关依赖，并对照 `paper/main.tex:2796–2838`、Section 6 Cartesian 网格约定以及 `governance/analysis/T081-physical-boundary.md`。已独立核查全弱状态、真实迹、实际残差、齐次 Hessian、物理尺度、常数量词和角点结论；未以执行者报告或 CI 替代数学核查。后续工作树增量不属于本次范围。

## 全部 15 项声明

名称均加前缀 `Carleman.`；源码位置相对于固定提交的 `Carleman/Spatial/`。

| # | 声明 | 源码位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `physicalBox_weak_face_scaled_bound` | `PhysicalBoxTraceBounds.lean:14` | PASS；真实面迹平方界合法取根，得到 √ℓ_i‖Tr_i w‖≤2(‖w‖+ℓ_i‖∇w‖)。 |
| 2 | `physicalBox_weak_face_uniform_bound` | `PhysicalBoxTraceBounds.lean:37` | PASS；ℓ_i≤κh、κ≥1 给 2κ 的统一物理尺度界。 |
| 3 | `physicalBox_affine_face_norm_scaling` | `PhysicalBoxTraceBounds.lean:50` | PASS；真实面 Jacobian 的精确平方范数身份给 √J_vol‖Tr_ref p̂‖=√ℓ_i‖Tr_phys p‖。 |
| 4 | `physicalBox_selected_reference_trace_bound` | `PhysicalBoxTraceBounds.lean:61` | PASS；原 w 零迹及实际迹线性将参考仿射面迹控制为 2κE_h(w−p)，全部面集统一。 |
| 5 | `h1_scaled_value_gradient_add_bound` | `PhysicalBoxBoundaryCorrection.lean:14` | PASS；真实 value/完整梯度及非负 h 的加权三角不等式。 |
| 6 | `physicalBox_h1_boundary_correction` | `PhysicalBoxBoundaryCorrection.lean:24` | PASS；参考核校正、可逆仿射拉回、原闭面保持及精确物理尺度组合，A=1+2κ²K 先于盒、h、J、w、p。 |
| 7 | `physicalBox_diameter_bound` | `PhysicalBoxH2Affine.lean:13` | PASS；实际 Euclidean 盒图和对角 CLM 范数给 dist(x,y)≤nL，未假定所需直径估计。 |
| 8 | `physicalBox_h2_affine_approximation` | `PhysicalBoxH2Affine.lean:41` | PASS；全部弱 H² 状态在物理域直接使用均值仿射逼近，给 B h²‖field₂u‖，B 只依赖 n、κ。 |
| 9 | `unitCube_face_tangent_derivative_zero` | `AffineCornerKernel.lean:12` | PASS；同一真实闭面上两个顶点之差迫使每个切向仿射导数为零。 |
| 10 | `unitCube_two_faces_affine_zero` | `AffineCornerKernel.lean:37` | PASS；不同坐标法向的两个任意上下闭面消去全部斜率及常数项。 |
| 11 | `physicalBox_two_faces_affine_zero` | `AffineCornerKernel.lean:64` | PASS；实际可逆拉回和闭面像身份把核零传到任意正侧长物理盒。 |
| 12 | `physicalBox_h2_boundary_affine` | `PhysicalBoxBoundaryAffine.lean:14` | PASS；先取 A、B，再以 C=AB 组合真实原弱状态的逼近与边界校正。 |
| 13 | `physicalBox_h2_boundary_affine_actual` | `PhysicalBoxBoundaryAffine.lean:41` | PASS；输出实际 affine map 与同一物理域 H¹ 残差，a.e. 值确为 u−p，保留全部闭面零值与 h² 界。 |
| 14 | `physicalBox_h2_corner_bound` | `PhysicalBoxBoundaryAffine.lean:67` | PASS；对两非平行面取 J，原校正多项式严格化为零，得到 u 自身的齐次 Hessian 控制。 |
| 15 | `OriginalForm.boundary_affine_lemma` | `BoundaryAffineLemma.lean:13` | PASS；令 ℓ=b−a 精确改写为任意端点 a、b 的完整原文接口，常数与所有后续数据统一。 |

## P025 原命题逐项映射

原 `lem:fd-boundary-affine`（`paper/main.tex:2803`）为每个 v∈H²(B_K)、在指定物理面 F∈F_K 上零迹的状态，寻找在这些面上消失的仿射 p_K，使 `‖v−p_K‖L²+h‖∇(v−p_K)‖L²≤Ch²‖D²v‖L²`，C 仅依赖维数和网格步长比较界。证明末尾还指出两个非平行物理面消去整个仿射核。

| 原文内容 | 固定提交中的实际对应 | 判定 |
|---|---|---|
| 任意正维矩形块 B_K | `openCoordinateBox a b`，任意正侧长；环境维数 n=d+1≥1 | PASS；原轴平行矩形块是该一般类的特例。 |
| 仅依赖维数和步长比较界的 C | `∀ d,κ≥1, ∃ C>0, ∀ a,b,h,J,u`；h/κ≤b_i−a_i≤κh | PASS；常数选取在位置、尺寸、状态之前。 |
| 每个原弱 H² 状态 | `WeakSobolevJet n 2 (volume.restrict B) B`，真实全阶 L² 字段及全部分布测试 | PASS；无光滑或连续代表、延拓、H¹₀ 或预设逼近前提。 |
| 在每个指定物理面上零迹 | 同一原状态一阶截断的 `weakJetBoxFaceLinearMap=0` | PASS；是实际 L² 物理面迹，不是自由给定边界值。 |
| 任意物理面配置 | 任意 `J : Finset (Fin n × Bool)` | PASS；同时覆盖空集、单面、上下侧、角点和全部面，原 F_K 为特例。 |
| 仿射 p_K 且面上消失 | 实际 `→ᵃ[ℝ] ℝ`，所选整个闭面上处处为零 | PASS；含边缘与角点，强于只在相对开面 a.e. 消失。 |
| 原差的 L² 与梯度误差 | r=`truncate u−affineBoxJet q`，真实 H¹ 值类及全梯度；a.e. 等于 u−p | PASS；非任意误差能量，也未为不同结论更换残差。 |
| 齐次 h² Hessian 控制 | RHS 精确 `C*h²*‖WeakSobolevJet.field 2 u‖` | PASS；无零阶/一阶或完整 H² 范数替代。 |
| 两非平行面仿射核零 | `physicalBox_two_faces_affine_zero` | PASS；任意两个不同坐标法向、任意上下侧。 |
| 角点时可取 p_K=0 并得强制界 | `physicalBox_h2_corner_bound` | PASS；原函数本身的 value+h·gradient 由 h² Hessian 控制。 |

原 Section 6（`paper/main.tex:1634` 起）取正维、各方向步长互相可比的 Cartesian 网格，h 为最大步长；Appendix B 在 `paper/main.tex:2789` 附近把 B_K 定为包含 K 和活动基函数支撑的轴平行局部矩形块，块边长与 h 可比。这里用一个 κ≥1 表达这些两侧比较，允许把仅依赖维数的局部块宽因子吸收进比较界；没有要求具体位置、固定边长、正方形或特定面配置。证明适用于所有这样的盒，因而不需要把完整 FD 离散系统当作该局部引理的额外输入。

P025 的三个覆盖声明应取 `OriginalForm.boundary_affine_lemma`、`physicalBox_h2_corner_bound` 和 `physicalBox_two_faces_affine_zero`，都必须绑定本次同一 checked SHA。它们联合覆盖原 B1 全部陈述及指定证明末尾结论。其余 12 项为此次完整证明的内部辅助接口。

## 全部弱状态、真实迹与原残差

原 `WeakSobolevJet` 的字段是零、一、二阶对称多重指标导数的真实 L² 类；所有各阶分量及全部坐标方向满足对全部 SpatialTest 的积分分部身份。SpatialTest 包含所有原域内紧支 C∞ 测试，而非缩小的特选测试族。已核对实际类型，没有把自由梯度或二阶界作为附加数据。`truncate` 只截取原低阶字段，value 和一阶字段与原状态定义相同；`OriginalForm` 在最终声明中只是命名空间，不隐含额外形式模型或算子前提。

T074 的物理域均值仿射构造仍是任意弱 H² 状态的完整结果：斜率取实际弱梯度均值；先对每个梯度分量使用原弱 Poincaré，再用二阶分量收缩和明确 d² 上界控制完整梯度误差；对同一零均值残差再用一次 Poincaré。输入没有光滑代表或全空间弱延拓前提。当前代码与该已验收版本的相关定义/证明逐字节一致。

真实面迹由物理盒的保测度坐标图和 a.e. 弱区间切片的实际连续代表端点构造，区间长度恰为 ℓ_i。全部弱切片测试的共同例外零测集由可数稠密测试对和连续配对取得；不是只逐测试声称 a.e.。所得迹是 L² 面类，满足 `‖Tr_i w‖²≤2/ℓ_i‖w‖²+2ℓ_i‖∇w‖²`，并在连续代表存在时等于其实际面限制。T078 的实际端点可积性与线性证明保证对 jet 差真实地有 `Tr(w−p)=Tr(w)−Tr(p)`。

实际仿射 jet 的弱导数由常 Fréchet 导数的积分分部证明，全梯度组装不是指定一个方便的能量模型。`h2AffineResidual_eq_jet_sub` 使用原开域的弱导数唯一性把 T074 构造的残差识别为 `truncate u−affineBoxJet p`；因此不仅 value 相同，全部一阶字段也相同。校正后继续在同一原物理域取该真实 jet 差。最终 actual 入口在 a.e. 代表层面证明 value(r)=value(u)−p，并将同一 r 交给范数界；其 H¹ 类型保证所写梯度就是该差的弱梯度。

零迹是原 B1 的显式假设，不是新增前提。本批不需要先从全局 H¹₀ 推导它，也未假定 u 为 H¹₀。相关 H¹₀ 到局部物理面零迹的应用接口、B2 的矩重构和全局加权求和、完整 FD 实例仍可继续开发，但不阻止本局部显式零迹命题完成。

## 物理尺度和常数完整核对

写 n=d+1、J_vol=∏ᵢℓ_i、E_h(w)=‖value(w)‖+h‖field₁(w)‖。实际图 Φ(x)=a+diag(ℓ)x 是可逆连续线性映射加平移，Jacobian 为 J_vol>0；其真实开盒和完整闭面像身份都已核对。

T080 的标量积分换元从已证明的仿射限制换元得到：物理 bulk L² 范数平方是 J_vol 乘参考平方范数；第 i 个面的 Jacobian 为 J_vol/ℓ_i，来自所有其余坐标长度的真实乘积。面参数化与 Φ 逐点交换，不是只给形式测度因子。实际仿射拉回 T 在全部系数空间上为线性等价，且 `poly(Tp)=poly(p)∘Φ`、`(Tp)'(e_i)=ℓ_i p'(e_i)`。所以

`√J_vol·‖Tr_ref(Tp)‖ = √ℓ_i·‖Tr_phys(p)‖`。

两个平方根边的非负性及长度正性均明确供应后才由平方等式推出此式。没有把面 Jacobian 当作体积 Jacobian，也没有遗留逆因子。

从真实弱迹平方界乘以 ℓ_i 再合法取根，得到 `√ℓ_i‖Tr_i w‖≤2(‖w‖+ℓ_i‖∇w‖)`。ℓ_i≤κh、κ≥1 给 `≤2κ E_h(w)`。令 w 的所选迹为零，则 `Tr_phys(p)=−Tr_phys(w−p)`；换元后逐所选面得到 `√J_vol‖Tr_ref(Tp)‖≤2κE_h(w−p)`。参考所选面映射用有限 Pi 的 max 范数，因此相同上界直接对整组成立；没有偷偷增加随 J 变化的因子，未选分量为零、J 为空时也合法。

T078 提供单位立方体常数 K=K(n)>0，先于全部面集和仿射输入，给参考核中的 q̂ 及参考真实 bulk+全梯度误差≤K·参考面映射范数。取 q=T⁻¹q̂，精确闭面像身份保留 q 的全部物理闭面零值。

梯度换元的实际平方式为 `‖∇(Tp)‖ref²=J_vol⁻¹∑ᵢℓ_i²‖∂ᵢp‖phys²`；以 h/κ≤ℓ_i 得 `h‖∇p‖phys≤κ√J_vol‖∇(Tp)‖ref`。bulk 值的精确 √J_vol 缩放再用 κ≥1，得到 `E_h(p)≤κ√J_vol E_1(Tp)`。应用于同一 p−q，并接上实际面迹界，恰得

`E_h(p−q)≤2κ²K E_h(w−p)`，

再由真实 jet 线性和加权三角不等式得到 `E_h(w−q)≤A E_h(w−p)`，A=1+2κ²K。K 在选择盒之前已确定；Φ、a 和各 ℓ 的依赖只出现在等价与精确缩放中，最终没有留在 A 内。

物理盒的开放、凸、有界及正体积由真实盒几何内部证明。原点不受限制。对角范数界和参考单位立方体的实际 Euclidean 距离给 `diam(B)≤D=nκh`；n≥1、κ≥1、h>0 保证 h≤D。因此直接在物理域应用 T074，得到

`E_h(u−p)≤B h²‖field₂u‖`，`B=(2^n+1)n(nκ)²`。

这里 D² 精确提出 h²，右端始终是原物理域的实际二阶对称导数字段范数。没有需要而未完成的全弱 H² 状态拉回；仅有限维仿射校正需要缩放。该路线与原文的“先拉回全部状态”路线结论等价。

最终代码先选 A、B，再取 `C=AB=(1+2κ²K)(2^n+1)n(nκ)²>0`，之后才引入 a、ℓ、h、J、u。实际完整类型保留该量词次序，最后以 ℓ=b−a 改写为任意 a、b，证明参数和端点转换没有改变常数。没有小 h、固定盒、正交多项式、边界光滑或额外导数界限制。

## 全部边界模式和角点结论

闭面核的实际 iff 已核对：从连续多项式在开横截面 a.e. 为零，利用正测开集上的连续唯一性得到处处为零，再延拓到整个闭横截面；insertNth 像身份给整个闭面含边缘和角点。核校正始终使用这个实际空间，不把零测边缘上的任意 Lp 代表值当作边界值。

单位立方体单面消失时，以该面上的点 x 及 x+e_k（k≠i）比较实际仿射值，得每个切向斜率为零；这些点确实属于指定上/下闭面。第二个不同法向面再消去剩余法向斜率，标准基张成全空间使整个 CLM 为零，在第一面取一点即得常数项为零。因此 `unitCube_two_faces_affine_zero` 得系数 p=0，进而全 affine map 处处为零，不只是盒上 a.e. 为零。

物理盒版本通过真实线性等价 T 的单射性传回，所有上下侧均保留。不同坐标法向 i≠j 正是本轴平行盒中两面的非平行条件。角点强制界取 J={(i,ui),(j,uj)}，用原两条零迹假设供应完整 J 条件，再将 B1 产生的 q 由核零严格化为 0；仿射 jet 的线性性给其 jet 也为 0，因此得到原 u 自身的 `‖u‖+h‖∇u‖≤Ch²‖D²u‖`。

n=1 仍覆盖 B1 的空面、单端点和双端点配置；不存在不同坐标法向的角点前提，未因此排除一维 B1。h>0 和 ℓ_i>0 是原物理网格非退化条件；未除以状态或 Hessian 范数，零状态及零 Hessian 均正常覆盖。

## 固定版本、构建与递归公理

六新模块的 Carleman 导入闭包共 179 个模块，173 个既有模块相对 base 逐字节不变；root 明确导入六模块。另将 T074 的五模块及弱 jet/弱 Poincaré 定义、T078 的六个相关模块及实际迹/切片依赖分别与其已验收固定版本比较，16 个关键文件均逐字节未变。AGENTS、治理流程、原论文、Lean/mathlib pin 和两个 CI workflows 未改。原论文 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

固定 `/tmp/carleman-physical-boundary-target.log` 实际显示 BoundaryAffineLemma 定向构建 3361 jobs 成功；`/tmp/carleman-physical-boundary-full.log` 实际显示 Carleman 全库 3726 jobs 成功。固定 `/tmp/carleman-physical-boundary-local-axioms.txt` 的 15 项完整类型逐项与固定源码核对，每项恰有一条完整类型和一条递归公理打印。全部 1732 条显式公理打印（1728 个不同声明）也已扫描，只有 `propext`、`Classical.choice`、`Quot.sound`；末行确认所有 5708 个 Carleman 声明（含内部生成声明）递归审计通过。

实际公理审计程序相对 base 未改，本批新增 15 项显式打印；仍遍历全部 Carleman 声明并递归 `collectAxioms`，拒绝白名单外项。六新模块无 sorry/admit 或新增公理。固定本机产物为 1,656,911 bytes，SHA256 `45b447e0c23d9dfae6353d172fcdcfbffbb78ea9e4363549c6cbfdbb386afe5c`。Lean 4.35.0，mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`。

## 远端证据与签发状态

在签发时间独立从 GitHub 查询 [main CI run 39178646933 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39178646933/attempts/1)，其事件为 `push`、分支为 `main`、`head_sha` 为本报告固定 `checked_sha`，run 已为 `completed/success`，最后更新时间为 `2026-10-19T00:03:08Z`。三个实际 jobs 均最终成功：

| Job | ID | 最终状态 |
|---|---|---|
| `state-check` | `117826516075` | `completed/success` |
| `lean` | `117826516285` | `completed/success` |
| `dashboard / snapshot` | `117827594730` | `completed/success` |

独立读取同次原始 `/tmp/carleman-physical-boundary-main-ci/result.json`：`status=PASS`，`checked_sha=source_head_sha=e71006a89160b4a22833727048495aff3f9d2016`，`finished_at=2026-10-19T00:01:29.765492+00:00`，target 为 `Carleman`。其中 Lean 4.35.0 Linux 版本的 commit 为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib commit 与固定源码 pin 一致。

独立查询远端 artifact 元数据，`lean-ci-result`（ID `12155311976`）和 `lean-declaration-evidence`（ID `12155207097`）均绑定上述同 run、main 分支与固定 SHA，且未过期。已将下载的原始 `/tmp/carleman-physical-boundary-main-axioms/axioms.txt` 与固定本机副本逐字节比较：完全相同，均为 1,656,911 bytes，SHA256 为 `45b447e0c23d9dfae6353d172fcdcfbffbb78ea9e4363549c6cbfdbb386afe5c`。远端副本包含本批全部 15 项相同完整类型和递归公理结果；再次扫描全部 1732 条显式公理打印没有白名单外公理，末行实际为 `Axiom audit passed for all 5708 Carleman declarations.`。没有混入后续 T082 工作树产物。

最终结论：15 项和原完整 B1/P025（含角点结论）通过，未发现数学缺陷，**PAPER / PASS** 范围成立。可将 C097/P025 升为 **REVIEWED**，使原文从 12/26 增至 13/26；B2、P1、完整 FD 实例及后续应用不得随之自动提升。本 Agent 仅写本报告，未修改实现、台账、root 或原稿，未 commit/push。
