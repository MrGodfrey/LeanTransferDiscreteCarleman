# T122 / C138 独立本机验收

- `checked_sha`: `b40c6b3a3e783529e21adc5a699f4d4d19c4edbe`
- `base_commit`: `4689b4942585bde7e96bc0ecfa1a360de012db2b`
- `reviewed_at`: `2026-10-19T05:49:00+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：开凸域上原 H¹₀ 状态的任意闭包连续代表在全部边界点为零；对原有界开凸域、d≤3 的全部弱 H²∩H¹₀ 状态内部构造同一闭包连续代表并给出全部边界零值。全网格 conforming 插值、实际误差 jet 和全域允许权组装仍待，P011 不提升，原文保持 **14/26**。

本 Agent 从固定 git 对象读取四模块全部证明、5项完整展开类型及关键依赖，对照原 `paper/main.tex` Section 6 的原 V=H¹₀、完整 Vh 及 Step 2 的闭包连续节点插值范围（1466–1489、1530–1548），并读取固定 T122 分析、MATH_SPEC 和 C138 台账。执行者说明与 CI 未替代数学审查；未提交 T123 等后续工作树增量和变化中的 `.ci` 产物均排除。

## 全部五项声明

以下名称省略公共前缀 `Carleman.`，位置以 `Carleman/Spatial/` 为根。顺序与固定交付 JSON 和 C138 台账逐项一致。

| # | 声明 | 固定位置 | 独立结论 |
|---|---|---|---|
| 1 | `exists_smooth_gap_cutoff` | `SmoothGapCutoff.lean:13` | PASS；真实全局光滑 Lipschitz 截断，0 与远离0两区域的函数值和导数值均由实际邻域恒等式证明。 |
| 2 | `weak_zero_gradient_ae_constant` | `WeakZeroGradientConstant.lean:12` | PASS；原全部弱梯度为零，经真实均值 Poincare 和可积平方零积分，得到有界开凸域上 a.e. 常数。 |
| 3 | `weak_scalar_gap_on_convex` | `WeakScalarGap.lean:16` | PASS；真实全空间弱链式法则及域内零梯度排除同时占据零值和正绝对值间隙两部分。 |
| 4 | `dirichlet_continuous_zero_on_frontier` | `DirichletContinuousBoundary.lean:15` | PASS；任意开凸域、任意维数、原 H¹₀ 状态的任意闭包连续代表在每个边界点为零，无预设迹或边界零值。 |
| 5 | `WeakSobolevJet.exists_dirichlet_closure_representative` | `DirichletContinuousBoundary.lean:89` | PASS；原全部弱 H²∩H¹₀ 内部选择同一闭包代表，其 a.e. 身份和所有边界点零值同时成立。 |

## 实际光滑截断与真实弱函数间隙

第1项对任意 δ>0 取真实 `ContDiffBump` b，中心0、内半径δ/4、外半径δ/2，定义 η(t)=1−b(t)。b 的全局光滑性及紧支撑供应一个 Lipschitz 常数 M；η 的差与 b 的差仅相差负号，所以 η 全局 Lipschitz。η 本身不紧支撑，但 η(0)=0，后续复合 L² 的资格正是由此和 Lipschitz 性保证。

在0附近 b=1，故 η 在一个真实邻域恒为0，以 `EventuallyEq.deriv_eq` 得 η(0)=η′(0)=0。当 |t|≥δ 时，因为 δ>δ/2，t 严格位于 b 的闭支撑之外；真实支撑外邻域上 b=0，故 η(t)=1、η′(t)=0。没有把仅一点处取值为常数误当作导数为零，也没有漏掉 |t|=δ 的端点。

第2项先单独处理空域。非空开有界域有正有限体积，均值 c=(∫S u)/|S| 合法；u−c 具有真实 MemLp。已读取 `convex_weak_mean_poincare` 的完整弱类型及其紧凸耗尽/Fatou来源。将每个真实坐标弱导数取0后，均值误差平方积分≤0，结合非负性得到积分恰为0，再用实际可积函数的零积分定理推出 u=c a.e.。这不是仅在光滑函数上应用 Poincare，也没有用直观连通性代替弱导数论证。

第3项的 u 和全部 vᵢ 是全空间真实 L² 类，满足所有坐标方向的全空间弱导数身份。η∘u 的 MemLp 由 η(0)=0 和 Lipschitz 性内部证明；η′∘u 的可测性及 |η′|≤M 给每个 η′(u)vᵢ 的真实 MemLp。T121 的 `scalar_chain_rule` 通过原卷积、真实有界乘子强 L² 极限和全部弱测试身份的闭合，给出这些函数的实际弱导数。

已独立读取该链式法则与 `restrictDomain`。后者通过原测试函数及其导数在支撑外为零，把全空间身份限制到 S，保留 S 上全部 SpatialTest。由题设 a.e. 值域条件 u=0 或 |u|≥δ，两个区域上 η′(u)=0，所以限制后的导数 L² 类严格为0。对限制后的 η(u) 应用第2项，得到 η(u)=c a.e.。

若 c=0，则非零间隙区域会给 η(u)=1，与 c 矛盾；若 c≠0，则 u=0 区域会给 η(u)=0，与 c 矛盾。故 S 上要么 u=0 a.e.，要么 |u|≥δ a.e.。证明只使用原 L² 代表的 a.e. 信息，没有预设原 u 连续、点态可微或具有任何迹。

## H¹₀ 是原图闭包，零延拓具有全部实际弱导数

已展开 `dirichletJetSpace`、`dirichletSubspace` 和 `SobolevTopology`。前者是所有真实紧支光滑 SpatialTest 的 jet 线性张成在完整弱 H¹ 图拓扑中的闭包；后者是其真实 value 映像。图拓扑包含值和全部一阶 L² 字段，不是只取标量 L² 闭包，更不是把边界零值写进定义。

已读取 C073 的 `DirichletTestPairing` 和 `DirichletZeroExtension`。紧支光滑状态对任意全空间测试满足真实分部积分；相关值/导数配对在完整 H¹ 图拓扑连续，因而该身份延拓到上述闭包。再通过真实 L² 零延拓的 indicator 身份，得到

\[
D_i\widetilde u=\widetilde{D_i u}
\]

在全空间、全部坐标方向、全部真实弱测试意义下成立。第4项恰以这些 w=zeroExtendLp(value u)、vᵢ=zeroExtendLp(field₁分量) 调用第3项；没有把一般 H¹ 的零延拓错误当作全空间 H¹，也没有循环使用待证的边界零值。

## 每个边界点的两侧矛盾

第4项对任意 x∈frontier S 反设 f(x)≠0，取 δ=|f(x)|/2>0。f 在 closure S 上的真实连续性给一个 r>0，使 closure S∩B(x,r) 上 |f|≥δ。由原 a.e. 代表身份和零延拓的 indicator 身份，w 在整个球 B 上 a.e. 满足 w=0 或 |w|≥δ。这里 B 本身开、有界、凸，所以可调用第3项；并不要求原 S 有界。

两个分支分别如下，均已按实际证明检查：

- 若 w=0 a.e. 于 B，则在 O=S∩B 上有 f=0 a.e.。O 是开集，f 在其上连续；`Measure.eqOn_open_of_ae_eq` 以 Lebesgue 体积对非空开集的正性，将此提升为 O 上逐点 f=0。因为 x∈closure S 且 r>0，B 必与 S 相交，取得真实 y∈O，与 |f(y)|≥δ 矛盾。
- 若 |w|≥δ a.e. 于 B，则利用原开凸域的 `interior (closure S)=S`。非空 S 时由凸性和非空内部定理证明，空域另行化简。x∈frontier S 因而属于闭包外部 `(closure S)ᶜ` 的闭包。球 B 与 `(closure S)ᶜ` 的交集 O 是真实非空开集，故 volume O>0。零延拓在 O 上 a.e. 为0，同时前述下界给 δ≤0，构成正测度集合上的矛盾。

用于第二分支的 mathlib `Convex.interior_closure_eq_interior_of_nonempty_interior` 已核对，原开放性、凸性正好供应其条件；没有另加外球、Lipschitz 边界、迹算子、延拓算子或点容量假设。第一分支使用开放交集上的连续 a.e. 唯一性，其数学依据也是正测度，而不是从 S 内 a.e. 身份直接读取某个任意点。

两分支均不利用 frontier S 的零测性来推断 f 在边界的取值。论证对每个边界点单独成立，最终是全部边界点的严格等式。所选 δ、r 和截断 Lipschitz 常数仅用于局部反证；没有把这些依赖 f 或 x 的量宣称为数值统一常数。

## 全部弱 H²∩H¹₀ 的同一代表与原文范围

第5项接受任意原 `WeakSobolevJet d 2 (volume.restrict S) S`，仅加原 value∈dirichletSubspace 的 H¹₀ 条件。开、凸、有界和 d≤3 用于调用已验收 C134 构造同一个 closure S 连续代表 f，且 f 与原 value a.e. 相同；没有把连续代表存在作为最终前提。

H¹₀ 成员资格展开为一个 H¹ jet v、其图闭包成员证明及 value v=value u。第4项只需要 H¹ 状态及同一标量代表，因此用这一真实等式将 f 的 a.e. 身份对齐后，即给全部 frontier S 上 f=0；不需要更换 f，也不需要额外假定 u 的二阶导数可跨边界延拓。该存在量词先选择一个 f，再同时给原 a.e. 身份与所有边界点零值，可供后续全部边界节点共同使用。第4项本身还适用于此前任意已选合法闭包代表。

主边界定理不要求 S 有界或 d≤3；这两条件只属于最终 H² 连续代表的入口。空域分支明确处理，最终 empty closure/frontier 下结论成立；d=0 没有被排除，也没有除以 d，相关零维开放域的空边界及真实体积性质与证明一致。

原 P1 设置使用有界开凸多面体 Ω、d=2或3、V=H¹₀，以及 D(A)⊆H² 的闭包连续节点代表。本批证明其齐次 Dirichlet 边界节点义务，无新增实质限制。仍需把同一个代表放入真实全网格 conforming 节点插值，构造误差 jet 并完成全域允许权、投影和接口组装；不能据此签发整个 `prop:p1` 或P011。

## 固定依赖、构建与公理

四模块导入闭包共173个 Carleman 模块，新增恰为本批4模块，其余169模块与 base 逐字节不变。又比较既有已验收版本：C137 `WeakScalarChainRule` 的89模块闭包相对 base 不变；C134 `WeakH2ClosureContinuous` 的134模块闭包相对 `4e727b83c3fcb821432ba4089e6f9ea0c9e0a277` 不变；C089 `ConvexWeakPoincare` 的86模块闭包相对 `c99262c4a0d65a4d23f2efb57748bda490e971d7` 不变；C073 `DirichletZeroExtension` 的69模块闭包相对 `fbcd888532fe88caff4907495fad399fe6feeb55` 不变；C055 `DirichletSpace` 的30模块闭包相对 `fa61af9d4b260cac83d599ef4e228af88f67aee8` 不变。没有混用改变后的旧 declaration_version。

原稿、已读治理协议和工具链pin自 T119 不变。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean固定4.35.0，mathlib pin及本机实际HEAD为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，本机mathlib工作树干净。root显式导入4模块，`tools/CheckAxioms.lean` 对5项均含完整类型和公理输出，并递归审计全部Carleman声明。

实际读取 `/tmp/carleman-dirichlet-continuous-target.log` 的3350 jobs成功记录和 `-full.log` 的3876 jobs成功记录，后者末行为6702声明递归公理审计PASS。固定 `-local-axioms.txt` 为 **2,037,306 bytes**，SHA256 **`d3a489fa8a703d6acf48fcb8b25afd045dd97db9534202d15419834fff90ed9b`**。5项完整展开类型逐项核对；全部2339条显式公理记录中2331非空、8无公理，均无 `propext`、`Classical.choice`、`Quot.sound` 之外的公理，无sorryAx。

## 实际同 SHA CI 与原始远端证据

本 Agent 自行经 GitHub connector 查询 [main CI 39206204127 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39206204127/attempts/1)。实际run为main/push、completed/success，head SHA精确匹配固定提交。三个job均completed/success：lean **117909468872**、state-check **117909469041**、dashboard / snapshot **117910247352**。

同run原始artifact为 `lean-ci-result` **12165701788**、`lean-declaration-evidence` **12165846296**，两份元数据的workflow_run.head_sha均精确匹配。本 Agent 自行通过 `gh run download 39206204127` 下载至 `/tmp/carleman-dirichlet-continuous-main-ci` 与 `-main-axioms`。

实际 `-main-ci/result.json` 为PASS，`checked_sha=source_head_sha=b40c6b3a3e783529e21adc5a699f4d4d19c4edbe`，targets为Carleman，`finished_at=2026-10-19T05:47:38.061314+00:00`；ci_url与上述run/attempt一致，Lean提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib为上述pin。

独立逐字节比较远端 `-main-axioms/axioms.txt` 与固定本机副本，完全一致：**2,037,306 bytes**，SHA256 **`d3a489fa8a703d6acf48fcb8b25afd045dd97db9534202d15419834fff90ed9b`**。另逐名确认远端5/5完整类型，实际末行为 **6702项全声明递归审计PASS**。没有采用其他SHA或未来工作区产物。

## 验收决定

**C138：PASS，可升级为REVIEWED，scope保持AUXILIARY。** 5项声明未发现需要修复的数学缺陷。实际光滑截断、原弱链式法则、全部弱梯度为零的 Poincare 推论、真实 H¹₀ 零延拓和每个边界点的内外开集矛盾均已独立核对；最终原全部弱 H²∩H¹₀ 自动取得同一闭包连续代表和全部边界零值。同SHA三项正式CI及自行下载的原始公理证据已核实。

全网格 conforming 插值、实际误差 jet、全域允许权及投影组装仍待，P011不提升，原文保持 **14/26**。本次仅新建本报告，未修改实现、台账、原稿或root导入，未commit/push。以上签发UTC固定，通知主Agent后不再变更报告或时间戳。
