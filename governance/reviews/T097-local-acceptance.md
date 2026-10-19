# T097 / C113：原 Lemma B.2 / P026 独立本机验收

- `checked_sha`: `a9ca6fccf19cc677a4a60b07f373eb533df9d502`
- `base_commit`: `ab5f74bf708c3bb969ecca40fcee8b26edd16d96`
- `semantic_checked_at`: `2026-10-19T02:26:30+00:00`
- `reviewed_at`: `2026-10-19T02:30:07+00:00`
- `result`: **PAPER / PASS**；完整原 B.2 语义、同 SHA 三项 CI 和原始产物核验全部通过。
- `axiom_check`: **PASS**；远端原始产物与固定本机副本逐字节相同，6188 项递归审计通过。
- `scope`: **PAPER**；原 `lem:fd-weighted-approximation` / `eq:fdapproxallD`，覆盖项 **P026**。
- `extra_hypotheses`: **无**；最终接口的环境、权和状态条件由原矩形设置和原允许权假设供应。
- 最终原文接口：`Carleman.allowed_weight_cartesianKuhn_approximation`。

本报告直接读取固定四模块的全部 7 项源码、证明和完整实际类型，并复核相关真实 J_h/R_h/Q_h、H¹₀ 重构 jet、局部逆估计、弱导数局部唯一性、局部 B.1 逼近、允许权比较及有限重叠求和依赖。对照原 `paper/main.tex:1634–1666` 的 FD 网格及矩重构定义、`2841–2869` 的完整 B.2，以及 `291–302` 的原允许权族；同时核对 `governance/analysis/T097-kuhn-weighted-error.md`。没有用执行者报告、规格或 CI 替代数学核查，后续工作树中的刚度模块不在本次验收范围内。

## 全部 7 项声明

名称均加前缀 `Carleman.`；位置相对于固定提交 `Carleman/Spatial/`。

| # | 声明 | 固定位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `BoundedMultiplier.bochner_map_restrict` | `WeightedMeasureAnchor.lean:16` | PASS；对任意较小测度，将真实全域乘权类的局部 Bochner 范数识别为同一原权和原场的 L² 限制范数，全部代表身份为 a.e.。 |
| 2 | `BoundedMultiplier.bochner_map_le_anchor` | `WeightedMeasureAnchor.lean:27` | PASS；实际局部权上界 W·s 给真实标量或向量 L² 场的乘权上界，可积性由原 Lp 及测度单调性供应。 |
| 3 | `BoundedMultiplier.bochner_le_map_anchor` | `WeightedMeasureAnchor.lean:33` | PASS；严格正锚点及 s≤W|σ| 给反向 W/s 界，没有除以可能为零的锚点或场范数。 |
| 4 | `cartesianKuhn_h2_weighted_local_error` | `CartesianKuhnWeightedLocalError.lean:13` | PASS；原完整状态的真实局部值/弱梯度误差乘权，锚点严格抵消为 W²A，常数在网格、锚点、权和状态之前。 |
| 5 | `cartesianKuhn_error_assembly` | `CartesianKuhnErrorAssembly.lean:13` | PASS；用真实闭单元与原域交集、精确限制测度身份和已证重叠界，将实际平方范数组装到全域，只损失 √(2·5ⁿn!)。 |
| 6 | `allowed_weight_cartesianKuhn_h2_error` | `AllowedCartesianKuhnError.lean:15` | PASS；在最终证明内部供应所有局部权比较、正锚点和单元误差，再求和得到真实误差 jet 的完整 B.2。 |
| 7 | `allowed_weight_cartesianKuhn_approximation` | `AllowedCartesianKuhnError.lean:63` | PASS；直接以原 L² 差和完整真实弱梯度差写出论文结论，右端为原加权 Hessian；所有原状态和允许权均覆盖。 |

## 原命题及实例化

原 B.2 对矩形 Ω 上的任意 `u∈H²(Ω)∩H¹₀(Ω)`、任意原允许权 σ，以及固定时刻的 `h q(t)≤1`，要求

`‖σ(u−Q_hu)‖L²(Ω) + h‖σ∇(u−Q_hu)‖L²(Ω) ≤ C h²‖σD²u‖L²(Ω)`，

C 不依赖网格、h、q、σ 和 u。原数值设置为正维数 n、Ω=∏(0,L_j)、N_j≥2、δ_j=L_j/N_j、h=max δ_j、各方向步长可比、同向 Kuhn 剖分、原完整内部节点和零边界值。

最终类型使用 n=d+1，覆盖全部原 n≥1。先固定开放、凸且闭包紧的环境 S、原空间轮廓 ρ 和 κ≥1，再选 C>0；其后才量化 o、全部正 δ、N、网格盒 Ω_g⊆S、h>0、`h/κ≤δ_j≤h`、任意 TimeWeight、τ、t、η，以及原全部弱 H²∩H¹₀ 状态。

对原命题取 S=Ω、o=0、δ_j=L_j/N_j，则 Ω_g=Ω，包含条件为等号；原矩形的开放性、凸性和闭包紧性直接供应环境条件。ρ 的原闭包光滑性蕴含这里所用 C¹ 条件，有界可测性也由原光滑有界域供应。h=max δ_j 在原正维数和正步长下严格正；互相可比的步长给某个固定 κ≥1 的下界，δ_j≤h 由定义成立。没有扩大原所需小参数约束 `hq≤1`，没有额外要求 h≤h₀、N_j 较大或特殊长宽比。

允许更一般的 Ω_g⊆S 和 h 并未缩小原状态/网格范围。原固定域实例保持 C 与网格无关；并非为每个网格另选 S 或空间轮廓。最终证明没有局部逼近、零迹见证、仿射再现、逆估计、锚点、有限重叠或权比较等未清偿前提。

## 真实 J_h、R_h、Q_h 及弱状态

已重新读取实际 `CartesianKuhnProjection` 和 `CartesianKuhnReconstructionJet` 定义。内部索引逐轴 `Fin(N_j−1)` 对应原整数 `{1,…,N_j−1}`；物理节点是 o_j+(a_j+1)δ_j。原实际矩为

`(J_hv)_a=(∏jδ_j)⁻¹∫Ω_g vφ_a`，

重构为同一真实连续 Kuhn 帽函数有限和 `R_hf=Σ_af_aφ_a`。`cartesianKuhnProjection`、`cartesianKuhnProjectionLp` 和 `cartesianKuhnProjectionJet` 都由同一个 `cartesianKuhnMoment` 和同一重构定义，不是正交投影、另一插值或抽象稳定算子。没有对一般 L²/H² 类取节点值；只有仿射函数和有限网格对象使用合法点值。

重构的实际 L² 类经与原零边界 nodal 函数的等式，属于真正 `dirichletSubspace Ω_g`。后者是全体紧支光滑测试函数在真实 H¹ 图拓扑闭包的标量像。`cartesianKuhnReconstructionJet` 从该已证资格选择真实弱 H¹ jet，且值严格等于同一 R_h 的 L² 类。选择见证不会允许任意梯度：在开放域上弱 jet 的值注入性保证唯一性。`cartesianKuhnReconstructionJet_gradient_on_cell` 进一步证明其弱梯度在每个闭单元上 a.e. 等于真实仿射插值的 Fréchet 导数；零测单元边界被正确处理。

输入 `WeakSobolevJet n 2` 由实际 L² 值、一阶和二阶全部多指标场构成，各阶通过全测试族的分布导数身份连接。`DerivativeFiber n k` 为全部 k 阶多指标的 Euclidean 空间，混合导数按多指标计一次；范数是原导数集合的真实 Euclidean L² 范数。输入值属于原 H¹₀ 即原边界要求，不另加平滑代表、单元可微性、特殊频率或有限维状态限制。

实际误差 `cartesianKuhnErrorJet` 是原截断弱 H¹ jet 减去同一 Q_h jet，因此值就是原 L² 差，第一阶场就是原弱梯度差。最终声明只将这两项展开，未改变范数或输入；`truncate` 保留值和第一阶字段，字段的线性性使弱梯度相减为定义上的同一个对象。右端直接使用原 u 的二阶字段，并非重构 Hessian、目标误差或任意能量见证。

## 无权局部误差依赖的实质核对

T096 的固定证明正是本批 base，相关旧模块相对 base 均未修改；本次仍直接读取 `CartesianKuhnLocalError`、`CartesianKuhnErrorStability`、`CartesianKuhnErrorLocality`、`WeakJetLocality`、`CartesianKuhnWeakInverse` 和实际逆映射依赖。

无权局部界从原全部 H²∩H¹₀ 状态出发，调用已验收 B.1 及真实全局 H¹₀ 到局部物理面零迹结论。T094 的同一 p 在中心闭单元满足 Q_hp=p，且真实局部弱 H¹ 残差 r 的值为 u−p，并有 h² 局部 Hessian 控制；其物理面覆盖包含角点，未要求 p 在人工邻域面为零。p 通过实际仿射系数表示构造为全域弱 H¹ jet。

原 Q_h 值的减法线性性经真实弱 jet 值注入性提升到 jet 层；局部再现使 e(u)=e(u−p) 的值在闭单元上 a.e. 相等。证明先限制到开放单元内部，用真正弱导数唯一性得到各弱字段相等，再由单元边界零测恢复闭单元 a.e. 身份。不是从孤立点或仅边界相等推导梯度相等。

在实际裁剪开块上，u−p 的全域 jet 限制与 r 的值 a.e. 相等，同一唯一性再次给整个局部 jet 相等，因此 r 的值和梯度范数恰是原全域残差的局部范数。局部稳定性对全部真实弱 H¹ 输入成立：值项使用实际 Q_h 局部 L² 稳定性，梯度项使用实际重构的统一逆界。

该逆界的参考单纯形固定在维数 n 上。真实物理仿射图为坐标置换接坐标伸缩，置换逆保持 Euclidean 范数，δ_j≥h/κ 给其实际逆线性算子范数≤κ/h。已证仿射单纯形 L² 换元和全梯度范数界因此给 C_inv/h；C_inv 在位置、步长、排列、单元和全部节点系数之前。无需另加目标逆估计或单元形状见证。h 乘该梯度界精确抵消 1/h，局部稳定常数可取 C_inv+2；再乘 B.1 常数，得到实际无权局部误差 A₀(n,κ)h²‖D²u‖L²(B)。

## 局部真实乘权与锚点抵消

新 `WeightedMeasureAnchor` 对一般 `ν≤μ` 工作，因而适用于闭单元仅在零测边界意义下包含于原开域的情形。`bochner_map_restrict` 将全域 `σ.map u` 的局部范数与同一 multiplier 的测度限制、同一原场的 `MemLp.toLp` 限制连接；三份代表等式都在 ν 下 a.e. 成立。原场和乘权场的局部 L² 有限性均来自已证 MemLp 及测度单调性，没有使用无穷值的 `toReal` 总化。

`BoundedMultiplier.map` 是真实点态标量乘法在 L² 商空间上的实现，`seminorm` 就是其 L² 范数。已读其平方积分身份 `∫|σ|²‖u‖²` 和实际可积性。它作用于标量误差、完整梯度和完整 Hessian，不是给这些字段另配抽象范数。

局部定理显式暂取 `W>0`、`s>0` 及 B 上 `|σ|≤Ws`、`s≤W|σ|`。闭单元限制测度≤B 的限制测度≤原域限制测度，使前一权界可下传到单元。误差值和 h 倍梯度分别乘 Ws，原 Hessian 的反向比较给 W/s；所有相乘系数的非负性由 W、s、h、A₀ 的正性供应。于是

`Ws · A₀h² · (W/s) = W²A₀h²`。

这里 s 严格为正，所以抵消合法；没有保留锚点大小、局部体积或 σ 的绝对幅度。局部常数 W²A₀ 先于全部网格、s、σ 和 u，且仍是真实局部加权 Hessian 范数。

## 原允许权、任意幂次和 T 统一性

原允许权是 `σ(t,x)=q(t)^τ exp(ηρ(x)q(t))`，η∈{1,−1}、|τ|≤τ_*。实际 `SpatialProfile.scaled` 和 `multiplier` 恰给这一函数；实数条件 |η|=1 精确覆盖两种符号。空间限制 `onSubdomain` 保持同一函数值，并有真实限制与乘权可交换身份。

最终定理先从固定 S、ρ 的 C¹ 闭包正则性取得 L≥1，使 `|ρ(x)−ρ(y)|≤L dist(x,y)`。该证明用真实闭包导数有界性、开放凸域闭包上的可微唯一性和凸集均值估计，未引入随网格或 q 变化的 L。

每个实际 B 非空且各方向宽≤5h，内部选 y∈B，设 s=σ(y)>0。盒直径上界给 `dist(x,y)≤5nh`。空间权比中的 `q(t)^τ` 精确相消，η 的绝对值为 1，因而在 `hq(t)≤1` 下，双向比较常数可统一取

`W=exp(5Ln)`。

W 只依赖固定轮廓/环境和维数，不依赖 s、q、q_max、τ、t、η、网格或周期。证明在每个单元内实际构造这一比较和正锚点，然后供给局部定理；调用者不需提供比较假设。

`TimeWeight` 只要求 q 的正下界和有限全局上界；原 qclass 的周期延拓满足这些条件。最终 C 在任意 TimeWeight 和任意 t 之前，故覆盖所有原周期 T>0 以及所有原时刻，C 对 T 统一；证明不含时间积分、端点或方向条件。省略未用于纯空间结论的 q′、q″、β 和周期性要求加强了声明。τ 可为任意实数，故原整个区间 |τ|≤τ_* 也统一覆盖；原 ρ 的负性在此亦不必使用，未缩小原允许权族。

## 闭单元、有限覆盖和无基数损失的组装

实际闭 K 包含物理边界，不能直接断言 K⊆Ω_g。本证明对每个单元取 `A_K=K∩Ω_g`，这是真正可测子域。实际单纯形 frontier 零测、开放凸原域包含单元内部，给出精确限制测度等式 `volume.restrict A_K=volume.restrict K`。输入局部范数因此无损地转入真实子域范数。

实际有限 Kuhn 分割覆盖原开域，所以 A_K 给 a.e. 全覆盖。值和梯度的全域平方范数分别不超过局部平方范数之和。相关 `L2FiniteOverlap` 证明从真实平方范数积分出发，先供应 L² 平方可积性和每个指示函数项的可积性，再合法交换有限和与积分；没有把形式有限求和当作积分覆盖。

对 B_K^+ 的重叠，直接核对实际 `CartesianPatchOverlap`：对任意空间点，每个可能格点原点逐轴落在长度 5 的整数窗口，格点索引与 Kuhn 排列的配对是单射；每盒 n! 个排列，故所有实际裁剪块的点态重叠≤M=5ⁿn!。裁剪只减少覆盖，不增加重叠。这个数与 N、δ、位置、单元总数和域大小无关。

将各局部非负和 `a_K+h b_K≤A h²H_K` 平方，可舍去其非负交叉项，得到 `a_K²+h²b_K²≤(Ah²)²H_K²`。覆盖和重叠控制给全域平方和≤(Ah²)²M‖σD²u‖²，再用 `(a+hb)²≤2(a²+h²b²)` 和非负平方根，得到精确损失 `√(2M)`。没有把局部范数之和粗略估成单元数倍，也没有残留依赖网格基数的常数。

综合起来，可选最终常数

`C=√(2·5ⁿn!) · exp(10Ln) · A₀(n,κ)`。

该表达式说明所有 C 的选择均先于数值网格、h、权和状态，与最终实际类型的量词次序一致。

## 加宽块路线及完整 PAPER 判定

本证明用 T093/T094 的加宽裁剪块 B_K^+ 代替原证明中的最小 B_K。它的边长位于 `[δ_j,5δ_j]`，包含原局部作用需要的活动帽非零点集合，B.1 的尺度比较参数统一为 5κ，且全域重叠≤5ⁿn!。物理面和角点零迹由实际边界包含关系供应。

这会改变中间局部界所用区域和固定常数，但组装后的右端是同一个原 Ω_g 上的 `‖σD²u‖`，没有加宽域积分、邻域输入或额外状态条件残留。最终 h² 阶、完整值与梯度左端、允许权范围和常数量词均与原 B.2 相同。因此此处加宽块是保留结论的证明路线变化，不是原最终命题的实质弱化。

结论为完整原 **Lemma B.2 / P026 / PAPER PASS**。这不是仅从 T094/T096 的辅助 PASS 自动推定：本次已检查最后所缺的真实加权、内部锚点比较、覆盖、重叠、全域范数以及最终原差值/弱梯度接口。三项 CI 和同版本原始产物现已核验完毕，可将 C113 与 P026 按 PAPER / REVIEWED 记录，原文从 13/26 增至 14/26。完整 FD/P012 仍需刚度及其余数值接口，不能由 B.2 单项通过而提升。

## 固定版本、本机构建和递归公理

四新模块的 Carleman 导入闭包共 283 个模块，279 个既有模块相对本次 base 逐字节未变；root 明确导入全部四模块。AGENTS、操作协议、state 证据协议、原稿、Lean/mathlib pin 和两个 CI workflows 相对 base 未改。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

固定 `/tmp/carleman-kuhn-weighted-error-target.log` 实际显示定向 3474 jobs 成功；`/tmp/carleman-kuhn-weighted-error-full.log` 显示全库 3796 jobs 成功并完成 6188 声明递归审计。固定 `/tmp/carleman-kuhn-weighted-error-local-axioms.txt` 为 1,841,706 bytes，SHA256 `0fdf3ee30ea9143b692ac7b8ec95cefccb06ab3701a55c624663acdeaf943894`。

7 项完整实际类型与固定源码逐项核对，各恰有一条类型打印和一条公理打印，均仅含 `propext`、`Classical.choice`、`Quot.sound`。全产物 2043 条带公理打印（2039 个不同带公理声明）及 6 条无公理打印已扫描，无白名单外公理；末行实际为 `Axiom audit passed for all 6188 Carleman declarations.`。递归审计程序相对 base 未改，仍用 `collectAxioms` 检查全部 Carleman 常量及私有生成声明。本批无 sorry、admit、native_decide 或新增数学公理。

## 远端证据与正式签发

已自行查询 [main CI run 39189752195 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39189752195/attempts/1)，确认事件 `push`、分支 `main`、head SHA 为本次固定 `a9ca6fccf19cc677a4a60b07f373eb533df9d502`，run 最终 `completed/success`，最后更新时间为 `2026-10-19T02:28:36Z`。三个实际 jobs 均最终成功：

| Job | ID | 最终状态 |
|---|---|---|
| `state-check` | `117859742825` | `completed/success` |
| `lean` | `117859742923` | `completed/success` |
| `dashboard / snapshot` | `117860870916` | `completed/success` |

已独立读取远端 artifact 元数据：`lean-ci-result`（ID `12159706766`）及 `lean-declaration-evidence`（ID `12159109764`）均未过期，且各自绑定同一 run、main 分支和上述固定 SHA。本 Agent 使用该 run 自行下载两份原始产物，两个下载进程均 exit 0。

原始 `/tmp/carleman-kuhn-weighted-error-main-ci/result.json` 实际为 `status=PASS`，`checked_sha=source_head_sha=a9ca6fccf19cc677a4a60b07f373eb533df9d502`，`finished_at=2026-10-19T02:26:43.612494+00:00`，target 为 `Carleman`。实际 Lean 4.35.0 Linux commit 为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib commit 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，与固定源码 pin 一致。

原始 `/tmp/carleman-kuhn-weighted-error-main-axioms/axioms.txt` 与固定本机副本经过独立逐字节比对，完全一致：1,841,706 bytes，SHA256 `0fdf3ee30ea9143b692ac7b8ec95cefccb06ab3701a55c624663acdeaf943894`。远端 7 项完整类型各一条、公理结果各一条，均匹配固定源码；全部 2043 条带公理打印仅含三项正常基础公理，另有 6 条无公理打印，末行再次确认全库 6188 声明递归审计通过。未使用后续工作树的 `.ci/axioms.txt`。

正式签发 **PAPER / PASS**，未发现原 B.2 范围内的数学缺陷或额外未清偿前提。可将 **C113、P026 升为 PAPER / REVIEWED，原文计数 14/26**；FD/P012 不提升。本 Agent 仅写本报告及下载所需临时证据，未修改数学实现、台账、root 或原稿，未 commit/push。
