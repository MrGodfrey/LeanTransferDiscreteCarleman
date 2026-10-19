# T112 / C128 独立本机验收

- `checked_sha`: `c8377e5f743689641ab84d5049b4d0fb291d29f5`
- `base_sha`: `0d91a94335bd491366597b81f45de26b4559b7ad`
- `reviewed_at`: `2026-10-19T04:28:08+00:00`（UTC；同 SHA 最终 CI 与原始证据核验完成时间）
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**；15/15 项显式声明通过。原文覆盖保持 **14/26**，不提升 P011 / 完整 P1。
- 验收者：独立 Agent `/root/accept_section3`。本报告定稿后冻结正文及上述时间戳。

直接从固定 Git 对象读取两新模块全部证明、15 项实际完整展开类型、关键依赖、原论文与 `governance/analysis/T112-p1-h2-nodal.md`，再独立查询同 SHA main CI、自行下载同 run 原始产物并逐字节核验。执行者报告与 CI 没有代替数学验收。本次只新增本报告，未改实现、台账或提交；工作区 T113 `SmoothH2NodalGradient` 及其后续根导入、公理产物未纳入本次结论。

## 原论文对应及范围

原 `paper/main.tex` Section 6 P1 Step 2（1523–1548）使用 `d=2,3` 时的 H² 连续代表及节点插值，建立 `eq:p1-interpolation` 和 `eq:p1-interpolation-energy` 的全局加权估计。本批证明其中的一个局部基础：对 **全空间 C² 函数**，任意满维真实单纯形 K、维数 `d≤3` 及实际直径上界 D，有

`∫_K (f−I_K f)² ≤ 16 D⁴ ∫_K ‖iteratedFDeriv ℝ 2 f‖²`。

其中 `I_K` 是同一单纯形顶点上取真实 f 值的重心节点插值；二阶导数是 f 的实际 Fréchet 二阶多线性映射。右端是其多线性算子范数的真实平方积分，**不是空间上确界**。本批没有把该量声称为已经识别的弱 `WeakSobolevJet.field 2` 分量范数，也没有从任意弱 L² 等价类读取节点值。全弱 H² 的连续代表/逼近、梯度误差、全局边界资格及允许权组装仍须后续清偿，故不能据此宣布原整个局部弱 H² 插值定理或 P011 完成。

## 15 项声明逐项验收

下表名称省略 `Carleman.`，路径相对于固定提交 `Carleman/`。

| # | 声明及固定位置 | 实际语义核查 |
|---|---|---|
| 1 | `smooth_first_taylor_integral` — `Spatial/SmoothAveragedTaylor.lean:16` | PASS；全空间 C² 的真实一阶 Taylor 余项，等于 `(1−t)D²f(y+t(x−y))[x−y,x−y]` 在 [0,1] 的积分。实际调用 n=1 的高阶 Taylor 积分定理，阶数、方向和系数均正确。 |
| 2 | `integral_convex_segment_jacobian_le` — `:28` | PASS；0<r≤1、x∈K、凸 K、非负可积标量函数下，实际收缩像积分界带精确 `r⁻ᵈ` 因子。利用真实仿射换元和像集包含 K，不预设目标积分估计。 |
| 3 | `convex_segment_norm_integral_sq` — `:42` | PASS；任意 NormedAddCommGroup 值连续 F，实际 K 上 Cauchy–Schwarz 和上一条给 `I_r²≤|K|r⁻ᵈ∫_K‖F‖²`。紧性供应真实有限测度和可积性。 |
| 4 | `convex_segment_lowdim_kernel_bound` — `:65` | PASS；在 `d≤3`、0<r≤1 下，正确使用 `r³≤rᵈ`，得到 `r I_r≤sqrt(|K|∫‖F‖²)/sqrt r`。所有平方和除法都在相应非负/正条件下执行。 |
| 5 | `integrableOn_unit_inv_sqrt` — `:89` | PASS；在真实 Lebesgue 限制测度 `(0,1]` 上识别为 `r^(−1/2)`，实际证明可积，不把奇异核当作连续函数。 |
| 6 | `integral_unit_inv_sqrt` — `:98` | PASS；相同区间和相同函数的积分精确等于 2；指数 −1/2>-1，端点处理合法。 |
| 7 | `convex_segment_lowdim_integral_bound` — `:109` | PASS；实际连续参数积分的被积函数可积，并与已证可积奇异核比较，得到 `2 sqrt(|K|∫‖F‖²)`。 |
| 8 | `smooth_first_taylor_contracted` — `:129` | PASS；以 r=1−t 精确变换第 1 项，余项为 `∫_[0,1] r D²f(ry+(1−r)x)[x−y,x−y] dr`，区间方向和符号无误。 |
| 9 | `smooth_taylor_remainder_norm_bound` — `:148` | PASS；实际多线性算子范数给 `|D²f[h,h]|≤‖D²f‖‖h‖²`，用真实位移界 `‖x−y‖≤D` 控制为 D²；没有改用 Hessian 上确界。 |
| 10 | `convex_smooth_averaged_taylor_error` — `:174` | PASS；对任意闭凸紧 K 和每个 x∈K，实际二阶余项在 y 上平均，经有可积性证明的 Fubini 得 `||K|f(x)−∫_K[f(y)+Df(y)(x−y)]|≤2D²sqrt(|K|∫_K‖D²f‖²)`。该未归一化式无需正体积假设。 |
| 11 | `averagedTaylorPolynomial` — `Spatial/SmoothH2NodalError.lean:14` | PASS；构造实际 `AffineMap`：常数项为平均 `f(y)−Df(y)y`，线性部分为平均 Df 的连续线性映射，锚点为 0。 |
| 12 | `averagedTaylorPolynomial_apply` — `:19` | PASS；紧 K 和全空间 C¹ 下，Bochner 积分与实际连续线性求值交换，得到该多项式的值精确等于平均一阶 Taylor 表达式。 |
| 13 | `averagedTaylorPolynomial_error` — `:35` | PASS；显式正体积下合法除以 |K|，在全部闭集点得到同一平均多项式的误差界；D 是实际两点距离的统一上界。 |
| 14 | `simplexNodal_smooth_h2_value_error` — `:51` | PASS；满维实际单纯形内部非空给正有限体积；使用同一多项式及实际仿射再现/非负重心坐标，把误差因子从 2 变为 4，覆盖整个闭单元及全部顶点。 |
| 15 | `simplexNodal_smooth_h2_value_integral` — `:69` | PASS；实际误差平方连续且可积，平方第 14 项并对 K 积分，精确消去体积，得到 `16D⁴` 乘实际 Hessian 平方积分。无形状参数、节点数或体积残留因子。 |

固定 `axioms.txt` 中完整类型依次从第 25227、25233、25246、25259、25273、25275、25277、25288、25294、25302、25319、25322、25330、25348、25364 行开始，均附实际递归公理记录。

## Taylor 公式、真实 Jacobian 与维数条件

独立核对锁定 mathlib 的 `map_add_eq_sum_add_integral_iteratedFDeriv` 实际类型：取 n=1，零阶和一阶项分别为 f(y)、Df(y)(x−y)，余项系数为 1/1!，核为 1−t，二阶张量沿同一位移求值两次。公式本身没有漏掉额外的 1/2；二次函数中的该系数来自核的积分。随后 `integral_comp_sub_left` 完成 r=1−t 的真实换元，Icc/Ioc 的差异通过 Lebesgue 单点零测度消去。

核对 `AffineChangeVolume` 与 `ConvexSegmentIntegral`：真实映射 `Φ_r(y)=ry+(1−r)x` 的线性部分为 r·Id，行列式绝对值为 rᵈ，因此

`∫_K g(Φ_r(y))dy = r⁻ᵈ ∫_{Φ_r(K)} g(z)dz`。

不是相反方向的 rᵈ。0<r≤1 和 x∈K、K 凸给 `Φ_r(K)⊆K`，非负性允许扩大积分域。这里没有要求 x 位于内部，因此后面直接适用于单元顶点和边界。

实际 Cauchy–Schwarz 以常函数 1 和 `‖F∘Φ_r‖` 为对象，因而得到体积因子 |K|，不是单元直径或人为能量。记 `A=|K|∫_K‖F‖²`、`I_r=∫_K‖F∘Φ_r‖`。从 `rᵈI_r²≤A` 和 `r³≤rᵈ` 得 `(r I_r sqrt r)²≤A`；对非负量取根并除以正 `sqrt r`，正是第 4 项。维数限制在这一处实质使用；没有宣称 d≥4 时相同论证仍可积。d≤3 覆盖原 P1 的 d=2,3，并允许低维边界情形。

## 可积性、奇异端点与平均多项式

`hf : ContDiff ℝ 2 f` 给实际 `iteratedFDeriv ℝ 2 f` 连续。其范数平方在紧 K 上可积，因此右端确实是有限的 L² Hessian 量，不存在以 Lean 对不可积函数积分的默认值代替实际估计的问题。

在 `(0,1]` 上，`1/sqrt r` 与 `r^(−1/2)` a.e. 相等，使用指数 −1/2>-1 的实际可积性与幂函数积分公式给出积分 2。r=0 的仿射映射不作可逆换元，也不在该点除以 sqrt r；同时实际余项核 `r‖F(ry+(1−r)x)‖` 在闭区间上连续。证明始终区分实际连续核与可积奇异控制核。

Fubini 使用明确的联合函数 `G(y,r)=r‖F(ry+(1−r)x)‖`。它在紧乘积 `K×[0,1]` 上连续，源码先证明它对 `(volume.restrict K).prod (volume.restrict [0,1])` 可积，再调用 `integral_integral_swap`。内外积分换序不是未经验证的形式操作。平均 Taylor 表达式及其余项也分别由连续性和紧性证明可积，积分的减法、常数提出和单调比较都有实际资格。

设 V=|K|。实际多项式为

`p(x)=V⁻¹∫_K[f(y)−Df(y)y]dy + (V⁻¹∫_K Df(y)dy)(x)`。

Df 的积分是连续线性映射空间内的 Bochner 积分，`ContinuousLinearMap.integral_apply` 合法交换它与求值，故 p(x) 精确等于 `V⁻¹∫_K[f(y)+Df(y)(x−y)]dy`。多项式不是假设存在的最佳逼近，也没有随 x 选择不同 p。

## 闭单元节点、常数与体积抵消

对实际 `Affine.Simplex ℝ (SpatialCoordinates d) d`，仿射独立性和满维性给非空内部，Lebesgue 开集正测度给正体积，紧性给有限体积。第 14、15 项在内部自行证明 `0<V<∞`，并不要求用户另供可能失真的单元质量。一般凸集版本归一化误差所需的 `V>0` 则明确出现在其类型中。

独立核对 `SimplexNodalInterpolation`、`SimplexNodalRemainder`：`I_K` 是原真实重心坐标的节点插值，坐标在闭单元内非负、和为 1，且对每个真实仿射多项式精确再现。若 `|f−p|≤R` 在 K 全部点成立，则各顶点也满足该界，故 `|I_K(f−p)|≤R`，从而 `|f−I_Kf|≤2R`。不需要在任意 L² 类上评估顶点，也没有把“几乎处处”偷换为点态。

取 `H=∫_K‖D²f‖²≥0`，第 13 项给 `R=2D²sqrt(VH)/V`，第 14 项给 `C=4D²sqrt(VH)/V≥0`。最后使用实际误差平方可积性和非负平方比较得到 `∫_K(f−I_Kf)²≤VC²`，并严格算出

`V·(4D²sqrt(VH)/V)² = 16D⁴H`。

V 的分母由 V>0 合法抵消，sqrt(VH) 的平方由 VH≥0 合法化简。常数 **16** 对全部单纯形位置、形状、体积、函数及 D 统一；没有 Hessian 上确界或网格基数因子。这个值误差界不需要内球形状条件；本批没有因此宣称后续梯度界也不需要形状条件。D=0 不被除掉，维数零及空/零体积一般凸集的前置未归一化结论均无除零问题。

## 依赖版本与公理

两新模块的递归 `Carleman.*` 导入闭包共 **97** 个源码文件，其中 **95** 个既有文件与基线逐字不变。关键指定依赖另与其原验收版本逐字比对：

- C088：`ConvexSegmentIntegral.lean` 与 `36c57dbc4edf3d9671f7b00f8c0675230f6b4380` 一致。
- C075：`SimplexNodalRemainder.lean` 与 `daf0c9e455f04bf5d7eff4e4ecde1729e01f6a92` 一致。
- C031：`RealL2Integral.lean` 与 `9f8e351a71cbcd8943db0d9056afdd2bc0a1ffe7` 一致。

上述依赖的实际证明已阅读；没有仅凭旧状态标签认可。新模块顺序为真实 Taylor/换元/平均界，再到实际节点误差，未调用后续弱 H² 或梯度结论，无循环清偿。

固定根目标 `Carleman.lean` 导入两模块。新源码无 `sorry`、`admit`、`axiom`、`native_decide`。三份治理文件、原稿、工具链和 mathlib 锁定文件与基线一致；全环境递归公理审计实现未改。原稿 SHA256：`492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

实际原始产物中的 15 项清单完整。全文件有 2227 个带公理打印记录（2223 个不同名称）及 8 个无公理记录，所有出现的依赖仅为 `propext`、`Classical.choice`、`Quot.sound`。打印记录数不等于全环境总数；最终递归审计明确通过 **6577** 个 Carleman 声明，无非基础公理。

## 同 SHA CI 与原始产物

独立核对 [main CI run 39199243542 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39199243542/attempts/1)。该 main/push 运行的 `head_sha=c8377e5f743689641ab84d5049b4d0fb291d29f5`，最终 **completed/success**，API `updated_at=2026-10-19T04:27:52Z`。

| Job | ID | 最终状态 |
|---|---:|---|
| `lean` | 117888577195 | completed / success |
| `state-check` | 117888577362 | completed / success |
| `dashboard / snapshot` | 117889556298 | completed / success |

验收者自行通过 `gh run download` 下载：

- **12163126814**，`lean-ci-result` → `/tmp/carleman-p1-h2-nodal-main-ci/result.json`。
- **12162633160**，`lean-declaration-evidence` → `/tmp/carleman-p1-h2-nodal-main-axioms/axioms.txt`。

实际 `result.json` 为 `status=PASS`，`checked_sha` 与 `source_head_sha` 均为完整固定 SHA，目标 `Carleman`，`finished_at=2026-10-19T04:26:25.057669+00:00`。Lean **4.35.0**，Linux 构建提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib **56a005855ea17e0b0958f73ec801ae140b0a1679**，与固定锁定及本次阅读的 mathlib 源码一致。

远端原始 `axioms.txt` 与固定 `/tmp/carleman-p1-h2-nodal-local-axioms.txt` 独立逐字节比较完全一致：**1,955,924 bytes**；SHA256 **`d8316745f0ccde509794ed84809143537f822124d8aacd34c46c1bda16ec5355`**。

固定 `-target.log` 实际记录定向 **3269 jobs** 成功；固定 `-full.log` 实际记录全库 **3836 jobs** 成功及 **6577** 项递归审计通过。未以工作树后续产物替换固定证据。

## 最终判定

**15/15 PASS，无需修复的数学、积分资格、类型、常数、依赖或版本绑定缺陷。** 本批真实完成 d≤3 的光滑局部节点值误差平方积分界及其完整平均 Taylor 证明。

C128 保持 **AUXILIARY**。全弱 H² 状态、弱 Hessian 分量识别、梯度误差、全局边界适配和允许权估计不在本次完成范围；原文覆盖仍为 **14/26**，P011 不提升。
