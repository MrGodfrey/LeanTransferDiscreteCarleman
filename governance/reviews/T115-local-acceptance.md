# T115 / C131 独立本机验收

- `checked_sha`: `f134750df6b8ef03c639f50dd5084d4c42d49272`
- `base_commit`: `a5c68e2aaa4da98efe42da31ed0c1da04ba99952`
- `reviewed_at`: `2026-10-19T04:51:03+00:00`
- `reviewer`: `/root/accept_section3`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 验收范围：一般实标量 L² 强收敛准则、实际缩小卷积核的强 L² 收敛，以及原全部弱 H² jet 在任意内部紧集上由同一 C∞ 卷积序列实现的值、一阶和二阶分量强收敛。**P011 不提升，原文保持 14/26。**

本 Agent 直接读取固定 git 对象的四个完整模块、10 项实际展开类型、关键调用依赖与原稿 Section 6 P1 Step 2（`paper/main.tex:1523–1548`），并读取固定 AGENTS、PROJECT_OPERATIONS、state 协议、MATH_SPEC 和 T115 分析。执行者说明及 CI 均未替代数学核查。metadata 提交、变化中的工作树和 `.ci/axioms.txt`、后续 SmoothH2PointBound 等模块不属于本报告依据。

## 全部 10 项声明

以下名称省略公共前缀 `Carleman.`；模块位于 `Carleman/Spatial/`。清单与固定提交 C131、T115 以及 `/tmp/carleman-strong-h2-declarations.json` 逐项一致。展开类型所在行为固定本地及远端相同的 `axioms.txt` 行号。

| # | 声明 | 固定源码 | 展开类型行 | 独立结论 |
|---|---|---|---|---|
| 1 | `l2_square_tendsto_zero_of_ae_of_energy_le` | StrongL2Limit:14 | 25548 | PASS；任意测度上的实标量 L²，a.e. 收敛和逐项能量上界给真实平方误差积分趋零。 |
| 2 | `spatialMollifier_square_error_tendsto` | StrongMollifierLimit:17 | 25556 | PASS；实际卷积的 a.e. 收敛与 L² 收缩供应第 1 项的全部前提。 |
| 3 | `spatialMollifier_L2_error_tendsto` | StrongMollifierLimit:30 | 25566 | PASS；实际可积平方误差经非负平方根给真实 Bochner L² 误差趋零。 |
| 4 | `spatialMollificationLp` | StrongMollifierLimit:44 | 25575 | PASS；用已证明的 MemLp 构造同一卷积的真实 toLp 类。 |
| 5 | `spatialMollificationLp_ae` | StrongMollifierLimit:50 | 25578 | PASS；该 Lp 类的代表确实 a.e. 等于实际卷积。 |
| 6 | `spatialMollificationLp_tendsto` | StrongMollifierLimit:54 | 25583 | PASS；在原 Lp 范数拓扑中强收敛回任意输入类。 |
| 7 | `spatialMollifier_L2_error_restrict_tendsto` | LocalStrongMollification:16 | 25586 | PASS；限制测度的范数单调性给任意集合 K 上的强收敛。 |
| 8 | `IsWeakSpatialDerivative.local_mollification_strong_first` | LocalStrongMollification:26 | 25596 | PASS；内部支撑缓冲与原局部弱身份给实际 Fréchet 一阶方向导数的强收敛。 |
| 9 | `IsWeakSpatialDerivative.local_mollification_strong_second` | LocalStrongMollification:39 | 25616 | PASS；任意两个方向的原弱链识别真实二阶张量分量，并强收敛到原第二场。 |
| 10 | `WeakSobolevJet.local_mollification_strong_h2` | WeakH2LocalSmoothing:15 | 25637 | PASS；原完整弱 H² jet 自动提供全部链，同一序列同时覆盖值、d 个一阶与 d² 个有序二阶分量。 |

## 实际 L² 强收敛准则

第 1 项完整类型只要求任意可测空间、任意测度 ν、实值 f 和 Fₙ 属于真实 MemLp 2、Fₙ→f 几乎处处，以及每个 n 满足 ∫Fₙ²≤∫f²。没有有限测度、共同支配函数、预设弱收敛、紧支撑或光滑性假设；此项并未声称一般 Banach 值版本。

令 E=∫f²。证明中的积分平行四边形身份是

\[
\int(F_n+f)^2+\int(F_n-f)^2=2\int F_n^2+2E.
\]

加减两函数的 MemLp 和平方可积性先由输入得到，再合法拆分 Bochner 积分；不是对不可积函数使用积分默认值。非负性供应趋零判据的下界。若某 b>0 的误差上界不最终成立，`exists_seq_forall_of_frequently` 给出 φ:ℕ→ℕ，φ→∞ 且每项误差≥b；已核对该 mathlib 声明真实返回 Tendsto，足以将原 a.e. 极限传到子列，无需额外单调假设。

平行四边形身份和能量上界逐项给 ∫(Fφₙ+f)²≤4E−b。由非负积分与第 0 项先证 4E−b≥0，随后将实际极限 2f 及所有和函数的 MemLp 交给 `l2_square_bound_of_ae_tendsto`，得到 4E≤4E−b，与 b>0 矛盾。依赖 `PairwiseL2Limit` 已实际读取，其结论来自 mathlib `Lp.eLpNorm_le_of_ae_tendsto` 的 Fatou/liminf 证明；真实范数有限性与平方根换算均显式清偿，没有把待证强收敛作为前提。

## 实际卷积、范数与 Lp 类

第 2–6 项用同一 `spatialMollifier d n`，其核为实际归一化光滑 bump，内半径 1/(n+1)、外半径 2/(n+1)，非负、单位质量、外半径趋零且半径比恒为 2。已读取 `FullSpaceInterpolation.spatialMollifier_converges` 和固定 mathlib 的对应定理：a.e. 极限来自局部可积函数的 Lebesgue 微分定理；输入任意全空间 L² 类自动局部可积，不要求连续代表。

已重新检查 `ConvolutionL2`、`MollifiedInterpolation`：真实卷积积分通过带核平方根的 Cauchy–Schwarz 及卷积积分身份给平方能量收缩，并先证明真实 MemLp；实标量卷积交换性将结果用于源码的右卷积顺序。因而第 2 项所需 ∫(u⋆κₙ)²≤∫u² 确实来自同一实际核与输入，而非假设另一个有界近似族。

第 3 项先用卷积和 u 的 MemLp 得到差函数的 MemLp，再将真实平方积分识别为 `bochnerL2Norm` 的平方。连续平方根与范数非负性给误差范数趋零。第 4 项直接对该卷积的 MemLp 取 toLp；第 5 项是其真实 a.e. 代表身份。第 6 项同时使用 Lp 减法的 a.e. 身份与第 5 项，将原 Lp 范数差准确识别为第 3 项的误差，因此是原 L² 空间的强收敛，而非只有某代表的逐点收敛。

第 7 项不要求 K 开、闭或有限体积；限制测度≤原测度使真实 eLpNorm 减小。转换 `ENNReal.toReal` 时所需全空间误差范数有限性由 MemLp 供应，随后夹逼到零。不存在把无穷范数的 toReal=0 当作强收敛的问题。

## 局部支撑、真实导数及原全部弱 H²

第 8、9 项的额外几何前提精确为开 S、紧 K、K⊆S。`compact_mollifier_eventually_inside` 从紧集在开集中的正缓冲距离和实际外半径趋零，得到同一个最终阈值：对所有 x∈K 和所有 y∈tsupport κₙ，x−y∈S。该阈值只用于最终身份，有限多个初始核不影响极限；不是向调用者另索要支撑条件。

`IsWeakSpatialDerivative` 已展开为对全部真实紧支光滑 `SpatialTest S` 的分布导数身份。`DomainConvolution` 的反射测试 κ(x−y) 由支撑条件保证 admissible，其导数负号与弱分部积分负号相消。由此在 K 上识别真实 `fderiv`，再与 v 的实际卷积强收敛相接。域仍为 S，没有将局部弱身份改成全空间身份。

二阶结论调用的 `LocalHessianConvolution` 也已实际读取。它先把全局光滑卷积的 Dₑ₁(u⋆κ) 写成 u⋆Dₑ₁κ，再利用方向核支撑包含和第一条弱链 Dₑ₀u=v，随后用第二条弱链 Dₑ₁v=z。真实 `fderiv_clm_apply` 与 `iteratedFDeriv_two_apply` 得到

\[
D^2(u\star\kappa)(x)[e_0,e_1]
=D_{e_0}(D_{e_1}(u\star\kappa))(x)=(z\star\kappa)(x).
\]

没有对仅在单点成立的局部等式直接求导，也没有将候选张量定义成导数。任意两个方向均允许。所用弱链的次序与源码一致，光滑核上的交换步骤已有实际证明。

第 10 项接受任意 `WeakSobolevJet d 2 (volume.restrict S) S`，并固定

\[
U_n=(\operatorname{zeroExtendLp}(\mathrm{value}\,u))\star\kappa_n.
\]

所有 n 的 C∞ 性来自实际光滑紧支核与全空间 L² 输入。k=0 的原 jet 弱链供应每个 i 的值到 field₁ 分量；k=1 的链供应每个 i,j 的 field₁ 到 field₂ 分量。目标二阶分量准确为 `Sym.cons j (Sym.cons i Sym.nil)`，实际张量参数为 `[e_i,e_j]`。所有 d² 有序对都出现，含 i≠j；对称 multi-index 的重复对应没有漏掉混合项，也没有声称有序坐标范数与对称纤维范数精确相等。

已核对 `ZeroExtensionLp` 的定义、a.e. 身份及 `IsWeakSpatialDerivative.zeroExtend`：这是从原限制测度 L² 类到全空间 L² 类的实际指示函数延拓；它保留的弱身份仍只对 **S 内测试函数** 成立。最终 `hreplace` 将零延拓与原分量的 a.e. 身份沿 restrict K≤restrict S 限制到 K 后替换。未假定零延拓跨边界具有全空间 H¹/H² 正则性。

最终结论逐分量写强 L² 收敛，而不是额外构造一个 Sobolev 空间序列的抽象拓扑极限。该分量表述准确覆盖同一 Uₙ 的值及全部有限坐标；没有为不同分量选择不同子列。实际导数误差确实平方可积：Uₙ 的各阶导数连续且 K 紧，原分量是限制后的 L² 类。所有空间维数 d 允许，包括 d=0 时空的一阶/二阶索引族；K 为空、S 无界或不连通均未额外排除。不存在量词后移或依状态选择的另一平滑算子。

## 原文对应与范围边界

原 P1 Step 2 对任意 v∈D(A)⊆H²(Ω)，使用闭域连续代表定义真实全网格节点插值，并要求局部值/梯度估计、零边界适配及全允许权版本。本批独立清偿的是将原全部弱 H² 数据在**原域内部紧集**上由同一真实光滑卷积强逼近的步骤，可用于已验收光滑估计的内部极限论证。

K⊆开 S 是实质内部范围，不能自动用于接触 ∂S 的闭单元。L² 强收敛自身也不提供原弱类在顶点的点值或一致收敛。本批没有闭域连续节点代表、边界零值资格、全域 H² 稠密性、H¹₀ 插值资格或全局允许权求和结论；亦未给出对整个 Ω 的卷积 Hessian 强收敛。没有 T、τ、时间权或网格量词被偷偷限制，因为本阶段尚未声称那些最终结论。该范围与规格中的 AUXILIARY 一致，不能将其当作原完整 `eq:p1-interpolation`、`eq:p1-interpolation-energy` 或 P011 的 PAPER 验收。

## 固定依赖、构建与公理

四个新模块的 Carleman 导入闭包共 **101** 模块，除本批四模块外的 **97** 模块与 base 逐字节不变。进一步独立比较关键已验收版本：`LocalHessianConvolution` 的 53 模块闭包及 `MollifiedHessianEnergy` 的 61 模块闭包与 T114 的 base 一致；`DomainConvolution` 的 26 模块、`FullSpaceInterpolation` 的 49 模块、`PairwiseL2Limit` 的 46 模块、`InteriorWeakPoincare` 的 67 模块闭包，与已验收 `c99262c4a0d65a4d23f2efb57748bda490e971d7` 逐字节一致。相关记录见 [T114](T114-local-acceptance.md)、[T073](T073-local-acceptance.md)；本次另独立检查了其关键证明和实际调用。

AGENTS、运行/状态协议、原稿和工具链 pin 与 base 不变。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean 固定 4.35.0；mathlib pin 与本机实际 HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，本机 mathlib 工作树干净。本次直接读取了该版本的 Fatou、频繁子列和 bump a.e. 卷积极限证明。四个新模块均在固定 `Carleman.lean` 导入；新源码无 sorry、admit、额外 axiom 或 native_decide。

`tools/CheckAxioms.lean` 对本批 10 项输出完整类型和递归公理，末尾审计器与 base 不变，对全部 Carleman 常量（包括私有辅助、生成声明）逐个 collectAxioms，只允许 propext、Classical.choice、Quot.sound。固定证据逐项含上述 10 项的实际类型和正常三项基础公理；全文件 **2253** 条非空公理记录、**8** 条无公理记录均无不允许的公理。显式打印记录含重复，与全环境审计计数不同；真实末行是 **6617** 项全声明递归审计 PASS。

独立读取固定 `/tmp/carleman-strong-h2-target.log` 的 **3264 jobs** 成功，以及 `-full.log` 的 **3845 jobs** 成功和上述全量审计。固定本地产物 `/tmp/carleman-strong-h2-local-axioms.txt` 为 **1,975,813 bytes**，SHA256 **`19fa623ea0be6657f94b72e17ed570f0739857030a3ac99e1e6cc4f099656d57`**。

## 实际同 SHA CI 及原始产物

本 Agent 自行查询 [main CI 39201164238 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39201164238/attempts/1)：main/push，head SHA 精确等于本报告 checked_sha，最终 **completed/success**，run 更新时间 `2026-10-19T04:49:33Z`。以下三项均 independently queried completed/success：

| Job | ID | 最终结果 |
|---|---|---|
| lean | 117894233638 | success |
| state-check | 117894233904 | success |
| dashboard / snapshot | 117894928927 | success |

同 run 的 `lean-ci-result` artifact **12163991952**（归档 493 bytes）和 `lean-declaration-evidence` artifact **12164305711**（归档 181,830 bytes）元数据均绑定本报告 head SHA，且未过期。本 Agent 自行执行两次 `gh run download 39201164238`，均实际 exit 0，分别下载到 `/tmp/carleman-strong-h2-main-ci` 与 `/tmp/carleman-strong-h2-main-axioms`。

实际 `result.json` 为 **537 bytes**，SHA256 `4c8cc6022943620af70aa37fa3758350e0a35626a4a010c0f8e484c9e4a3a764`。内容为 PASS，`checked_sha=source_head_sha=f134750df6b8ef03c639f50dd5084d4c42d49272`，target 为 Carleman，`finished_at=2026-10-19T04:48:25.068490+00:00`，ci_url 为同 run/attempt。远端 Lean 4.35.0 的提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib 提交与固定 pin 一致。

远端原始 `/tmp/carleman-strong-h2-main-axioms/axioms.txt` 已与固定本地副本独立逐字节比较：**完全一致，1,975,813 bytes，SHA256 `19fa623ea0be6657f94b72e17ed570f0739857030a3ac99e1e6cc4f099656d57`**。远端实际末行同样为 6617 声明审计 PASS。原始结果、同版本类型与公理产物、全部 job 的最终成功均已分别核实。

## 验收决定

**C131：PASS，可升级 REVIEWED，scope 保持 AUXILIARY。** 10 项声明的数学对象、实际可积性、强收敛、局部支撑、真实导数、原全弱 H² 状态范围和依赖公理均通过独立核查，未发现需要修复的数学缺陷。同 SHA 三项 CI 与独立下载的原始产物证据通过。

**P011 不提升，原文仍为 14/26。** 本次只新增本报告，未修改数学实现、root、台账或原稿，未 commit/push。以上签发 UTC 固定；报告定稿通知主 Agent 后冻结，不再修改内容或 reviewed_at。
