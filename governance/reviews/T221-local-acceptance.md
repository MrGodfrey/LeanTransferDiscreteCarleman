# T221 / C237 独立本机验收

- checked_sha: `e9e50330857e19ec60f3f65e664f9b240029fdcc`
- mathematical_base: `1d10859fce3c68f87f9f5e7e166f41e3c90d60c5`
- reviewed_at: `2026-10-20T05:42:40+00:00`
- reviewer: 独立本机 Agent `accept_spatial_lemma`
- result: **PASS，4/4 定理，无阻断缺陷。**
- scope: **AUXILIARY；C237 可在此范围验收，原文 17/26 不变。**

已直接读取固定 Git 对象中 `HigherWeightedCoercivity.lean` 全部代码、四项完整 raw 类型/公理、固定分析/MATH_SPEC，核对原稿 `paper/main.tex:2637–2652` 的吸收步骤及 `eq:unshiftedcoercive`（371 行）的真实结论。本批由原 coercivity 得出实际允许权的统一形式下界；尚不包含一般 W^{2m,∞} 系数的算子交换子，也不因此提升完整 Proposition A.1。

## 数学审查

1. **原完整 H₀ᵐ 的实际乘后状态。** `HigherDirichletEnergy S m` 是原测试全阶 jet 的 Hᵐ 闭包对应的完整 Hilbert 实现，并非光滑核心或人为加权子空间。已直接读 `HigherDirichletSpace`、`HigherDirichletProduct` 和 `conformingEmbed_range`：域内光滑有界乘法是实际全阶弱乘积 CLM，原测试乘法及连续性保持该闭包；真实零阶嵌入值域恰是原 `higherDirichletSubspace`。第一定理据此从任意 u 构造 z∈H₀ᵐ，实际 L² 值等于 wu，而非将乘后射流存在性作为输入。所有高阶字段属于同一弱射流，由零阶值及弱导数唯一性识别。最终定理连续调用两次该构造，内部得到 z=w²v；中间下界定理还适用于任意满足这一零阶身份的已有 z。
2. **原 SmoothOnClosure，非域外延拓。** 已重读其定义：ρ 在闭包连续、域内 C∞，各真实域内迭代导数各有连续到闭包的延伸；不要求域外光滑。`boundedSmoothOn` 通过原有界域的紧闭包，对有限阶导数取共同界。后续实际词导数只在开域内部计算，受限 Lebesgue 测度集中于 S，故没有对任意域外代表或边界处的全空间导数施加额外要求。乘子可测性和有界性由 `intrinsicWordMultiplier` 从这些域内数据构造。主结论的 `w : BoundedMultiplier` 及精确指数值身份是原权的实现接口，不是额外权导数假设；同一构造的空词也提供该实际 w，故接口不空泛。
3. **逆权、双符号和统一相对导数。** 对所有 q≥1、τ∈ℝ、|eta|=1，实际 ξ 构造为 `q^(−τ) exp(q((−eta)ρ))`。`Real.rpow_neg` 及指数互逆严格给 wξ=1，q>0 保证无零除。两侧估计分别用 τ/eta 与 −τ/−eta 的同一个已证 `allowedWeight_word_uniform`，再以正的另一权乘回，得到 `|ξ D^l w|`、`|w D^l ξ|≤J q^|l|`。J>0 在 q、τ、符号、乘子元数据及全部状态之前选择；并不使用 w/ξ 各自可能很大的绝对 sup 界。无 τ_* 限制的结论包含原有限允许指数族，且没有 T、网格或 qmax 依赖。零阶词也覆盖；没有自行指定导数或将导数界输入给最终定理。
4. **真实系数形式误差和吸收方向。** 形式为全部 `|α|,|β|≤m` 的原积分和，包含低阶及非对角系数。已直接核对 `higherCoefficientForm`、`coefficientJetForm_smooth_conjugation_error` 与其实际逆权配对。令 u=wv、ju 为其原 jet、L=lower(q,ju)、R=parameter(q,one,ju)，由 ξw=1 得 v.value=ξu.value，由给定/构造的平方权身份得 z.value=wu.value；两侧与 T220 方向完全一致。因此实际 `|a(v,z)−a(u,u)|≤B L R`，其中 A=Σαβ bound(aαβ)、K=2^mJ、B=A K(K+2)≥0。系数只需有界可测性及原 coercivity；对称性和系数导数不是该下界步骤所需，不是被错误推导或替换为光滑系数。
5. **小常数、正性和完整 Hᵐ 范数。** 固定原 c₀>0 后，取 B₁=1+B>0、δ=c₀/(2B₁)>0；T219 给 `LR≤δ‖ju‖jet²+E(q^m‖u‖₂)²`，E≥1 仍先于 q/u。真实 jet 积范数≤实际 Hilbert Hᵐ 范数 H=‖u‖，没有等同两者。因 L,R≥0，B≤B₁ 的放大方向正确；B₁δ=c₀/2，误差于是≤c₀H²/2+B₁E M²（M=q^m‖u‖₂）。利用绝对值界的负方向和原 `a(u,u)≥c₀H²`，准确得到 `a(v,z)≥c₀H²/2−B₁E M²`。没有把最终加权估计、额外状态预算或正则性作为输入，且 B=0 时不除以 B。
6. **N 范数与原质量余项。** 先用真正平方和 N≤参数和，再用既有双向权共轭的正确反向分量，得 `N(q,w,v)≤D R`；原域参数插值给 R≤I(H+M)。D>0、I≥1 都在参数/状态之前固定，因此 `N²≤G(H²+M²)`，G=2(DI)²>0。取 c=c₀/(2G)>0、C=B₁E+c₀/2>0，将这一比较代入上一步恰得 `cN²−CM²≤a(v,z)`。由同一 u 的实际零阶身份，M=`q^m w.seminorm(v.value)`，平方即原 `q^(2m)‖wv‖₂²`。不存在丢失的维数因子、逆权方向或质量指数。最终量词精确为固定 S/ρ/a/coercivity 后 `∃c,C>0 ∀q≥1 ∀τ ∀|eta|=1 ∀w ∀v ∃z`；没有任何状态、网格、时间或权元数据进入常数选择。
7. **退化和范围。** m=0 的低阶项为空，所有常数分母仍由原 c₀、B₁、D、I 保证合法；q=1、零状态、空域/零测度和 d=0 不触发额外非空/正体积前提。原论文 d,m≥1 为此声明的子范围。最终正、逆权均保留原 H₀ᵐ 状态；没有声称关联算子域身份、一般弱系数乘法或完整 A.1 已被此形式估计清偿。

## 四项完整声明

源码行相对于固定 `Carleman/Spatial/HigherWeightedCoercivity.lean`，raw 行相对于下列固定公理文件。每项实际类型和证明均已检查。

| 声明 | 源行 / raw 行 | 结论 |
|---|---:|---|
| `Carleman.higherDirichlet_smoothProduct_exists` | 17 / 40725 | PASS；完整原 H₀ᵐ 中实际乘法存在，保持真实零阶 L² 值。 |
| `Carleman.allowedWeight_inverse_relative_uniform` | 31 / 40734 | PASS；内部构造逆权及两侧实际相对词导数统一界；通用 ν 的集中条件明示。 |
| `Carleman.higherCoefficientForm_allowedWeight_lower` | 81 / 40762 | PASS；原 coercivity 和真实共轭误差内部吸收，对任意同值平方权状态成立。 |
| `Carleman.higherCoefficientForm_closure_weighted_coercivity` | 190 / 40796 | PASS；原闭包光滑性供应全部权资格，内部构造平方权成员并得统一原下界。 |

## 固定依赖与本地证据

T220 冻结报告 `6b2e214345ec21a1553d0359485a1990607d6d13` 已全文读取（checked_sha 为本批数学基线、reviewed_at `2026-10-20T05:31:08+00:00`，15/15 PASS）。本批实际导入闭包 143 个模块，其中 142 个旧模块与基线逐 Git blob 不变；仅新增被审模块。关键调用仍直接读取源码，并比对对应已验收版本：域插值和 intrinsic 权结论四模块与 `a315bdc449c58a705a982f0d009f1dde24d6af66` 不变，高阶弱乘积两模块与 T217 不变，真实系数形式两模块与 T218 不变，小常数模块与 T219 不变，余项两模块与 T220 不变。未混入后续 T222 工作树或动态审计文件。

- 本批证据来源为 **local**。`/tmp/carleman-t221-local-evidence.json` 为 PASS，checked/source 均精确等于完整 proof SHA，finished_at `2026-10-20T05:39:20.960088+00:00`；实际 `lake build Carleman` 和 `lake env lean tools/CheckAxioms.lean` 均记录 exit 0。本次独立审核真实执行记录及源码绑定，不声称重新执行全库或检查远端 CI。
- 独立枚举固定提交所有 tracked Lean 文件及三项构建配置，与 `/tmp/carleman-t221-local-source-manifest.txt` 核对路径集合、唯一性及全部 Git blob 字节 SHA256：**1011 项全部一致**。清单 109673 bytes，SHA256 `214fbd66e3a265bba559e8aee18424a3d32af06fc399bfacaf777ac513d7057f`。
- `/tmp/carleman-t221-target-build.log` 为 **3303 jobs** 成功，112 bytes，SHA256 `f09b4b583d5a9a7ced21e696f01311a7ab6ae66366ab21685919bbb1ddc3e54c`；全库 `/tmp/carleman-t221-build.log` 为 **4247 jobs** 成功，80 bytes，SHA256 `786316cf130b4ffb8506d44979dbd80adb50ae7a0456607d1649b0716a10877b`。`/tmp/carleman-t221-axioms.log` 为 0 bytes。
- 固定 raw `/tmp/carleman-t221-weighted-lower-local-axioms.txt`：**3133426 bytes**，SHA256 `63af521350768197fab1eb6426e2af8d7dc8f9c6e8e47e12166d60562992f5e3`。四项完整展开类型逐项检查；全部 3635 个非空公理列表及 10 个无公理记录已扫描，只有 `propext`、`Classical.choice`、`Quot.sound`，无 sorryAx 或新增数学公理。固定审计工具以 `privateToUserName` 遍历 Carleman 命名空间并递归 `collectAxioms`，禁止白名单外公理；原始末行确认 **9289 声明递归审计 PASS**。根导入新模块，四项显式 #check/#print axioms 齐全；递归审计循环未改。
- Lean 4.35.0（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）、mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 与固定构建配置一致。原稿 SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef` 未变。

没有需要修复的数学或证据缺陷。本报告只接受该真实允许权形式下界，保持 AUXILIARY / 17 of 26。签发后正文与 reviewed_at 冻结；仅单文件提交报告，不改数学、台账、根导入、原稿，不 push。
