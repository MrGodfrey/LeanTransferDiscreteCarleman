# T201 / C217 独立本机验收

- checked_sha: `cf2701d48ac60007502c1ad44286c1d64b1303ce`
- base_commit: `a081c61839658c2869ef6a01e7bcd387a81b9af4`
- reviewed_at: `2026-10-20T03:24:52+00:00`
- reviewer: independent local Agent `/root/accept_spatial_lemma`
- result: **PASS — 19/19 显式声明（4 个定义、15 个定理），无阻断数学缺陷**
- axiom_check: **PASS**
- scope: **AUXILIARY；17/26 不变，P021 不提升**
- evidence_source: **local**；采用固定提交的实际本地构建和公理审计，不查询或声称远端 CI 成功。

已直接读取固定 Git 对象中三个新模块的全部类型与证明、相关实际依赖、T201 分析、MATH_SPEC 和任务记录。原稿实际对应 `paper/main.tex:2403–2415`，其中 H 连续时间迹及端点识别一句在 **2415 行**。固定分析及 claim 引用的 2420–2421 行已进入 spectral-comparison remark，是非阻断的行号定位错误，本报告按实际原文核验。原稿 SHA256 仍为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

## 逐声明核查

模块路径均为 `Carleman/Control/`。以下名称均带 `Carleman.` 前缀；每项已与固定 raw 的展开类型和公理输出对应。

| 模块 | 声明 | 结论及实际核对点 |
| --- | --- | --- |
| PositiveMassRegularization | `positiveMassForm` | PASS；实际连续双线性形式 Bε(v,w)=〈Mv,w〉+ε〈v,w〉。 |
| 同上 | `positiveMassForm_coercive` | PASS；非负配对及 ε>0 内部给出强制常数 ε，无对称性要求。 |
| 同上 | `positiveMassInverse` | PASS；实际 `variationalSolve` 与 Riesz 映射复合构造连续线性 Rε，没有输入逆算子。 |
| 同上 | `positiveMassInverse_equation` | PASS；全 w 变分身份与内积外延性给 (M+εI)Rεx=x。 |
| 同上 | `positiveMassInverse_left` | PASS；变分解唯一性给 Rε(M+εI)x=x。 |
| 同上 | `positiveMassInverse_commute` | PASS；由上述左右逆及线性得 RεM=MRε，未另假设交换。 |
| 同上 | `positiveMassRegularizer` | PASS；定义恰为 Qε=MRε。 |
| 同上 | `positiveMassRegularizer_norm` | PASS；令 z=Rεx，以 Mz 配对方程得 ‖Qεx‖≤‖x‖。 |
| 同上 | `positiveMassRegularizer_residual_norm` | PASS；真实残差 x−Qεx=εz，以 z 配对并合法处理 z=0 得残差收缩。 |
| 同上 | `positiveMassRegularizer_range_error` | PASS；实际交换式给 Mx−QεMx=εQεx，故误差≤ε‖x‖。 |
| MassRegularizerStrong | `positiveMassRegularizer_strong` | PASS；明确输入一般 M 的稠密值域，以 range 误差和残差收缩推广至每个 x；不是算子范数收敛。 |
| 同上 | `adjoint_mass_denseRange` | PASS；任意单射有界 E 的真实质量 M=E*E 满足 M*=M、ker M=ker E=0，正交核身份给稠密值域。 |
| 同上 | `compLpL_strong_of_contractions` | PASS；真实 Lp 代表的平方误差由 4‖Y(t)‖² 支配，DCT 给实际 compLpL 的 L² 强收敛。 |
| DirichletMassRegularization | `dirichletTimeMass_nonneg` | PASS；实际 E*E 配对等于 ‖Ev‖²，非负性内部清偿。 |
| 同上 | `dirichletTimeMass_dense` | PASS；原 Sobolev 值注入性供应 E 单射，再调用上面的稠密值域结论。 |
| 同上 | `dirichletMassRegularizer` | PASS；使用原 H¹₀ 完备结构及真实 M，实例化所构造的 Qε。 |
| 同上 | `dirichletMassRegularizer_norm` | PASS；对所有完整 H¹₀ 状态、所有 ε>0 的能量收缩常数为 1。 |
| 同上 | `dirichletMassRegularizer_strong` | PASS；原 M 的非负性与稠密性均内部供应，任意正 εn→0 对每个完整 H¹₀ 元素强收敛。 |
| 同上 | `dirichletMassRegularizer_bochner_strong` | PASS；对所有原 H¹₀ 值 Bochner L² 状态，真实 compLpL 强收敛；无逐时间正则性输入。 |

## 数学忠实性与条件边界

**实际逆和收缩。** `variationalSolve` 使用 mathlib 的真实 Lax–Milgram 连续线性等价之逆及 Riesz 逆映射，其 spec 和唯一性均已直接检查。一般 M 只需在实 Hilbert 空间上有界线性且 〈Mv,v〉≥0；不要求 M 可逆、自伴、有限维或有闭值域。对 z=Rεx，方程是 Mz+εz=x。测试 Mz 后，交叉项 ε〈z,Mz〉非负，Cauchy–Schwarz 给 Qε 收缩；测试 z 给 ε‖z‖≤‖x‖，零向量分支显式处理。range 误差由同一个 Rε、M 的实际交换式产生，没有把目标估计作为假设。

**强收敛的量词。** 一般 `positiveMassRegularizer_strong` 的 `DenseRange M` 是辅助定理的明确条件。先在真实 range 上用 εn‖v‖→0，再对任意 x 选距离小于 δ/2 的 Mv，以 I−Qε 的收缩控制剩余项。没有输入 Qε 的强极限，更没有推断 ‖I−Qε‖→0。参数序列只要求每项严格正且趋零，不要求单调、ε≤1 或与网格耦合。

**原 H¹₀ 实例不残留稠密性前提。** `dirichletTimeMass` 展开确为原值映射 E 的 E*E。V 是 `DirichletEnergyState S`，继承原弱 H¹ 图内积；其完备性来自原测试闭包，E 单射来自开放域上的完整弱 jet 值唯一性。质量稠密性使用的是 V 中 E*E 的 range，而非误用 E 在 H 中的稠密性。实际 `ker_adjoint_comp_self` 和 `orthogonal_ker` 均为无限维 Hilbert 定理，未偷偷引入有限维性。最终只要求 S 开，不要求 S 有限体积、有界或边界光滑；d=0、空域未被排除。原控制问题的有界开盒当然满足这些条件。

**真实 Bochner 范数。** 一般提升引理适用于任意测度 μ，不依赖有限测度。Y∈Lp V 2 μ 先给出 ‖Y(t)‖² 可积，连续算子作用保持强可测性。收缩及三角不等式逐点给
`‖Ln(Y(t))−Y(t)‖² ≤ 4‖Y(t)‖²`；
对每个 v 的强收敛可直接用于所选代表的每个 Y(t)，无需交换不可数个 a.e. 量词。DCT 之后，`Lp.coeFn_sub`、`coeFn_compLpL` 和实际 L² 内积公式把积分精确识别为 `‖Ln.compLpL Y−Y‖²`，最后通过平方根连续性得到范数收敛。不存在用未证明可积性的积分默认值或忽略 a.e. 代表的问题。

最终 Dirichlet Bochner 声明对任意实 T 的 `volume.restrict (Ioc 0 T)` 成立；T≤0 的零时间测度亦合法，原应用取 T>0。收缩常数 1 与状态、ε、T 无关；强收敛是每个给定状态的结论，没有声称统一收敛率。本批尚未把质量弱导数转化为原状态的 H 一致时间极限，亦未证明连续代表或初终端身份；不能从 MY 的 V 连续性直接推出 Y 的 H 连续性。

## 固定依赖与本地执行证据

已全文读取并核对 T200 冻结报告 `0c0f916331bfc3b9b8de33c6cea3c4c74eaade7c:governance/reviews/T200-local-acceptance.md`（15/15 PASS），其当前文件与提交逐字节相同。新模块的 Carleman 递归源闭包共 **409** 文件，其中 **406** 个旧文件相对数学基线全部 Git blob 相同。直接重读了 `FormSolve`、`DirichletTimeLoad`、`ConformingHilbert`，并核对完整能量空间及其值映射相关闭包。另读取 mathlib 的 LaxMilgram、Adjoint、DominatedConvergence 所需实际定理；三个本地文件均逐字节匹配固定 mathlib 提交。

独立读取 `/tmp/carleman-t201-local-evidence.json`，`checked_sha=source_head_sha` 均为本报告 proof SHA，`status=PASS`、`source=local`，完成时间 `2026-10-20T03:21:57.900009+00:00`。真实记录中 `lake build Carleman` 和 `lake env lean tools/CheckAxioms.lean` 均 exit 0。本次验收核对执行证据及其源码关联，没有声称再次执行全库构建。

| 固定本地证据 | 独立核验 |
| --- | --- |
| `/tmp/carleman-t201-target-build.log` | 三新模块实际完成，3611 jobs；257 bytes，SHA256 `c756d2f24e2bbc4fb4701374fa0e6071ec179e6c3d046d4421c994f63313a404`。 |
| `/tmp/carleman-t201-build.log` | 根目标实际完成，4202 jobs；80 bytes，SHA256 `26725cbc87435ccebd63524c34cfd68774635b0fa618245d55ec8dfdee4a5543`。 |
| `/tmp/carleman-t201-axioms.log` | 0 bytes，stderr 为空。 |
| `/tmp/carleman-t201-mass-regularization-local-axioms.txt` | 2,919,749 bytes；SHA256 `46e16af9bec0291d1465c207074a7ba2670c7c2a599128aeb0ae2312a3c746a1`；末行确认 **8909** 项全命名空间递归审计通过。 |
| `/tmp/carleman-t201-local-source-manifest.txt` | 104,844 bytes；SHA256 `b943167afc1d43715f7cab0561591efc9f76c1919dcb6e52c46316d135e2f355`。逐项枚举固定 Git 树，全部 tracked Lean 文件与三项工具链配置共 **967** 项；集合精确、无重复，每项内容摘要均与 proof blob 一致。 |

已核对全部 19 项根导入、`#check @...`、`#print axioms` 及 raw 展开类型（固定 raw 第 38093–38181 行附近）。每项仅依赖 `propext`、`Classical.choice`、`Quot.sound`。全部 3475 条显式依赖列表无白名单外项，另有 9 条明确不依赖任何公理的输出；另直接读取固定审计循环，确认 `privateToUserName` 后遍历完整 Carleman 命名空间，并以 `collectAxioms` 递归检查私有及生成声明。8909 为实际全局审计数。Lean 4.35.0、compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`、mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 与固定配置及证据一致。

**签发结论：C217 本阶段可按 AUXILIARY 接受，19/19 PASS。** 原文定位偏差仅属文档问题；H 连续时间迹和端点识别仍待，P021 及 17/26 覆盖数不变。本报告签发后冻结时间与正文，仅单文件提交，不修改数学、台账或原稿。
