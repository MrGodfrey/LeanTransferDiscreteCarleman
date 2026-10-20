# T228 / C244 独立本机验收

- checked_sha: `a914d2ede5d27b37e30708efaff64fdf1b783d2d`
- mathematical_base: `4573638d5529914e0140c25f4dfe3689be92afaa`
- reviewed_at: `2026-10-20T06:26:53+00:00`
- reviewer: 独立本机 Agent `accept_spatial_foundations`
- result: **PASS，30/30 显式声明（26 定理、4 定义），未发现缺陷。**
- axiom_check: **PASS**
- accepted_scope: **AUXILIARY；同一原闭 coercive 形式的正自伴平方根、完整组合域与全能量空间身份。原文覆盖保持 17/26，尚不升级 P022。**

已完整读取固定三个新模块、全部 30 项 raw 类型、公理记录、analysis/MATH_SPEC/台账及原稿 `paper/main.tex:333–376,2615–2654`，直接核对实际关联算子、零移位 resolvent、T227 正根和所用 mathlib 延拓/闭范围依赖。只使用固定 Git 对象及对应本地证据，未纳入后续工作树或动态审计，未查询远端 CI/看板，未重复运行全库。

## 对 T226 F1 的明确结论

**T226 F1 所要求的抽象平方根数学桥已清偿。** T226 报告 `63c553825231ccf22f1efb72dc2f10ed4e666fde` 指出的缺项是原稿 353 行的 `D(A^(1/2))=V` 与 `‖A^(1/2)v‖²=a(v,v)`，不能仅由口头援引第二表示定理替代。现在 `FormSquareRoot.lean:101` 的实际存在定理在同一原 H 上构造线性算子 S，其定义域是原能量嵌入的完整范围；输出正性、完整伴随图等价、S² 与原 A 的双向完整图等价，以及全部原 V 成员的能量身份。B 的存在、范围等式和能量身份均在证明内供应，不再作为额外前提。

这是可作为 `A^(1/2)` 的真实正自伴图平方根构造，满足 F1 要求的全部数学内容；无需再假定第二表示定理或谱分解。此次没有声称与另一个外部谱演算对象相等，也没有单列通用平方根唯一性新定理；这些并非本次构造接口所需的额外输入。**完整 P022 仍需后续接入验收**：将此处 `range(b.embed)` 与原 `OriginalForm.V`/具体 `H₀ᵐ` 值域、此处 `b.operator`/`b.form` 与原一般系数 A/a 作实际 Lean 身份对接，并把平方根字段与已验收 A1–A3 合并。当前泛型定理未完成该最终包装，不能仅凭本报告直接升级 P022；但 F1 已不再缺一条未证明的抽象平方根表示定理。

## 关键数学核对

1. **原 A 的真实逆。** `CoerciveForm` 只含原稠密连续单射 `embed:V→H`、有界对称形式和 coercivity；H、V 是完整实 Hilbert 空间，没有维数、可分性或紧嵌入限制。原 `domainV/domain/operator` 由全部 V 测试的变分身份构造。`inverseH=embed∘resolventEnergy(0)` 使用已实际构造的 Lax–Milgram 解；`inverseH_form` 为全部 f,v 给 `a(R_E f,v)=⟨f,embed v⟩`。交换形式变量得到 R 的真实自伴配对，取同一解得到非负性；原 resolvent 方程和唯一性给 R 单射及 `range R=D(A)`。`inverseH_operator_graph` 的双向等价明确包括原 A 的全部域和作用，故 R 确为原 A⁻¹，而非任意代用品。
2. **两种真实稠密性。** R 在 H 中的稠密性来自既有原关联域稠密性；B²=R 使 `range R⊆range B`，因此 B 稠密，且 R 单射给 B 单射。更关键的 `inverseEnergy_dense` 在原 V 的 Hilbert 拓扑中证明 `range R_E` 稠密：对其正交向量 y，用 coercive 形式对应的实际连续线性同构逆取 w，使形式 Riesz 算子作用于 w 等于 y。全部 H 载荷测试给 `⟨f,embed w⟩=0`，取 f=embed w 后由单射得到 w=y=0。这里没有把 H 中稠密误当成 V 中稠密，也没有输入目标形式域资格。
3. **真正延拓到完整 V。** 对正 B 且 B²=R，实际对称配对给 `a(R_E f,R_E g)=⟨Bf,Bg⟩`。coercivity 的 c>0 给 `‖R_E f‖V≤c⁻¹/²‖Bf‖H`，只除以严格正的 √c。`inverseSqrtLift` 用 mathlib `LinearMap.extendOfNorm` 延拓 `Bf↦R_E f`；已检查该工具的真实定义、稠密性/界前提和延拓身份，并非任意选取一个满足目标身份的 L。由 `range B` 及其乘积的稠密性、真实连续性，将两项身份扩展到所有 x,y：`a(Lx,Ly)=⟨x,y⟩` 和 `embed(Lx)=Bx`。
4. **满射与精确范围。** 原形式有界性给 `‖x‖²≤‖a‖‖Lx‖V²`，进而得合法的较松界 `‖x‖≤(1+‖a‖)‖Lx‖V`。由此 L 是 antilipschitz；H 完备及 L 连续使其范围闭。与此同时 `L(Bf)=R_E f` 和上一项 V 中稠密性给 L 范围稠密，故 L 满射到全部原 V。最终两向包含证明 `range B=range embed`。没有仅处理 D(A)、光滑核心或某个更小的能量空间；常数仅用于延拓与闭范围存在证明，不承担或改变论文权常数的统一性。
5. **同一 H 上的正自伴平方根。** `formSqrtDomain` 定义为原 `embed` 的范围，并且由真实范围定理允许以 B 的单射范围线性等价之逆定义 S。`formSqrt_graph` 精确给 `(x,f)∈graph S ↔ Bf=x`。域的稠密性直接是 `b.dense`，不是额外假设。正性来自 `⟨Sv,v⟩=⟨Sv,B Sv⟩≥0`。对任意 y,g，完整伴随测试等式通过全部 v=Bf 和内积分离性推出 y=Bg，反向用 B 的自伴性；因此 `formSqrt_adjoint_graph` 证明真正完整自伴图，未仅证明域内对称性。
6. **完整平方组合域与全 V 能量。** `formSqrt_square_graph` 左侧明确量化 v∈D(S)、u∈D(S)、u=S v 和 S u=f，右侧是原 A 的完整图；两个方向经 `B(Bf)=x ↔ Rf=x` 证明。这同时给 D(S²)=D(A) 和作用相同，不遗漏第二次作用的域资格。对任意原 v∈V，取 x=S(embed v)，由 `embed(Lx)=Bx=embed v` 和原嵌入单射得 Lx=v，再由全部 x 的配对身份得 `‖S(embed v)‖²=a(v,v)`。并未把平方根范数定义成标量 `sqrt(a(v,v))` 来回避算子问题。
7. **最终存在性与假设边界。** `exists_positive_form_square_root` 内部对同一 R 调用 T227 `positive_exists_sqrt`，然后返回上述同一个 S 的四项性质；最终类型不输入 B、range 等式、平方根域、能量等式或第二表示定理。已直接读取 T227 真实非交换迭代与实 Hilbert 正根构造，以及冻结报告 `cf3b8b7e99df3b1548a86f172f01f6a4ca154fac`（proof=本批 base，reviewed_at=`2026-10-20T06:23:47+00:00`，14/14 PASS）。无有限维、紧性、复化、光滑系数或椭圆正则性新增条件；零空间也包含，`1+‖a‖>0` 和 c>0 的使用不排除它。泛型构造仅处理既有 coercive 形式，没有声称非 coercive 半有界形式也有零移位有界逆。

## 全部声明逐项结论

下表名称统一带前缀 `Carleman.CoerciveForm.`；I/L/S 分别是固定 `Carleman/Continuous/FormInverse.lean`、`FormSquareRootLift.lean`、`FormSquareRoot.lean`。raw 行为本批固定公理文件中完整类型的起始行。

| 源码 / raw 行 | 声明 | 结论 |
|---|---|---|
| I:16 / 41483 | `inverseH` | PASS；实际零移位解的 H 值连续线性映射。 |
| I:19 / 41490 | `inverseH_eq` | PASS；与原域值 resolvent 完全相同。 |
| I:22 / 41494 | `inverseH_form` | PASS；全部 f,v 的真实变分身份。 |
| I:27 / 41499 | `inverseH_pair` | PASS；真实自伴配对。 |
| I:35 / 41504 | `inverseH_positive` | PASS；对称和非负二次型同时成立。 |
| I:44 / 41508 | `inverseH_injective` | PASS；由原算子方程推出单射。 |
| I:54 / 41512 | `inverseH_range` | PASS；精确范围等于原 D(A)。 |
| I:66 / 41516 | `inverseH_dense` | PASS；原 H 中稠密。 |
| I:72 / 41520 | `inverseEnergy_dense` | PASS；原 V 拓扑中稠密，内部构造证明。 |
| I:93 / 41524 | `inverseSqrt_injective` | PASS；B²=R 及 R 单射足够。 |
| I:99 / 41528 | `inverseSqrt_dense` | PASS；真实范围包含及稠密性。 |
| I:106 / 41532 | `inverseSqrt_energy_pair` | PASS；两个不同载荷的精确形式配对。 |
| I:113 / 41539 | `inverseSqrt_energy_bound` | PASS；由 coercivity 得实际延拓所需界。 |
| L:16 / 41544 | `inverseSqrtLift` | PASS；真实有界线性延拓定义。 |
| L:19 / 41551 | `inverseSqrtLift_apply` | PASS；在全部 Bf 上恢复原 R_E f。 |
| L:24 / 41556 | `inverseSqrtLift_pair` | PASS；全 H×H 配对身份。 |
| L:36 / 41562 | `inverseSqrtLift_embed` | PASS；同一原嵌入下 L 与 B 的关系。 |
| L:46 / 41567 | `inverseSqrtLift_lower_bound` | PASS；合法下有界估计。 |
| L:60 / 41572 | `inverseSqrtLift_surjective` | PASS；真实闭范围与 V 中稠密共同给满射。 |
| L:73 / 41577 | `inverseSqrt_range` | PASS；B 范围精确等于原能量嵌入范围。 |
| S:16 / 41582 | `formSqrtDomain` | PASS；原完整能量空间的 H 值域。 |
| S:18 / 41588 | `formSqrt` | PASS；B 的真实单射范围逆，作为域上线性算子。 |
| S:23 / 41599 | `formSqrt_inverse` | PASS；B(Sv)=v。 |
| S:29 / 41604 | `formSqrt_graph` | PASS；完整双向图身份。 |
| S:40 / 41609 | `formSqrt_energy` | PASS；全部原 V 的平方范数等于形式。 |
| S:51 / 41614 | `formSqrt_nonneg` | PASS；原 H 中正性。 |
| S:56 / 41619 | `formSqrt_adjoint_graph` | PASS；全部伴随图等价，不仅对称。 |
| S:72 / 41626 | `inverseH_operator_graph` | PASS；原 A⁻¹ 与原完整关联图相互识别。 |
| S:82 / 41631 | `formSqrt_square_graph` | PASS；全部组合域及算子作用精确匹配 A。 |
| S:101 / 41637 | `exists_positive_form_square_root` | PASS；仅由原形式数据内部构造同一 S 的全部性质。 |

## 固定源、依赖与本地证据

本批 Carleman 导入闭包共 **8 文件**：三个新模块及五个旧模块 `CoerciveForm`、`FormSolve`、`FormOperator`、`FormSelfAdjoint`、`RealOperatorSquareRoot`。五个旧文件相对数学 base 的 Git blob 全部不变，并已直接读取本批所需定义和证明。检查的 mathlib checkout 无修改且提交与 lock 一致：`56a005855ea17e0b0958f73ec801ae140b0a1679`；实际延拓与 antilipschitz 闭范围定理适用的是完整无限维实 Hilbert 空间。工具链固定 Lean 4.35.0，编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`。根导入、30 项 `#check`/`#print axioms` 均齐全。

- `/tmp/carleman-t228-local-evidence.json`：source=local、PASS，checked/source 均为本报告 proof，finished_at=`2026-10-20T06:23:40.139578+00:00`；`lake build Carleman` 和 `lake env lean tools/CheckAxioms.lean` 实际执行记录均 exit 0。
- 固定源清单 `/tmp/carleman-t228-local-source-manifest.txt`：**1024 项、111087 bytes**，SHA256 `d2aa90a215a294a26e86d714fa3a1d8d4574c1c90a8b2068d00e2e69f48ed4b7`。独立枚举固定提交全部 tracked `.lean` 与三个工具链配置，路径集合及唯一性一致；全部条目与固定 Git blob 逐一摘要相同。
- `/tmp/carleman-t228-target-build.log`：**2760 jobs** 成功，三个新模块均有实际成功记录；236 bytes，SHA256 `48e05d5c780103fd1756d4c74ddce6d4b4fdaaa3c99548df3fcef80a78067ec8`。`/tmp/carleman-t228-build.log`：**4261 jobs** 成功，80 bytes，SHA256 `c811272eeff95917eac6a98dfab8d54789a14753a255aace23733fedc1e2e63b`。`/tmp/carleman-t228-axioms.log` 为 0 bytes。
- `/tmp/carleman-t228-form-square-root-local-axioms.txt`：**3196747 bytes**，SHA256 `b5b3192a3991eb6977799471298bdb9e03d95d9b801b080c3b7ced17f3ae2e2d`，与证据摘要一致。30 项完整类型与公理记录已逐项读取；全部 **3744 个显式公理记录**只含正常基础公理 `propext`、`Classical.choice`、`Quot.sound` 或无公理。原全命名空间 `privateToUserName`/`collectAxioms` 白名单递归检查循环不变，末行确认 **9521 声明递归审计 PASS**；无 sorryAx 或额外数学公理。
- 原稿与固定基线相同，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本报告不把本地证据表述为远端 CI，也不把已观察日志表述为本 Agent 重新构建。

无数学修复项。接受本批 **AUXILIARY 正自伴平方根及完整形式域身份**，确认 T226 F1 的抽象数学桥已补齐；完整 P022 的原对象对接与最终装配须另验收。正文及 reviewed_at 冻结后仅单文件提交本报告，不修改实现、总台账、原稿或其它报告，不 push。
