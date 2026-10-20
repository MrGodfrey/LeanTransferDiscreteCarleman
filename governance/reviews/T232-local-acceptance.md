# T232 / C248 独立本机验收

- checked_sha: `fb7cdb9855e940d9d275e726ce09f3beef9b20b0`
- mathematical_base: `e61081ad723542df4c8e33ab57a10f10f6db67d0`
- reviewed_at: `2026-10-20T06:58:05+00:00`
- reviewer: 独立本机 Agent `accept_spatial_foundations`
- result: **PASS，15/15 显式声明（13 定理、2 定义），未发现缺陷。**
- axiom_check: **PASS**
- accepted_scope: **AUXILIARY；原全空间 L² 弱方向链的真实平移、统一差商界、分部求和及方向导数交换。覆盖保持 18/26，P023 不提升。**

已完整读取固定 `Carleman/Spatial/FullSpaceDifferenceQuotient.lean`、15 项 raw 完整类型、公理记录、analysis/MATH_SPEC/台账和原稿 `paper/main.tex:2659–2665`，并直接核对真实弱测试、卷积平移估计及强极限、仿射弱传输和 mathlib 的 Lp 测度保持复合接口。原 Corollary A.2 要求一般凸多面体 Dirichlet Laplacian 的完整空间分析性质；本阶段仅提供其边界正则性证明路线的差商工具。没有将这些工具本身计作内域或全域 H² 正则性。

## 实际对象与数学核对

1. **真正全空间 L² 平移。** `spatialTranslationLp z` 是 Lebesgue L² 等价类上由 `x↦x+z` 的真实测度保持拉回构造的线性等距映射。AE 公式、范数不变、零平移和 `T_z(T_w u)=T_(z+w)u` 均与这个约定一致。复合身份直接使用实际 Lp 复合定理，不把任意代表的逐点等式当成 Lp 定义。由等距内积身份以及 `T_zT_(-z)=I` 得 `⟨T_z u,v⟩=⟨u,T_(-z)v⟩`；平移的伴随符号正确，适用于全部 u,v∈L²，无有限支撑或有限测度前提。
2. **原弱状态、真实磨光界。** `IsWeakSpatialDerivative volume univ z u v` 明确量化所有原 `SpatialTest univ`，即真实紧支 C∞ 测试，要求 `⟨u,D_zφ⟩=−⟨v,φ⟩`。u,v 都是原全空间 L² 类，不是假定光滑代表，也不要求全部方向导数。`mollified_full_translation_bound` 将原 `mollified_cone_translation_l2` 用于真实 patch：region=univ、direction=z、height=t+1；t≥0 保证高度正且 t≤height，所有球/管状包含资格由 univ 内部供应。原核的紧支、非负和单位积分都使用已证明的实际 `spatialMollifier` 性质。旧估计通过卷积局部弱微分、线段 FTC、平移保测度和 L² 积分估计给 `‖T_(tz)u_n−u_n‖≤t‖v‖`，没有输入目标估计或遗漏一个方向长度因子。
3. **从同一实际磨光传回全部原 u。** 新证明使用 `spatialMollificationLp_tendsto u` 的真实强 L² 收敛和固定平移映射的连续性，使 `T_(tz)u_n−u_n→T_(tz)u−u`；范数连续性传递同一右端 t‖v‖。卷积点态函数与 Lp 平移差的身份通过 AE 等式和保测度复合处理，包括被平移的磨光代表；没有在不可数多个平移参数上交换 AE 量词。每个固定 t 均成立，因而结论覆盖全部非负 t，常数 1 与步长及磨光尺度无关。
4. **负步长与零步长。** t<0 时，原弱测试方向线性性真实推出 `D_(-z)u=−v`；对 −t≥0 应用前项，利用 `(−t)(−z)=tz` 与 `‖−v‖=‖v‖` 得全实数界 `‖T_(tz)u−u‖≤|t|‖v‖`。`δ_(h,z)=h⁻¹(T_(hz)−I)` 是实际 L² 连续线性映射；h=0 按 Lean 实数逆的定义给零映射，并在界证明中独立处理。h≠0 才约去 |h|，从而全部 h 都满足 `‖δ_(h,z)u‖≤‖v‖`。这不是断言 δ_0 等于弱导数，也未声称差商在 h→0 时已收敛。
5. **真实差商分部求和。** 在同一 L² 内积上，平移伴随及实数缩放精确给 `⟨δ_(h,z)u,v⟩=−⟨u,δ_(-h,z)v⟩`。证明同时保留平移反向和逆步长的负号；h=0 时两边均零，不使用非法除法。身份适用于任意 L² u,v，不需要它们有弱导数。
6. **任意另一弱方向的交换。** 对任意已有 `D_eu=v`，取实际仿射图 A=Id、偏移 −z，其逆是 x↦x+z，所以原 `affineTransportLp` 正好是这里的 T_z。已直接读取该工具：对每一个目标紧支光滑测试取真实仿射拉回，支撑按原像传输，实际 Fréchet 链式法则把方向变成 A e，真实保测度换元恢复所有弱测试积分。此处 A=Id 使方向仍为 e；所得 `D_e(T_z u)=T_z v` 与 u、v 使用同一个平移。弱链加法及 h⁻¹ 缩放再给 `D_e(δ_(h,z)u)=δ_(h,z)v`，全部 e,z,h 均允许，e 与 z 不必相同。交换定理仅需 D_eu 存在；统一范数界则另使用 D_zu=v，两种前提没有混淆。
7. **范围与边界限制。** 所有新弱链假设的空间参数都确实是 `volume, univ`。不存在把一般域的 L² 零延拓自动当作全空间 H¹/H² 的步骤；若后续在半空间或一般域使用本工具，必须另证明需要的全空间弱身份或局部测试资格。本批未证明差商有界反推二阶导数、变量系数边界能量估计或整体域正则性。方向 z 的尺度已在 v=D_zu 中，常数 1 不要求 z 为单位向量。维数为任意自然数，含 d=0；零方向和零状态没有非退化假设。没有时间参数、网格耦合、光滑状态、紧支状态或一般域高阶零延拓前提。

## 全部声明逐项结论

以下名称统一带前缀 `Carleman.`；源码行均为固定 `FullSpaceDifferenceQuotient.lean`，raw 行为固定审计文件完整类型的起始行。

| 源码 / raw 行 | 声明 | 结论 |
|---|---|---|
| 14 / 41839 | `spatialTranslationLp` | PASS；原全空间 L² 的真实保测度拉回等距线性映射。 |
| 19 / 41843 | `spatialTranslationLp_ae` | PASS；实际 x+z 代表身份。 |
| 24 / 41847 | `spatialTranslationLp_norm` | PASS；精确保范数。 |
| 28 / 41850 | `spatialTranslationLp_zero` | PASS；零平移是恒等。 |
| 34 / 41853 | `spatialTranslationLp_add` | PASS；真实复合及加法次序。 |
| 43 / 41857 | `spatialTranslationLp_inner` | PASS；反向平移的实际伴随配对。 |
| 49 / 41861 | `mollified_full_translation_bound` | PASS；全部真实卷积的常数 1 界，patch 资格内部清偿。 |
| 81 / 41870 | `IsWeakSpatialDerivative.translation_bound_nonneg` | PASS；实际强极限给全部原弱状态的非负步长界。 |
| 89 / 41875 | `IsWeakSpatialDerivative.translation_bound` | PASS；全部实步长，负方向弱身份正确。 |
| 101 / 41880 | `spatialDifferenceQuotient` | PASS；实际连续线性差商，含 h=0 约定。 |
| 106 / 41884 | `spatialDifferenceQuotient_apply` | PASS；同一差商的精确作用公式。 |
| 110 / 41888 | `IsWeakSpatialDerivative.differenceQuotient_bound` | PASS；全部 h 的步长统一界，无目标界假设。 |
| 122 / 41893 | `spatialDifferenceQuotient_inner` | PASS；真实内积上的差商分部求和，负号及 h=0 正确。 |
| 129 / 41897 | `IsWeakSpatialDerivative.translation` | PASS；任意方向 e 的全测试弱导数与平移交换。 |
| 151 / 41904 | `IsWeakSpatialDerivative.differenceQuotient` | PASS；任意差商方向/步长与已有弱方向导数交换。 |

## 固定源码、依赖与本地证据

导入闭包共 **83 个 Carleman 文件**，其中 **82 个旧文件**与数学基线逐 Git blob 相同。除新证明外，已直接读取本批使用的 `MollifiedConeTranslation`、`MollifiedConeFTC`、`StrongMollifierLimit`、`WeakDerivative`、`WeakDirections`、`AffineWeakTransport`，核对原弱对象和实际调用资格；不重审无关旧闭包。检查的 mathlib checkout 无修改，提交与固定 lock 一致：`56a005855ea17e0b0958f73ec801ae140b0a1679`。Lean 固定 4.35.0，编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`。根导入及全部 15 项显式 `#check`/`#print axioms` 齐全。

- `/tmp/carleman-t232-local-evidence.json`：source=local、PASS，checked/source 均为本报告 proof；finished_at=`2026-10-20T06:51:51.464404+00:00`。原 `lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 执行记录均 exit 0。
- `/tmp/carleman-t232-local-source-manifest.txt`：**1029 项、111641 bytes**，SHA256 `d75a4cc652f1b2d6405b52ed60ecdf89648b13aebf0c1e7831cfac10ee7eccc0`。独立枚举固定提交全部 tracked `.lean` 及三个工具链配置，路径集合、唯一性及全部条目的固定 Git blob 摘要逐项匹配。
- `/tmp/carleman-t232-target-build.log`：**3230 jobs** 成功，116 bytes，SHA256 `c3f8f3050cfe8f799be584d16bb84a617a3acfa216dc8297bf541a51436b1ddc`。`/tmp/carleman-t232-build.log`：**4271 jobs** 成功，80 bytes，SHA256 `a01e7f6e6fab3eadb9517a456a7398f23b81e834f941dfa28d8a52c2b31c5608`。`/tmp/carleman-t232-axioms.log` 为 0 bytes。
- `/tmp/carleman-t232-difference-quotient-local-axioms.txt`：**3218429 bytes**，SHA256 `8cae0de36a4d298fb4a0646fb3a3b0442b422965bb618f6e749186b450a242f1`，与固定证据摘要一致。全部 **3786 个显式公理记录**仅含正常基础公理 `propext`、`Classical.choice`、`Quot.sound` 或无公理；15 项完整类型及公理记录逐项核对。原全命名空间 `privateToUserName`/`collectAxioms` 白名单循环不变，末行确认 **9587 声明递归审计 PASS**，无 sorryAx 或额外数学公理。
- 原稿与基线逐字节相同，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本次读取并验证固定本地执行证据，没有重跑全库，未查询远端 CI/看板，也未把本地记录称作 CI 成功。

无修复项。接受本批 **AUXILIARY 全空间弱差商工具**；保持 18/26，不提升 P023。正文及 reviewed_at 签发后冻结，只单文件提交本报告，不修改实现、台账、根导入、审计、原稿或其他报告，不 push。
