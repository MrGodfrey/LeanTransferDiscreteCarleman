# T198 / C214 — 每个原控制弱积点的有限弱方程验收

- checked_sha: `714954acb8b017b09da56c71d4bd91b7d0ccffe2`
- mathematical_base: `3998fb3b4353576457a0773e69d587e5cf92e7e8`
- reviewed_at: `2026-10-20T02:54:36+00:00`
- reviewer: `/root/accept_spatial_foundations`
- result: **PASS，5/5 声明；未发现阻断缺陷**
- scope: **AUXILIARY，原文覆盖保持 17/26；P021 不提升**
- evidence_source: **local**。遵循已简化的验收政策，仅核对固定本地构建、公理证据与独立数学证明，未查询或等待远端 CI。

直接读取固定 Git 中三个新模块的全部证明、五项展开类型、原稿 `paper/main.tex:2365–2400`、T198 分析、MATH_SPEC、台账及必要依赖。原稿 SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef` 未变。本批将原控制家族、任意控制弱积点、同一状态进一步子列及有限弱测试身份实际连接起来；审核未以执行者说明或编译成功代替数学判断。

## 全部声明

源码位于 `Carleman/Control/`，行号属于 checked_sha。名称均加 `Carleman.` 前缀；raw 行指 `/tmp/carleman-t198-weak-accumulation-local-axioms.txt` 的完整类型起始行。四项 theorem、一项 def 与 manifest、固定 C214/T198 清单精确一致。

| 模块:源码行 | 声明 | raw 行 | 结论 |
|---|---|---:|---|
| RegionalWeakControlLimit:14 | `hilbert_weak_limit_norm_le` | 37522 | 给定真实全测试弱极限的范数不增；PASS |
| RegionalWeakControlLimit:26 | `regional_control_of_weak_limit` | 37527 | 原 U 的实际区域零延拓代表、等范数及费用；PASS |
| FiniteWeakControlIdentity:16 | `FiniteDirichletControlIdentity` | 37541 | 全部有限原测试的实际配对公式定义；PASS |
| FiniteWeakControlIdentity:40 | `cartesian_weak_control_limit_finite_identity` | 37553 | 固定 U 后内部选择同一 Y，清偿预算与全部有限测试；PASS |
| CartesianControlWeakAccumulation:18 | `Physical.box_cartesian_controls_weak_accumulation` | 37628 | 实际 HUM 家族的弱子列及每个弱积点结论；PASS |

## 数学核查

**给定弱极限不被替换。** 范数引理以原极限 v 自身为固定测试，Cauchy–Schwarz 和标量极限给 `‖v‖²≤C‖v‖`；零范数分支单独处理，C≥0 由原序列界内部推出。区域引理保留任意给定 U，经补集限制 CLM 的真实 Bochner 核证明 U 仍支撑在 ω。重读 `bochnerKernel_of_weak_tendsto`：利用 CLM 伴随保留全测试弱极限，零像的唯一极限确为零，并非假设弱闭性。随后取原限制得到区域 v，其限制算子伴随是实际零延拓，严格满足 `zeroExtension(v)=U` 和 `‖v‖=‖U‖≤C`。无另外选择的控制极限、无节点支撑替代 a.e. 支撑。

**同一 Y 同时对应全部测试。** 中间定理先量化给定 U 及其全测试弱收敛，再调用原受控状态弱子列定理，取得 Y、范数界及同一严格递增 φ；此时还没有引入 r、η、f、ψ。之后才证明 `FiniteDirichletControlIdentity` 的全部有限测试，因此不是逐测试另选 Y 或另取子列。沿 φ，原 h、dt 极限、控制弱极限 U 和物理终端范数消失均保持。状态的值、完整弱梯度和原 E_h 都是同一 Y 的对应弱极限，未混用任意三组场。

**预算与原数据。** 初值严格为原 `E_h* y0`，伴随平均压缩给 `‖y_h⁰‖≤‖y0‖`，真实单元平均强一致性内部给 E_hy_h⁰→y0。原 ForwardEquation、实际平均势界、`dt M≤1/2` 和控制费用内部给节点界与刚度/梯度预算。T196 使用的值预算为 `sqrt(T·[energyConstant(T,M)(‖y0‖+CU)]²)`，梯度预算为 `sqrt(‖y0‖²+CU²+(1+2M)T·[energyConstant(T,M)(‖y0‖+CU)]²)`；实际 K_h 时间范数等于原 controlNorm。没有把这些状态界、R_h/E_h 的弱收敛或目标测试身份留作中间定理的新假设。中间接口仍明确输入控制费用 CU、给定 U 的弱收敛及终端范数消失；最终定理从实际控制家族供应它们。

**公式确为原有限弱方程。** 已展开 `FiniteDirichletControlIdentity`：对每个 r 和 Fin r 上全部原有限张量，用同一个 Y 的 Yv/Yg、η 的真实区间内导数 f、同一 ψ 的值与梯度，断言
`−〈Yv,Φd〉+〈Yg,Φg〉+〈b·product(Yv),φ〉=〈y0,Φ0〉+〈U,Φ〉`。
这正是 T196 经原六项离散恒等式得到的配对公式。Fin r 包含任意有限项数及空和；时间 C¹ 区间内条件覆盖原 C∞([0,T])。定义只是该公式的名称，真正证明来自状态子列、原测试强一致性、势配对和端点消失，未将定义本身当成证明。

**实际家族与两种量词。** 最终定理直接取得 T197 同一个完整尾段 J、u_n、y_n，并原样保留全状态方程、E_h* y0、费用、原指数终端估计、真实区域支撑及两个端点重构极限。第一部分对任意取样 `a:ℕ→ℕ`（允许重复）从有界可分 Hilbert 序列提取 StrictMono χ，得到区域弱极限和费用；这是实际相对弱序列紧性，所用闭核子列依赖由 Riesz 等距和弱对偶闭球序列紧性构造。第二部分对每个 StrictMono a 及其任意给定弱极限 U，先恢复 U 的区域代表，再沿 `a(n)+J` 调用中间定理。该索引确实趋于无穷，原网格细化不丢失；随后状态进一步子列不会更换已固定的 U。输出同一个 Y、区域 v 及所有有限测试身份，费用仍为 `sqrt(C)‖y0‖`。

**常数与限度。** 固定正维盒、内部开区域和 ratio≥1 后，κ、d0 先于 T/M；C(T,M)>0 先于全部网格序列、势 b 和任意原 L² 数据。未引入依赖子列或测试的新控制费用常数。状态能量界可以依赖固定 T、M；未声称 C(T,M) 或状态界对变化 T 一致有界。h 与 dt 独立趋零，原全状态和平均势均保留，无网格嵌套、频率截断或时空耦合。实际实现仍限正维 Cartesian 盒和所述内部控制区域。本批尚未把有限空间测试扩展到全部 H¹₀ 测试，也未构造 V′ 时间导数、H 连续时间迹及连续状态初终值；一般多面体/P1 控制极限及完整 P021 仍待。

## 依赖、公理与固定本地证据

三模块项目 import 闭包共 **837 文件**，834 个既有文件与数学基线逐字节相同，固定根导入三个新模块。完整读取 T197 冻结报告（提交 `3a6bd348117c86d39b3f17b9b111f5a85ac3e7ea`，reviewed_at `2026-10-20T02:45:42+00:00`），并核对其报告在 checked_sha 中未变。必要的 T197 家族构造、T188 原能量/弱子列、T196 实际调用、区域闭核与零延拓、Hilbert 弱子列证明已重新读取；没有重复宣称历史结果为本批新成果。

固定 audit 对五项均检查完整类型和公理。独立解析 raw 的 3445 条显式公理记录（3441 个不同名称），全部只含 `propext`、`Classical.choice`、`Quot.sound` 或无需公理（9 条）。工具通过 `privateToUserName`/`collectAxioms` 递归检查全 Carleman 命名空间，末行 **8780 项 PASS**；无 sorryAx 或新增数学公理。

source manifest 的 **957 个不同路径**逐项与 checked_sha 的 Git 内容 SHA256 比较，全匹配；集合恰为全部 tracked Lean 文件及 lean-toolchain、lake-manifest.json、lakefile.toml，无遗漏。Lean 4.35.0/compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` 和 mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 固定。

| 本机证据 | 独立核对结果 |
|---|---|
| `/tmp/carleman-t198-target.log` | 4075 jobs 成功；263 bytes；SHA256 `076adea1f32311429de31419ef5d9882f77241248c734e08cc43f84ade7942ba` |
| `/tmp/carleman-t198-build.log` | 全库 4192 jobs 成功；80 bytes；SHA256 `4fbd618d6fdb595b3ac25b6e83aa58dbcc70bad70d6cb661b831ef2cadba8cc9` |
| `/tmp/carleman-t198-axioms.log` | stderr 0 bytes |
| `/tmp/carleman-t198-weak-accumulation-local-axioms.txt` | 2892660 bytes；SHA256 `0695c24f5a9f5e32ecd6b81b21e54e0d339840a9215ec97bbadd28f0617f69ce` |
| `/tmp/carleman-t198-local-source-manifest.txt` | 957 条，103731 bytes；SHA256 `915b08a491d418f50ee58f5fa3a64702656b1816347f3bf03038131671c0794f` |
| `/tmp/carleman-t198-local-evidence.json` | 931 bytes；SHA256 `8a98d159b16566e3ee0a28674321f45f36a23f4fb32985c9e1b15a1040bc8d63` |

evidence.json 的 checked/source SHA 精确对应本报告版本，source=local、status=PASS、ci_url=null，finished_at=`2026-10-20T02:50:41.985017+00:00`。记录的 `lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 实际 exit_code 均为 0，manifest/raw 摘要与独立计算一致。本报告核验这些真实本地执行证据，不声称审查者另行重跑构建或获得远端结果。

仅提交本报告；正文与 reviewed_at 签发后冻结，不修改数学或台账。
