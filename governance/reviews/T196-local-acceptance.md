# T196 / C212 — 原差分有限测试弱极限身份独立验收

- checked_sha: `9c62b704e83c3e25302aa14d665337a646beb8ee`
- mathematical_base: `403ad474b6cb780407160e9d009e514c03287882`
- reviewed_at: `2026-10-20T02:36:31+00:00`
- reviewer: `/root/accept_spatial_foundations`
- result: **PASS，8/8 声明；未发现阻断缺陷**
- scope: **AUXILIARY，原文覆盖保持 17/26；P021 不提升**
- evidence_source: **local**。按用户简化后的规则核验固定本地构建、公理和独立数学证明；没有查询、等待或下载远端 CI。

已直接读取固定 Git 对象中两个新模块的全部证明、八项完整展开类型、原稿 `paper/main.tex:2385–2400`、T196 分析、MATH_SPEC、台账及必要依赖。原稿 SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef` 未变。本批对应 `eq:conv-limit-identity` 的有限光滑张量测试身份；审核没有以执行者说明或编译成功代替数学核对。

## 全部声明

名称均位于 `Carleman` 命名空间，源码目录为 `Carleman/Control/`；行号属于 checked_sha。raw 行指 `/tmp/carleman-t196-weak-limit-local-axioms.txt` 的完整类型起始行。两项 def、六项 theorem 与 manifest、固定 C212/T196 清单精确一致。

| 模块:源码行 | 声明 | raw 行 | 结论 |
|---|---|---:|---|
| CartesianWeakLimitTests:17 | `timeTensor_map` | 37105 | 原 Bochner 张量与真实 CLM 交换；PASS |
| CartesianWeakLimitTests:25 | `cartesianFiniteTestSequence` | 37111 | 所有 steps+1 节点的整个原有限和取样；PASS |
| CartesianWeakLimitTests:30 | `cartesianFiniteTestSequence_front` | 37123 | 同一取样的前层身份；PASS |
| CartesianWeakLimitTests:36 | `cartesianFiniteTestSequence_endpoints` | 37129 | 首末节点严格为 0、period；PASS |
| CartesianWeakLimitTests:47 | `cartesianGridPotential` | 37137 | 只沿原盒端点和 period 等式运输同一势；PASS |
| CartesianWeakLimitTests:57 | `cartesian_fixed_time_product_potential` | 37151 | 原平均势作用经真实产品映射精确交换；PASS |
| CartesianWeakLimitTests:74 | `cartesian_finite_test_gradient_strong_convergence` | 37168 | 原整个前层测试的完整弱梯度强极限；PASS |
| CartesianWeakLimitIdentity:15 | `cartesian_finite_test_weak_limit_identity` | 37198 | 从实际六项有限网格身份得到原符号的极限身份；PASS |

## 数学核查及范围

**同一原对象。** `cartesianFiniteTestSequence` 对每个 `Fin(steps+1)` 取原 `Ση_l(i·dt)ψ_l` 的全部内部节点值，经原物理有限空间构造；不是替代测试序列。`castSucc` 为前层、`succ` 为后层，原整个和的差商严格为 `dt⁻¹(φ_{i+1}−φ_i)`。首末节点由实际定义给 0 和 period=T。原 η/f 的 Icc[0,T] 连续性及区间内导数覆盖 C∞([0,T])，无需区间外延拓。

最终定理中的 E 是原后层状态的 E_h 时间重构，G 是同一状态 Kuhn jet 的 `field 1`，K 是原 `E_h B_h u`，均非任意占位映射。`DirichletEnergyState` 只是原 H¹₀ 图空间的载体；Yv、Yg 是同一个 Y 经实际值、梯度 CLM 的 Bochner 映像。重读 `dirichletGradient`、`cartesianBoxDirichletState_gradient` 和 `SpatialTest.dirichletState_gradient`：这里保留全部一阶导数纤维；原 Dirichlet 形式就是这些实际梯度的 L² 内积，没有混入值内积或将 Fréchet 算子范数当成梯度纤维范数。

**变化测试的强极限。** `timeTensor_map` 用实际 Lp 代表与 CLM 标量线性证明，不交换未经证明的逐时刻代表。T193 的原整个测试 H¹₀ 强极限，经固定梯度 CLM、真实胞元交换及有限和线性，给本批 Φg；同一调用给前层 Φ 和完整差商 Φd 的真实 L² 强极限。每个有限求和仍是同一 η、f、ψ。κ 在整个网格序列之前固定，`h/κ≤δ_j≤h` 是原可比网格条件；h 与 dt 分别趋零，无嵌套或时空耦合。固定 T，未声称测试常数对变化 T 统一。

**势及配对。** `cartesianGridPotential` 仅以 `hbox` 和 `hT` 进行相等运输，保留同一 b；`cartesian_fixed_time_product_potential` 调用真实时间—对偶胞元乘法交换身份。有限网格上先由 Bochner 产品等距精确保留内积，再把原 P_n E_n 配对写成 `fixedSpacetimePotential` 作用于同一产品状态。T185/T195 的实际平均势保界、强一致性和原测试产品强收敛清偿势配对极限。已复核乘法误差分解与实乘子的对称性：将乘子移到强收敛测试侧后，用状态全测试弱收敛。状态没有被误当作强收敛，也不需要 Bochner→产品映射满射。右端测试乘子的 value 精确为原整个有限和，因此混合使用产品势内积和 Bochner 其余内积确实表达原积分配对。

**六项符号和端点。** 重新读取原 `Physical.ForwardEquation`、非周期分部求和、真实刚度梯度配对及固定盒运输。每个 n 的实际身份为
`−〈E_n,D_n〉+〈G_n,H_n〉+〈P_n,V_n〉
 =〈E_h y_n^0,E_h φ_n^0〉+〈K_n,V_n〉−〈E_h y_n^N,E_h φ_n^N〉`。
由输入的三个范数预算和全测试弱极限，分别与 D_n、H_n、V_n 的强极限配对。初端点用真实初值强极限与固定测试端点强极限。终端物理范数趋零通过 E_h 等距给重构终态强趋零，再与强收敛测试端点配对消去；不预设 Y 的连续时间迹。唯一标量极限给
`−〈Yv,Φd〉+〈Yg,Φg〉+〈b·product(Yv),φ〉
 =〈y0,Φ0〉+〈U,Φ〉`，
与原 `eq:conv-limit-identity` 的符号和初端点一致。

**明确输入与未完成部分。** 定理仍明确输入原离散 ForwardEquation、E/G/K 的统一范数预算及对应全测试弱极限、实际 E_h y_h⁰→y0、原物理终端范数→0。Y/U 是所选极限，未在此处选择 HUM 控制或提取子列；U 的区域零延拓识别没有在结论中另行构造。N_j>0 是平均势一致性所用条件，论文 N_j≥2 满足；证明不需非空内部节点索引，d=0 亦未增加隐藏条件。最终只对任意有限光滑空间张量成立；扩展到全部 V 测试、V′ 时间导数、H 连续时间迹及其初终值、接入实际控制构造和整个 P021 仍待。上述剩余前提没有被隐藏为已完成结论。

## 依赖、公理和本地证据

新模块项目 import 闭包共 405 文件，403 个既有文件与数学基线逐字节相同；两模块均在固定根导入。已完整读取 T195 冻结报告（提交 `2eaf3a373f80f24d0d968f926bdf32244d55717f`，reviewed_at `2026-10-20T02:23:38+00:00`），并直接核对 T193 测试、T189 六项身份、T190 产品代表、T185 势配对及原 H¹₀ 梯度的实际调用和证明。

固定 audit 中八项均有完整 `#check @...` 和 `#print axioms`。独立解析 raw 的 3431 条显式公理记录（3427 个不同名称），全部只含 `propext`、`Classical.choice`、`Quot.sound` 或无需公理（9 条）；无 sorryAx 或新增数学公理。工具通过 `privateToUserName`/`collectAxioms` 检查全部 Carleman 常量及递归依赖，末行 **8714 项 PASS**。

固定 source manifest 的 **951 个不同路径**已逐项与 checked_sha 的 Git 字节 SHA256 比较，全匹配；其集合恰为全部 tracked Lean 文件和三个工具链配置，无遗漏或多项。Lean 4.35.0/compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 固定。

| 本地证据 | 独立核验 |
|---|---|
| `/tmp/carleman-t196-target.log` | 3607 jobs 成功；185 bytes；SHA256 `4424a1851cb70c3c78fb365495438bfb8e533f5e53f3eaf74f54e17c767246d5` |
| `/tmp/carleman-t196-build.log` | 全库 4186 jobs 成功；80 bytes；SHA256 `05f24d5510b030cf9daba9a200b174c88077748dd01e471406091666306878d0` |
| `/tmp/carleman-t196-axioms.log` | stderr 0 bytes |
| `/tmp/carleman-t196-weak-limit-local-axioms.txt` | 2847778 bytes；SHA256 `b85814859d7b5254eb43b565ddeb587da467b6f8b7eb48c48207ab7741be77a5` |
| `/tmp/carleman-t196-local-source-manifest.txt` | 951 条，103059 bytes；SHA256 `196d35e3d85b008b5f055b60ec346de5c61ae675ee1126604c6ac59d5fd07cf7` |
| `/tmp/carleman-t196-local-evidence.json` | 931 bytes；SHA256 `46fd081f7d895a6e3c21d2d3f1dc1067b087df54ce305e8085f912e862b98590` |

evidence.json 的 checked/source SHA 均精确对应本报告版本；source=local、status=PASS、ci_url=null，finished_at=`2026-10-20T02:32:48.021015+00:00`。所录 `lake build Carleman`、`lake env lean tools/CheckAxioms.lean` 的实际 exit_code 均为 0，manifest/audit 摘要与独立计算一致。审查者读取核验这些执行证据，没有宣称另行重跑构建或获得远端结果。

仅提交本报告。正文与 reviewed_at 签发后冻结，不修改数学或台账。
