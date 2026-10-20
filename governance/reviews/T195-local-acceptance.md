# T195 / C211 — 原有限测试与平均势强乘积极限独立验收

- checked_sha: `403ad474b6cb780407160e9d009e514c03287882`
- mathematical_base: `6812f26347c088d1d8d489c8e22dd1e5bb92e778`
- reviewed_at: `2026-10-20T02:23:38+00:00`
- reviewer: `/root/accept_spatial_lemma`
- result: **PASS，10/10 声明；未发现阻断缺陷**
- scope: **AUXILIARY，原文覆盖保持 17/26；P021 不提升**
- evidence_source: **local**。按固定提交中的简化治理规则，使用真实本机构建、公理审计和独立数学核查；本批没有查询、等待或下载远端 CI。

直接读取固定 Git 对象中的两个模块全部源码、10 项完整展开类型及公理记录、T195 分析、MATH_SPEC、原稿和关键依赖。原 `paper/main.tex:2926–2956` 的最后一个极限为 `b_{h,dt}E_hΦ⁻→bφ` 的产品 L² 强收敛。本批确实清偿这一有限测试乘积极限，未以执行者说明或编译成功代替语义核查。原稿 SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef` 未变。

## 全部声明

下列名称均在 `Carleman` 命名空间，源码位于 `Carleman/Control/`，行号属于 checked_sha；与 declarations.json 精确匹配：3 项 def、7 项 theorem。

| 模块:源码行 | 声明 | 实际核查 |
|---|---|---|
| FiniteTensorTestMultiplier:14 | `finite_tensor_test_bounded` | 原整个有限和的真实 a.e. 界由紧性内部供应；PASS |
| 同上:30 | `finiteTensorTestMultiplier` | value 为原 `Ση_l(t)ψ_l(x)`，强可测性和 bound 均已证明；PASS |
| 同上:40 | `finiteTensorTestMultiplier_value` | 全产品空间上精确函数身份；PASS |
| 同上:45 | `L2_tendsto_of_Linfty_error` | 有限测度上由实际 L∞ 误差推出真实 L² 类强收敛；PASS |
| FiniteTestPotentialConsistency:13 | `cartesianFiniteTestProduct` | 原全部内点取样、E_h、前层时间重构及真实 Bochner 产品映射；PASS |
| 同上:21 | `p1FiniteTestProduct` | 同一完整节点插值的原前层重构；PASS |
| 同上:29 | `cartesian_finite_test_product_strong_convergence` | 内部调用实际 FD 产品 L∞ 一致性得到原测试产品 L² 极限；PASS |
| 同上:45 | `p1_finite_test_product_strong_convergence` | 内部调用实际 P1 产品 L∞ 一致性得到同一极限；PASS |
| 同上:60 | `cartesian_finite_test_potential_strong_convergence` | 原时间—对偶胞元平均势的保界、强一致性和测试极限全部内部清偿；PASS |
| 同上:81 | `p1_finite_test_potential_strong_convergence` | 原时间平均势的保界、强一致性和节点测试极限全部内部清偿；PASS |

## 数学核查

**同一个原测试。** 时间因子只要求 Icc[0,T] 上连续；空间因子是原 `SpatialTest S` 的真实光滑紧支函数。紧区间与紧支撑分别给每项界，有限和取 `Σ|A_l||B_l|≥0`；不预设整和有界或取任意替代极限。时间限制与空间连续性经产品投影给真实 a.e. 强可测性。`finiteTensorTestMultiplier` 的 value 精确为原整个有限和；`toL2` 由有限测度及该已证界构造，代表 a.e. 等于同一函数。空有限和、零测度或空区间不需要额外分支假设。

**L∞ 到 L²。** 先用 `Lp.coeFn_sub` 与 `φ.toL2_ae` 将函数差精确识别为 `u_n−φ.toL2` 的 Lp 代表。复核固定 mathlib 的指数比较定理：此处实际给
`eLpNorm(v,2) ≤ eLpNorm(v,∞) · ν(univ)^(1/2)`。
v 是 Lp 差，强可测性内部成立；有限测度保证右侧固定幂不是 ⊤。在 ENNReal 中由非负夹逼和乘有限常数连续性得到二阶半范数趋零，最后仅在极限零点用 `tendsto_toReal zero_ne_top` 得 L² 范数趋零。没有把 ⊤ 的 toReal 当成有限范数，也没有除以测度或假设正体积。零测度情形同样有效。

**实际 I_h、E_h、Φ⁻。** FD 定义直接用 `cartesianNodalSample` 的全部原内节点值；P1 定义直接用同一网格的 `nodalLp`。两者都先对原整个有限和在 `g.nodeTime i` 取值，再用 `(t_i,t_{i+1}]` 的原时间重构，最后用已证的 Bochner→产品 L² 等距映射。已重读该映射的简单代表及胞元 a.e. 身份，以及 T194 的有限张量代表证明；没有把任意产品代表当成逐时刻值，也没有使用该映射的满射性。T194 的实际 L∞ 误差与这里的定义逐项相同，故可以直接送入 L² 桥梁。FD 边界条带仍保留原零延拓。

**真实平均势及乘法。** `fixedSpacetimePotential` 是原 FD 时间—对偶单元平均后的零延拓，`fixedTimePotential` 是原 FE 时间平均（空间变量保持原值），符合原稿 `sec:control-consistency`。其 bound 都精确等于原 `b.bound`。重新核查实际平均/投影身份、强收敛调用及乘法定义：`BoundedMultiplier.map` 的代表为真实逐点乘积，因而最终左、右端分别是原 `b_{h,dt}E_hΦ⁻` 与 `bφ` 的产品 L² 类。T185 的实际分解为
`a_n v_n−bφ = a_n(v_n−φ)+φ(a_n−b)`，
相应范数界是 `M‖v_n−φ‖₂+‖φ‖∞‖a_n−b‖₂`。两个最终定理内部供应 a_n 的统一 bound、T183/T184 的原势强一致性，以及本批原测试强极限；未留下抽象配对、目标收敛、额外预算或离散测试统一界作为输入。

**量词和范围。** 固定域、固定 T、固定有限测试与固定任意有界可测势 b；时间网格给 T>0，证明内部取得所需非负性。η/f 的区间内 C¹ 接口覆盖原 C∞([0,T])，不需要域外延拓。FD 只要求 δ_j≤h、h→0，最终平均势定理另用 N_j>0，原 N_j≥2 满足它；不添加长宽比、网格嵌套或 h/dt 耦合。P1 要求原有限分割的 FaceMatching、maxDiameter→0，以及有限空间测度；原有界开域满足这些条件。此零阶乘积极限无需额外形状常数、BoundaryFitted 或 H² 数据。dt 独立趋零；未声称测试常数对变化 T 统一。完整极限弱方程、连续状态时间迹和控制收敛定理仍待，不能据本批提升 P021。

## 依赖、公理和本地证据

两个模块的项目 import 闭包共 391 个文件，389 个既有文件与数学基线逐字节不变。T194 的冻结报告已完整读取并核对提交 `ebc826644387d929f67677cd4c4afea62cd1d42a`（reviewed_at `2026-10-20T02:19:05+00:00`）；其实际产品 L∞ 供应在本批未变。关键的 T183/T184 平均势强收敛和 T185 乘法误差闭包也与相应接受版本一致，并已实际重读当前调用及关键证明。

固定根 `Carleman.lean` 导入两个模块，固定 audit 工具逐项检查全部 10 个完整类型，并用 `privateToUserName`/`collectAxioms` 递归检查 Carleman 全命名空间。raw 末行 **8699 项 PASS**；本批每项仅依赖 `propext`、`Classical.choice`、`Quot.sound`。全部显式记录均在该白名单内，无 sorryAx 或新增数学公理。

独立逐条计算 source manifest 的 949 个不同路径在 checked_sha 中的 Git 字节摘要，全部匹配；其集合恰为全部 tracked Lean 文件及 lean-toolchain、lake-manifest.json、lakefile.toml，无遗漏。审查时这些受检工作树文件也与固定对象相同。Lean 4.35.0/compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`、mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 固定；所读 mathlib 指数比较文件与 pin 字节一致。

| 本地证据 | 独立核对结果 |
|---|---|
| `/tmp/carleman-t195-target.log` | 3591 jobs 成功；192 bytes；SHA256 `d6e41c9abb8de35ccd3a81bd35ad50d0185dc1742d5a3cd8bd9da8ee96d47400` |
| `/tmp/carleman-t195-build.log` | 全库 4184 jobs 成功；80 bytes；SHA256 `0169717a224bbfc0a462cff6ee577c6fda84312f6c33a10deb387555a576aa39` |
| `/tmp/carleman-t195-axioms.log` | stderr 0 bytes |
| `/tmp/carleman-t195-potential-tests-local-axioms.txt` | 2832139 bytes；8699 项；SHA256 `cad038574e32997e7a2a6a743d11c7850db109f295a561d59864f124f9026847` |
| `/tmp/carleman-t195-local-source-manifest.txt` | 949 条，102834 bytes；SHA256 `a90459b28e14ce05dc72ec121afa4a45034cc0a8d6be4df8c5021e367f3325ac` |
| `/tmp/carleman-t195-local-evidence.json` | 931 bytes；SHA256 `4951535183ef1b2bb3f123657a316d1b78fbbcd1f2d98fa423f7ec8f7c21dc0d` |

evidence.json 的 checked/source SHA 均为本报告版本，status=PASS、source=local、ci_url=null，finished_at=`2026-10-20T02:18:56.101348+00:00`；所录 `lake build Carleman` 和 `lake env lean tools/CheckAxioms.lean` 均实际 exit 0，manifest/audit 摘要与独立计算一致。本报告读取并核验这些真实执行记录，不声称审查者另行重跑构建或取得远端成功。

只提交本报告。正文与 reviewed_at 签发后冻结；不修改数学、台账或其他报告。
