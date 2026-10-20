# T194 / C210 — 原有限张量测试产品 L∞ 一致性独立验收

- checked_sha: `6812f26347c088d1d8d489c8e22dd1e5bb92e778`
- mathematical_base: `3ac3635f878b0c1521032b396a2630acdcc4da46`
- reviewed_at: `2026-10-20T02:19:05+00:00`
- reviewer: `/root/accept_spatial_foundations`
- result: **PASS，14/14 声明；未发现阻断缺陷**
- scope: **AUXILIARY；原文覆盖仍为 17/26，P021 不提升**
- evidence_source: **local**。遵照用户已简化的流程，以固定版本的真实本地构建、公理审计和独立数学核查签发；本批没有查询、等待或下载远端 CI。

独立读取固定 Git 对象的三个模块完整证明、14 项展开类型及公理、关键依赖、原稿、T194 分析、MATH_SPEC 和状态协议。原稿 `paper/main.tex:2926–2941` 要求整个有限张量的原 `E_h Φ⁻` 在产品时空域 L∞ 收敛；其 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，未修改。执行者分析和编译成功未被当作数学忠实性的替代。

## 全部声明

名称均加 `Carleman.` 前缀；源码位于 `Carleman/Control/`，行号属于 checked_sha。raw 行号指 `/tmp/carleman-t194-uniform-tests-local-axioms.txt` 中完整 `#check @...` 的起始行。清单与固定 C210/T194 及 declarations.json 精确一致。

| 模块:源码行 | 声明 | raw 行 | 核查结论 |
|---|---|---:|---|
| SpatialTestUniformError:14 | `cartesian_test_cell_uniform_error` | 36758 | 实际 E_h、含边界条带的 a.e. 空间误差；PASS |
| SpatialTestUniformError:41 | `cartesian_box_test_cell_uniform_error` | 36772 | 由真实端点等式运输至同一固定盒；PASS |
| SpatialTestUniformError:52 | `p1_test_uniform_error` | 36786 | 原节点函数误差 ≤2 Lip(ψ) maxDiameter；PASS |
| TensorTestUniformError:15 | `timeCell_ae_covered` | 36795 | 原时间单元在 (0,T] 的 a.e. 覆盖；PASS |
| TensorTestUniformError:25 | `finite_time_tensor_uniform_error` | 36798 | 整个有限和的前层取样误差；PASS |
| TensorTestUniformError:66 | `finite_tensor_test_bounds` | 36812 | 固定测试内部供应四类界，先于网格；PASS |
| TensorTestUniformError:87 | `bochner_finite_time_tensor_ae` | 36823 | 实际 Bochner 产品代表与原胞元函数身份；PASS |
| TensorTestUniformError:112 | `finite_tensor_test_aestronglyMeasurable` | 36831 | 原产品测试的真实 a.e. 强可测性；PASS |
| TensorTestUniformError:123 | `bochner_finite_time_tensor_uniform_error` | 36837 | 实际误差的指数 ⊤ 本质上确界估计；PASS |
| TensorTestUniformConsistency:13 | `cartesian_finite_time_test_uniform_bound` | 36857 | 原全部取样经 E_h 的 Ah+Bdt 界；PASS |
| TensorTestUniformConsistency:48 | `SimplicialPartition.nodalLp_finite` | 36883 | 同一节点插值的完整有限和线性身份；PASS |
| TensorTestUniformConsistency:61 | `p1_finite_time_test_uniform_bound` | 36889 | 原全部节点插值的 A maxDiameter+Bdt 界；PASS |
| TensorTestUniformConsistency:91 | `cartesian_finite_time_test_Linfty_consistency` | 36910 | 固定盒上原产品 L∞ 极限；PASS |
| TensorTestUniformConsistency:114 | `p1_finite_time_test_Linfty_consistency` | 36939 | 变化 P1 网格的原产品 L∞ 极限；PASS |

## 数学核查

**空间及边界。** 差分证明使用实际有限 Kuhn 分割，剔除真实零测坐标中平面后，最近格点是所在单纯形的顶点。`cartesianCellFunction_nearest_value` 的两分支分别给内部对偶单元取值和未覆盖条带上的零值。`cartesianInteriorData_test_vertex` 在内部构造原节点索引，在域外利用原 `SpatialTest.support ⊆ Ω` 得每个相应顶点严格零值；没有把边界零测擅自提升为点值。随后实际单元直径 ≤(d+1)h 与原测试 Lipschitz 界给所需误差。只用 δ_j≤h，无长宽比或网格嵌套前提。P1 证明用真实节点函数在每个单元的身份及常数仿射逼近，给 2 Lip(ψ) maxDiameter；经 `nodalLp_ae` 转入同一 L² 类。这个零阶结果无需原 H¹ 估计的形状或边界适配条件，包含论文网格，并允许空有限索引及 d=0。

**时间与完整有限和。** 实际单元为 `(g.nodeTime i, g.nodeTime i+dt]`，采用左端前层值，准确对应原 Φ⁻。全单元体积等于 T、两两不交及有限测度给 a.e. 覆盖；该结论仅用于时间，没有把空间条带当成零测。对每项实际展开
`η(t_i)v−η(t)ψ = η(t_i)(v−ψ)+(η(t_i)−η(t))ψ`，
由 |t−t_i|≤dt 得总界 `Σ(A_l ε_l+C_l dt B_l)`。紧区间连续性、区间内 C¹ 导数以及空间光滑紧支撑内部供应 A_l、B_l、C_l、D_l；未把目标误差或收敛作为最终假设。整个原取样和整个 P1 节点插值分别经 `cartesianNodalSample_finite`、`nodalLp_finite` 与线性重构识别为同一有限和，不是未经识别的因子近似。

**真实产品 L∞。** 重读 T190 的实际简单函数延拓及时间胞元代表身份。本批对有限 l、有限时间节点合并 a.e. 等式，再通过产品测度的投影拉回；没有不可数 a.e. 量词交换，也不使用 Bochner→产品映射满射。时间因子仅在 Icc[0,T] 连续，限制至 Ioc 后与全局连续空间测试相乘，内部给产品强可测性。实际 L² 代表减原测试因此可测。核对固定 mathlib `eLpNorm_exponent_top` 与 `eLpNormEssSup_le_of_ae_bound`：这里的 `eLpNorm · ⊤` 正是该误差的本质上确界，不是仅 L² 控制或不可测分支。

**常数与极限。** 两个 uniform_bound 在固定域、T、有限原测试之后，先给 A,B≥0，再量化所有网格、h、g。差分可取 A=Σ A_l D_l(d+1)，P1 可取 A=Σ2 A_l D_l，共同 B=Σ C_l B_l。没有节点数或网格相关常数。固定 T 可影响测试常数；未声称它对变化 T 统一。最终在同一个固定产品测度上，用 ENNReal.ofReal 的连续性和夹逼，从各自 h→0/maxDiameter→0、dt→0 得真实 L∞ 收敛，无 h/dt 耦合。区间内 C¹ 条件覆盖论文 C∞([0,T])，不要求区间外延拓。

本批完整清偿所述产品 L∞ 测试一致性。最终势乘积、极限弱方程、状态端点及整个控制收敛结论仍不属于本批，不能据此提升 P021。

## 依赖、公理与固定本地证据

三个模块的项目 import 闭包共 376 个文件，373 个既有文件与数学基线逐字节一致；三个新模块均由固定 `Carleman.lean` 导入。已读取冻结 T193 报告及其实际顶点身份，复核最近顶点/条带取值、P1 节点误差、原时间胞元及 T190 产品代表的关键证明。没有以旧报告替代当前代码。所读 mathlib 两个 L∞ 引理文件与固定 pin 字节一致。

固定 audit 工具对全部环境常量用 `privateToUserName` 筛选 Carleman 命名空间并递归 `collectAxioms`。raw 末行确认 **8670 项 PASS**；3413 条显式公理记录（3409 个不同名称）全部在 `propext`、`Classical.choice`、`Quot.sound` 白名单内，其中 9 条无需公理。本批 14 项均有完整类型和正常基础公理记录，无 sorryAx 或额外数学公理。

独立逐条计算 source manifest 的 **947 个不同路径**在 checked_sha 中的 Git 内容 SHA256，全部匹配；覆盖全部 tracked Carleman Lean 源、根导入、audit 工具以及 lake-manifest、lakefile、lean-toolchain，无遗漏。Lean 固定为 4.35.0（compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`），mathlib 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。

| 本机证据 | 独立读取和校验结果 |
|---|---|
| `/tmp/carleman-t194-target.log` | 3576 jobs，Build completed successfully；256 bytes；SHA256 `4a144299667ffb16160f6424e49268dffca4ae2f6336815424ec19140eb0bf82` |
| `/tmp/carleman-t194-build.log` | 全库 4182 jobs，Build completed successfully；80 bytes；SHA256 `141b6adab28b94ffb70ee840b03f3818b86f98dee8fce3ababdc47a14137c000` |
| `/tmp/carleman-t194-axioms.log` | stderr 为 0 bytes |
| `/tmp/carleman-t194-uniform-tests-local-axioms.txt` | 2822100 bytes；SHA256 `4b330ade154bb146d9c5ff2c51acedd59cd6788c599d057580545f5b6dab21b9` |
| `/tmp/carleman-t194-local-source-manifest.txt` | 947 条，102602 bytes；SHA256 `abaa225479ea2e86297d2a396b8bcb3391f27e568435afbe6fa0334772e5181a` |
| `/tmp/carleman-t194-local-evidence.json` | 931 bytes；SHA256 `39890f6e670554eabfee4bc24a18b60ade8deb8a7a5586434830774c14f1ea52` |

evidence.json 的 checked_sha/source_head_sha 均精确等于本报告固定 SHA，source=local、status=PASS、ci_url=null，finished_at=`2026-10-20T02:12:52.672454+00:00`；记录 `lake build Carleman` 和 `lake env lean tools/CheckAxioms.lean` 的实际 exit_code 均为 0，manifest/audit 摘要与上述独立计算一致。本报告读取并核验这些真实执行证据，不声称审查者另行重跑构建或取得远端结果。

只提交本报告；签发后正文和 reviewed_at 冻结。
