# 公开形式化工程复用清单（初始调查，未完成联合构建）

按当前缺失的依赖检索，再决定是否实现。无需在首轮完整调查或联合构建所有候选工程。**下表表示找到了公开代码、与本工程理论相关；不表示已经核实与当前 Lean 版本兼容，也不表示已经证明本文 (A1)–(A4)。**

| 项目 | 位置 | 首先可研究的内容 | 风险 |
| --- | --- | --- | --- |
| mathlib4 | https://github.com/leanprover-community/mathlib4 | Hilbert/adjoint、连续线性算子、测度积分、有限和 | 主依赖，锁定版本 |
| EllipticPDE | https://github.com/alejandro-soto-franco/EllipticPDE | Lax–Milgram、Sobolev、椭圆谱与局部正则性 | 局部正则性不能替代全局凸多面体 H² 正则性 |
| EscauriazaSereginSverak | https://github.com/scottnarmstrong/EscauriazaSereginSverak | Gaussian/Half-space Carleman 证明组织及工具 | 权函数与观测项不同，不等于原文 Proposition A.3 |
| CoarseGraining | https://github.com/scottnarmstrong/CoarseGraining | Sobolev、加权椭圆估计与长工程组织 | 体量和接口兼容性；只选择性借鉴 |
| CoarseDeGiorgi | https://github.com/scottnarmstrong/CoarseDeGiorgi | formalization.yaml、comparator、审计结构 | 不等于本论文直接可用引理 |
| SciLean | https://github.com/lecopivo/SciLean | 数值分析/科学计算表达方式 | 关注度次于证明内核和 Hilbert 空间基础 |

每次复用必须记录：代码仓库及 commit、license、Lean toolchain、目标命题具体声明、Lean 型别和所用前提、与论文接口匹配结论、引入包的后续维护成本。禁止单凭 README 声称某引理可直接调用。

采用记录只针对实际需要的声明：仓库/commit、许可、工具链、声明与前提、最小 import + example 兼容构建、接口对应和依赖成本。未采用项目保留为候选，不必因清单存在就全部导入。

## T001 实际采用

仅使用已锁定 mathlib4 `56a005855ea17e0b0958f73ec801ae140b0a1679`（Apache-2.0，Lean 4.35.0），不新增包。
`Mathlib.Logic.Equiv.Fin.Rotate` 的 `finRotate : (n : ℕ) → Equiv.Perm (Fin n)`、
`finRotate_apply`、`finRotate_symm_apply` 给出模 N 的 ±1 移位；
`Mathlib.Analysis.InnerProductSpace.Basic` 的 `real_inner_smul_left/right`、`inner_sub_left/right`
用于任意实内积空间的双线性展开，`real_inner_comm` 用于反向伴随。
最小模块调用及其前提由 `TimeGrid.lean` / `SummationByParts.lean` 的实际证明编译核实，
并由 `tools/CheckAxioms.lean` 输出主要声明及检查传递公理。有限和重排复用本仓库
`Carleman.sum_sub_perm`，没有另行证明该辅助引理。缓存只增加这些 import 的依赖闭包。

## T002 实际采用

继续仅用同一固定 mathlib4 commit、Apache-2.0 和 Lean 4.35.0，不新增依赖包。

| 声明/import | 实际类型与前提（省略宇宙参数） | 匹配与编译证据 |
| --- | --- | --- |
| `LinearMap.compLeft` / `Mathlib.LinearAlgebra.Pi` | 实模 E/F、`L : E →ₗ[ℝ] F`、索引 I；得到 `(I→E) →ₗ[ℝ] (I→F)` | `TimeGrid.map` 在原 Index 上使用；`dPlus_map/dMinus_map`，审计文件对 R/J/Q/G 各两次真实应用 |
| `LinearMap.toContinuousLinearMap` / `Topology.Algebra.Module.FiniteDimension`（由 Adjoint 引入） | 范数实空间、有限维域 X；将 `X →ₗ[ℝ] H` 升为连续线性映射，无需 H 有限维 | 对 `V.subtype.comp R` 使用，避免将 H/V 限成有限维 |
| `ContinuousLinearMap.adjoint`、`adjoint_inner_left` / `Analysis.InnerProductSpace.Adjoint` | 两实 Hilbert 空间；`A : X →L[ℝ] H` 的伴随 `H →L[ℝ] X` 满足 `⟪A†v,z⟫=⟪v,Az⟫`；X 完备性由有限维得到 | `Reconstruction.ofLinearMap` 是最小真实构造；`existsUnique_mass_adjoint` 给出原文 eq:massinterface，且实际编译/公理审计 |
| `Int.ceil_eq_iff`、`Int.floor_eq_iff`，`Fin.intCast` | 实数 floor ring，正 dt，N 非零 | `CellExtension` 两个 on_cell 定理直接证明原文半开单元取值及 0/T 端点；未另建周期索引 |

`Carleman` 实际构建闭包从 T001 的 2019 增至 2510 个 Lake jobs；新增 adjoint
缓存根已登记 `tools/setup_lean.sh`，其余版本和 manifest 不动。声明与传递基础公理
输出在 `tools/CheckAxioms.lean` 的实际 CI 日志。未采用清单中的其它工程。
