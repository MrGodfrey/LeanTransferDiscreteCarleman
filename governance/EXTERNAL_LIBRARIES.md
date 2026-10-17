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
