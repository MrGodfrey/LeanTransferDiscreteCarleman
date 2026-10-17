# 数学规格与桥接接口

依据 `paper/main.tex` / `paper/paper.pdf`（原 PDF 44 页，哈希见 `paper/SOURCE_MANIFEST.md`）。允许保留原始版本与清晰差异的论文修正、等价重述和证明路线调整，并同步本规格与覆盖映射；实质弱化最终结论或增加限制按 PROJECT_OPERATIONS 交用户决定。以下是实现规格与核对点，不是对全文数学正确性的重新审定。

## 原文目标

Theorem 2.1（`thm:main`，PDF p.10）保留 (A1)–(A4)、(N1)–(N5)、`eq:weightcoverage`、`eq:error-scales`、`eq:transfer-defects`、`eq:transfer-state-defect`。结论为 `eq:finalCE` 的载荷版本与由右逆推出的 `eq:rawCE` 残差版本。对所有允许的周期离散状态和两种方向成立，不能增添低频/频率截断或固定网格的限制。

固定结构数据及假设界以后，先选统一常数和阈值，再对所有允许的 T、h、δt、权函数与状态成立。统一性包括 T（TeX 330、387 行），不能为每个 T 任意另选常数；显式允许的参数依赖单独记录。

`X_h` 有限维；载荷空间 `𝔉_h` 仅要求原文范数空间条件，控制空间 `U_h` 不必有限维。`eq:massinterface`、`eq:transfer-compositions` 定义 R、J、Q=RJ、G=JR；不假定 Q 为投影或 G 为恒等。各映射独立于时间（pp.8–9，TeX 392–406）。

周期差分为 `D_+ zⁿ=(zⁿ-zⁿ⁻¹)/δt`，`D_- zⁿ=(zⁿ-zⁿ⁺¹)/δt`，伴随为 `D_+* = D_-`（p.10，TeX 495–500）。不能把 D_- 写成相反符号。共享模块统一 N>0、δt>0、T=Nδt、周期索引和加权 ℓ² 定义。

C001 共享接口位于 `Carleman/Periodic/TimeGrid.lean` 与 `SummationByParts.lean`：`TimeGrid` 存储 `N>0`、`δt>0`，`period=N*δt`，`Index=Fin N`，全部状态为 `Index → H`；`next/prev` 是互逆的模 N 移位。原文 TeX 477 使用 N≥2，本辅助恒等式对所有 N>0 成立。`dPlus/dMinus` 用实数逆的数乘表达向量除以 δt，`pairing=δt*∑ inner ℝ`。`pairing_dPlus/pairing_dMinus` 对任意实内积空间成立，因而包含原文的有限维实 X_h 及实 Hilbert 空间，无完备性或有限维限制。此处仅建立时间步长加权配对；空间权 σ、相应加权范数与延拓仍待后续共享模块。该辅助结果不清偿 B1–B5，不计 Section 5 或 Theorem 2.1 完成。

Corollary 2.2（`cor:general-scales`、`eq:scalerule`，p.11）中 α_x、α_t 的 minimum **略去分母为零的比值**。用非零条件筛选的有限集合或等价分支表达；不能沿用 Lean 实数除零等于零的默认值。Corollary 2.3（`cor:scales`）保留热算子参数与 4/5、2/5 指数。

## M2：有限、明确的桥接前提包

M2 连接真实空间、算子、权函数和范数，覆盖 Section 5 的 `eq:transfer-load` 至 `eq:transfer-absorption`（pp.19–20）。暂用前提逐项登记，后续证明后才消去：

| 接口 | 所需数学内容 | 后续来源 |
| --- | --- | --- |
| B1 冻结连续辅助解 | 对辅助载荷有满足周期端点的解 U，具备应用 (A4) 和误差估计的正规性，常数统一 | Lemma 3.4 `lem:frozen`；Lemma 3.1 `lem:graph` |
| B2 离散对应 | 给定状态 z 满足辅助离散方程；通过适定性/唯一性识别 u_h=z，或让误差估计直接适用于任意这样的 z | `eq:auxEuler`、`eq:transfer-load` 与 Sections 3–4 的适定性 |
| B3 权与延拓比较 | 节点权、连续权、分片延拓和冻结移位的统一比较，足以连接真实载荷、状态、观测和误差范数 | Lemma 3.2 `lem:cell`、`eq:cellbounds`、`eq:cellwise-extension` |
| B4 权族误差估计 | 所需每个权的统一能量/L² 误差，ε_E=a_E+η_A+√δt、ε_0=a_0+a_E²+η_A+δt | Theorem 3.5 `thm:timeerror`、Lemma 4.1 `lem:spatialEuler`、Theorem 4.2 `thm:combined` |
| B5 统一吸收 | 比较与误差组合产生统一 C；先固定 C 再取 c_* 使 C c_*≤1/2，并推出两种残差版本 | Section 5 `eq:transfer-comparison`、`eq:transfer-absorption` 及共享实数吸收引理 |

B4 的能量权为正指数时 `q^((c_j-2(m-j))/2) θ`，否则 θ；L² 权包括 `q^(c0/2)θ`、`q^(o/2)θ`、`q^(2m)θ`，须由 `eq:weightcoverage` 覆盖。冻结移位和误差项不能另用未经匹配的抽象标量代替。

该表是需要逐项关闭的接口清单，不要求把 B5 整个结论直接当作假设。已在 M2 证明的接口从额外前提中移除；真正暂用的条款完整登记在 `extra_hypotheses`，写明量词/常数和预期消去目标。B2 可用等价证明架构，不机械复制原文唯一性步骤。单独实数吸收引理只算 AUXILIARY；直接假设最终离散估计不算 M2。

## 分层成果与模块复用

- 条件性 Section 5：`scope=CONDITIONAL`，逐项列出上述尚未证明的桥接条款；即使核对完成也不计入原文目标完成。
- 原始 Theorem 2.1：`scope=PAPER`，只保留原文前提，消去新增桥接前提；(A1)–(A4)、(N1)–(N5) 不属于额外前提。
- 具体应用：验证热方程/格式满足抽象前提。Proposition A.3 是应用层依赖，并非抽象 Theorem 2.1 要无条件证明 (A4)。

共享周期序列、加权范数、R/J/Q/G 和误差接口放在独立 Lean 模块；改变接口时同 PR 更新调用者与规格。首轮先完成书面规格、基础对象和小证明，完整主定理类型随接口建立逐步落实。

Section 3 保留 L² 的 δt 阶和能量 √δt 阶；Section 4 保留 a_E+η_A 与 a_0+a_E²+η_A。后续覆盖全部结果见 `PAPER_COVERAGE.md`；附录的证明位置映射到对应结果，避免重复计数。
