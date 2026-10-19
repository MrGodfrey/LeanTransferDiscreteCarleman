# T136 / C152 独立本机验收

- checked_sha: `fe4cd0a34c2c118548b17ce534eae0f210bea70c`
- base_commit: `7ad1a9dd94d3abfe384564b1f24f351f5c60fe21`
- reviewed_at: `2026-10-19T08:00:17+00:00`
- reviewer: `/root/accept_section3`，独立于实现者。
- 结论：**PASS / AUXILIARY**。三模块全部 18 项声明通过数学、类型、依赖及同版本 CI 验收。C152 可记为 REVIEWED，保持 AUXILIARY；P020 不升级，原论文覆盖保持 **15/26**。

## 审查依据与版本隔离

从固定 Git 对象读取 AGENTS.md、PROJECT_OPERATIONS、state/README、MATH_SPEC、`governance/analysis/T136-refined-chain.md`、三模块完整源码及 `paper/main.tex`；核对固定声明清单、原始完整类型与递归公理结果。没有使用变化中的工作树、动态 `.ci/axioms.txt` 或后续多维实现代替本次证明。固定根模块导入全部三模块；声明清单与固定 C152/T136 登记一致。

原文对应 Proposition 7.8（`prop:filter-fd`），`paper/main.tex:2241–2274`，尤其 2251–2271 的一维部分。原目标最终是实际粗插值像空间的 Rayleigh 上界 `12 Σ H_r⁻²`；本批提供其一维有限和基础。原 P019 已有独立 PAPER 验收，但不是这三模块的数学依赖。

## 逐项声明核验

下表名称均带命名空间 `Carleman.`；行号对应固定源码。每项同时核对实际完整类型和证明，而非仅核对名称或执行者说明。

| # | 声明 | 固定模块／行 | 独立判断 |
|---|---|---|---|
| 1 | `linearRefinementValue` | LinearRefinementCell:18 | PASS。真实值为 `a + (k:ℝ)/(m:ℝ)*(b-a)`，没有抽象插值参数。 |
| 2 | `linearRefinementMass` | LinearRefinementCell:21 | PASS。逐细边两端平方的梯形和；不是连续一致质量的别名。 |
| 3 | `linearRefinementEnergy` | LinearRefinementCell:25 | PASS。全部 `k < m` 的实际相邻值差平方和。 |
| 4 | `sum_affine_sq` | LinearRefinementCell:28 | PASS。自然数归纳得到实际仿射平方和；`n-1` 在实数中运算，`n=0` 也成立。 |
| 5 | `linearRefinementMass_eq` | LinearRefinementCell:35 | PASS。两次平方和计算给 `m(a²+ab+b²)/3 + (a-b)²/(6m)`；仅需 `m>0`。 |
| 6 | `linearRefinementEnergy_eq` | LinearRefinementCell:54 | PASS。每条差精确为 `(b-a)/m`，总和为 `(b-a)²/m`。 |
| 7 | `linearRefinement_inverse` | LinearRefinementCell:64 | PASS。由前两等式与非负平方推出 `energy ≤ (12/m²) mass`，不输入目标逆估计。 |
| 8 | `uniformLinearProlongation` | UniformLinearProlongation:11 | PASS。实际使用 `k/m` 与 `k%m` 选择粗单元和单元内坐标。 |
| 9 | `linearRefinementValue_zero` | UniformLinearProlongation:14 | PASS。零端点值为 `a`，此基础身份甚至不要求 `m>0`。 |
| 10 | `linearRefinementValue_end` | UniformLinearProlongation:17 | PASS。`m>0` 时右端点 `k=m` 的值精确为 `b`。 |
| 11 | `uniformLinearProlongation_node` | UniformLinearProlongation:22 | PASS。所有粗节点 `m*j` 精确恢复 `u j`。 |
| 12 | `uniformLinearProlongation_cell` | UniformLinearProlongation:26 | PASS。实际公式对整个闭单元 `0≤k≤m` 成立；右端点单独用下一粗节点身份处理。 |
| 13 | `sum_uniform_blocks` | UniformLinearProlongation:38 | PASS。`range (m*K)` 精确分成 K 个长度 m 的块；没有遗漏项、重复项或额外整除假设。 |
| 14 | `uniformLinearProlongation_energy_cells` | UniformLinearProlongation:46 | PASS。全部细边能量精确组装；末边需要并实际使用 `k+1≤m` 的闭单元公式。 |
| 15 | `uniformLinearProlongation_mass_cells` | UniformLinearProlongation:60 | PASS。梯形质量精确组装；共享粗节点由相邻半权正确计数。 |
| 16 | `trapezoid_square_sum` | RefinedChainInverse:11 | PASS。保留精确端点修正 `(z_n²-z_0²)/2`，自然数归纳覆盖空和。 |
| 17 | `uniformLinearProlongation_inverse` | RefinedChainInverse:18 | PASS。仅由原零端点消去修正，再逐单元求和得到原对角节点质量；没有 K 因子。 |
| 18 | `uniformLinearProlongation_physical_inverse` | RefinedChainInverse:34 | PASS。恢复真实正步长 h、前向差商 `/h` 与质量因子 h，右侧常数严格为 `12/(m*h)²`。 |

## 原文保真、量词和边界情况

独立代数复核给出

`(12/m²) mass - energy = 3(a+b)²/m + 2(a-b)²/m³ ≥ 0`。

因此 12 对任意正整数 m、任意实数端点 a、b 统一，允许符号混合；证明不诉诸范数等价或未证连续逆估计。质量修正项方向为正，系数与分母均准确。

令 `H=m*h`，单元物理质量的代数表达是

`h*mass = H(a²+ab+b²)/3 + (h²/6)*(b-a)²/H`，

而物理边能量是 `(b-a)²/H`。这与原文的连续线性单元质量加 `h²/6` 倍能量修正完全相符。本批 Lean 直接证明有限和身份和不等式，并未构造连续 `v_H` 或声称已形式化上述连续积分解释。

最终声明量化所有 `m,K : ℕ`，仅要求 `m>0`；所有粗数据 `u : ℕ → ℝ`，仅有 `u 0=0`、`u K=0`；物理式再要求 `h>0`。常数 12 先于且独立于这些数据。`m=1` 不被排除；`K=0` 是空和且端点条件一致。各闭单元公式覆盖右端点，故实际目标只取决于 `u 0,…,u K`，终点定义表面出现的 `u(K+1)` 系数为零，不造成额外数据约束。

边差和包含从 0 到 `m*K-1` 的所有边，覆盖两端边界。节点平方和取 `range (m*K)`，包含零值左端、排除零值右端，因而精确等于原内部节点对角平方和。端点修正先显式计算，再凭原零边界消去，没有把梯形质量无条件当作对角质量。乘以 `h⁻¹` 恢复物理能量，右侧同步成为 `12/H²` 乘原质量 h；不存在缺失 h、额外单元数量或长宽比常数。

范围限制明确：本批未构造多维张量插值、未将此有限和结论接到原物理 Hilbert 空间及实际差分算子，也未建立插值像 F 的实际 Rayleigh 上确界。因此不能单凭本批将完整 Proposition 7.8 / P020 标为 PAPER 完成。这是已声明辅助范围，不是所提交 18 项中的缺陷。

## 依赖与公理

三模块的 Carleman 依赖闭包恰为本批三模块：`RefinedChainInverse → UniformLinearProlongation → LinearRefinementCell`；首模块只导入 mathlib 的实数、有限和、域运算及证明策略。没有旧 Carleman 解析、Carleman 估计或数值假设的外部依赖，无循环，也无把目标离散估计作为输入。

固定新源码没有 `sorry`、`admit`、新增 `axiom` 或 `native_decide`。18 项打印出的递归公理均仅为 `propext`、`Classical.choice`、`Quot.sound`。原始产物中 2466 个非空打印记录及 8 个无公理记录均无其他公理；最终全库递归审计为 **7011** 声明 PASS。完整打印记录数不是自动生成声明总数；已核对 `CheckAxioms` 的 `privateToUserName`、`collectAxioms` 遍历及递归检查，审计实现与基线一致。

Lean 固定为 4.35.0，CI 编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，与锁定版本及实际干净依赖一致。原稿与治理协议在本阶段未变。定向日志实际完成 1103 jobs，全库日志实际完成 3935 jobs。

## 独立远端证据核验

独立查询 [main CI 39219003258 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39219003258/attempts/1)，事件为 push，分支 main，`head_sha=fe4cd0a34c2c118548b17ce534eae0f210bea70c`。run 最终 `completed/success`，更新时间 `2026-10-19T07:58:27Z`。三项任务均独立读取为 `completed/success`：

| job | ID | 结果 |
|---|---|---|
| lean | 117949610009 | success |
| state-check | 117949610179 | success |
| dashboard / snapshot | 117951110810 | success |

本验收者通过 `gh run download` 自行下载同次 run 的两份原始产物，未使用执行者转述替代：

- `lean-ci-result`，artifact ID **12171131605**，归档 491 bytes；archive digest `sha256:94d8658d7ec86b27fbb19c8523ebf43d79ad0d235a866d8e0d07f83848a6719e`。
- `lean-declaration-evidence`，artifact ID **12170992486**，归档 198776 bytes；archive digest `sha256:d00837242361a050c5a77351b34566a4a12c4f57c8eaaff3a970422f21dad775`。

实际读取 [result.json](/tmp/carleman-t136-fd-filter-main-ci/result.json)：`status=PASS`，`checked_sha` 与 `source_head_sha` 均等于本报告固定 SHA，目标 `Carleman`；`finished_at=2026-10-19T07:56:55.267800+00:00`。此时间是证明结果时间，最终 run 成功时间另见上文。

下载的 [原始 axioms.txt](/tmp/carleman-t136-fd-filter-main-axioms/axioms.txt) 与 [固定本机副本](/tmp/carleman-t136-fd-filter-local-axioms.txt) 经本验收者直接字节比较完全相同：均 **2152839 bytes**，SHA256 均为 `12fcf4ad8a59a9cf6c1267be692e86458997f4f9498637a194d0a5291c975954`。末行明确为 `Axiom audit passed for all 7011 Carleman declarations.`；清单 18 项均有对应完整类型与公理证据。

未发现需要修复的问题。以上签发仅涵盖固定版本与明示辅助范围；签发后冻结本报告内容及 reviewed_at。
