# T020 — Section 4 空间误差的精确恒等式

从实际已合并基线 `bce9be563a26a373585eb6d7f705d6fc5e2becf2` 接续，
初始分支 `proof/t020-spatial-identities`，按用户本机开发指示已快进并推送 main。PR22 已合并，main CI
[39089488235](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39089488235)
的 lean、state-check、dashboard 三项实际成功。本地任务按用户要求接续云端检查点；
原 Lean 4.35.0 和 mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 不变。

T019 台账从 REVIEW 修正为实际 MERGED；其原文级声明维持 BUILT，
本次没有把 GitHub 合并或构建成功等同于独立语义验收。

## 精确声明与原文对应

1. `sum_variable_bilinear_increment` 对任意有限置换和节点相关对称双线性形式
   证明精确能量恒等式。`TimeGrid.pairing_variable_operator` 将其应用于
   `inner v (T_n w)`，得到原 `eq:weighted-time-summation`。
   D+ 的负贡献使用 `T_next − T_current`；D− 自动使用相反方向的邻点。
   不要求不同节点的测试算子交换，不把它们限制为标量乘法。
   `pairing_variable_operator_lower` 仅在丢弃增量能量时使用正半定性。
   `testOperator_cell_increment` 从真正的二次型时间导数及单元上的统一界
   推出节点差分界；`pairing_testOperator_dPlus_lower/dMinus_lower` 接入两方向。
   周期最后一格通过 T(0)=T(T) 处理。N4 的权依赖导数界与已证单元权比较
   之间的具体常数组合仍待接入，未把它直接记为完成。

2. `spatial_continuous_test` 从原 D(A) 上的 Euler 方程和原算子测试等式
   得到 V 上的变分方程；`spatial_discrete_test` 从实际
   `Dε z + A_h z + μ G z = J f` 得到重构测试方程。
   `spatial_error_equation` 相减得到原 `eq:thetaEuler`：
   `e_h = z − Ju`、`η = u − Q u`，刚度缺陷的两项和符号均保留。
   形式仅要求代数双线性；没有把 V 的 H 诱导范数充当 H^m 能量范数。

3. `spatial_consistency_identity` 证明完整误差恒等式的逐节点版本。
   `spatial_complete_identity` 用原周期差分伴随和实际反向对偶方程求和，
   保留三项：`(Dεu,Y−QY)`、`a_μ(e_s,Y−QY)`、`b_h(z,JY)`。
   `spatial_weighted_duality` 在实际对偶载荷 `W² e_s` 下把左端识别为
   `dt ∑ ‖W_n e_s,n‖²`。W 为任意对称线性权算子，允许权乘法是其预期实例。
   对偶解目前作为满足原方程的任意解输入；本阶段未包装 Section 3 的解构造。

4. `existsUnique_auxiliaryEuler` 在论文要求的有限维 X 上，将既有全状态
   唯一性提升为任意载荷的存在唯一性。只用原 N1 的 R 单射、A_h 非负及正 μ；
   不需要 Q 投影、G 恒等、正交重构、频率截断或步长限制。

5. `weightedFieldMap` 收集全部实际加权弱导数字段到 Hilbert 乘积。
   `weightedSeminorm_apply` 证明所得半范数恰为现有 `weightedNorm`；
   三角不等式和原 V 上的 `conformingWeightedSeminorm` 随之获得。
   没有以 H 范数替代 H^m，也没有把空间能量重新定义成与原文未识别的标量。

`SeminormAlgebra` 进一步证明真实 dt 加权序列范数的三角不等式、节点比较和 Cauchy–Schwarz；节点移位形式/刚度缺陷的界以同一个常数提升到序列范数。

七个模块均由 `Carleman.lean` 导入；35 个显式声明加入 `tools/CheckAxioms.lean`。
声明与构建证据以唯一任务台账和 PR 为准。

## 完成边界和接续

C038 为 AUXILIARY。它证明原 Section 4 使用的恒等式和适定性，
不代表 Lemma 4.1、Theorem 4.2 或原 Theorem 2.1 已完成；原文覆盖表不提升。
论文源码未修改。全部恒等式同时覆盖两时间方向、任意网格周期和全节点状态。

下一步把原 N4 的权依赖导数界和已证单元权比较接入已证算子增量引理，
用 Section 3 任意 B 的 coercivity 余量吸收。再把 N3、N4 superapproximation、
N1 stiffness defect 逐项接入真实 N/R 范数，得到 `a_E+η_A` 能量界。
完整对偶恒等式的三项分别产生 `a_0`、`a_E(a_E+η_A)` 和 `η_A`；
利用 `a_E≤1` 得到 `a_0+a_E²+η_A`。最后与真实时间误差、延拓比较组合。
不得把这些待证界放入新的“原假设”结构来宣称原文完成。

## 本机构建检查点

`3f85627f55d297e62ec124f6d9d22cf52ac85833` 本机完整 Carleman 构建3431 jobs成功，递归2940声明公理审计成功，仅正常基础公理。PR CI39132012222三项成功，实际测试SHA为`3832dbcae75558861ee911c0151f1d9c5a44697b`，与源码HEAD的tree同为`406b54232165cf21e299d8681c7fde3cc62ee018`。已核实测试提交的两个父节点为原main基线和源码HEAD。直接push main后PR23自动标为MERGED；后续在main继续，不新建常规PR。C038记录为BUILT/AUXILIARY，未据此提升原文覆盖。
