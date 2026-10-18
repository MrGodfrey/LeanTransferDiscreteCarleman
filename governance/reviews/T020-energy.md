# T020 能量阶段声明核对

执行者对本阶段声明的陈述及依赖接口核对；不是完整 Lemma4.1 或其独立验收。
构建的精确版本和实际 CI 以唯一台账为准。原文及界限见[分析记录](../analysis/T020-spatial-energy.md)。

| 声明 | 核对事项 |
| --- | --- |
| `SpatialProfile.test_mass_cell_le` | 真正 qσ 的 L² 范数，使用原 q 与权乘子单元比较，常数 6。 |
| `SpatialProfile.test_derivative_cell_bound` | N4 真正二次型导数、真实 R 的 L² 值；闭单元界 36C，无有限差分替代导数。 |
| `SpatialProfile.pairing_test_dPlus_lower` | D+ 精确求和与左节点比较，完整 dt 因子、质量余量 18C。 |
| `SpatialProfile.pairing_test_dMinus_lower` | D− 右端点比较，周期末格经 q 和 σ 的端点身份，不丢掉节点零。 |
| `Reconstruction.spatial_test_stability` | 由超逼近及 σ² 的乘法界推导 Ct=ε+CM，不预设测试稳定性。 |
| `Reconstruction.spatial_test_node` | 原误差方程测试，形式与刚度缺陷两处符号保留；质量余量尚未丢弃。 |
| `Reconstruction.spatial_test_energy_bound` | 真实时间有限和，质量余量相消，两个缺陷仅消耗 c/2；零范数分支合法。 |
| `squared_weight_test_uniform` | 原闭包光滑 profile 与正逆权保持；常数先于 w、τ、t、全 V 状态，未扩大权族。 |
| `OriginalForm.bilinearForm` | 原连续有界双线性形式通过原 V 的线性等价搬回，无拓扑替换假设。 |
| `OriginalForm.bilinearForm_apply` | 与既有 scalarForm 定义严格相同。 |
| `Section4.energySeminorm` | 节点真实加权弱 Sobolev Nm 半范数；由此前证明等于原范数。 |
| `Section4.spatial_cea` | 全 V、X 状态，两方向；从两实际 Euler 方程推导误差方程和 N4 时间界。形式与乘法供应定理尚待最终统一入口组装。 |
| `TimeGrid.weightedNorm_sum_le` | 实际 dt 加权半范数的有限 Minkowski，零和情形覆盖。 |
| `TimeGrid.weightedNorm_le_field_sum` | 各阶导数值域可不同；逐节点误差界提升，无网格数因子。 |
| `WeakSobolevJet.weightedNorm_truncate_le_parameterNorm` | 原弱 jets 截断、q≥1 和 m≤n；固定 m+1 常数，非反向椭圆界。 |
| `WeakSobolevJet.nodal_approximation_bound` | 逐节点 R 界到 Section3 的真实 sum-of-L² R 范数，能量和 L² 误差均可实例化。 |
| `Section4.conforming_energy_le_parameterNorm` | 经弱导数唯一性识别原 D⊆V 两阶 jets，然后应用已证截断界。 |

全部名称带 `Carleman.` 前缀。所有模块从根目标导入，显式声明均进入递归公理检查。不得把当前 Céa 条件式或未组装的常数阈值当作完整原空间误差定理。

本机执行 `bash tools/lean_ci.sh` 实际成功：3437 build jobs，2973 个 Carleman 声明递归公理检查通过，仅正常基础公理。17 个新增显式声明的类型和公理报告已输出。此记录不冒充远端 CI；精确源码版本和实际 main CI 在读取成功记录后绑定。

实际 main 提交 `010b37869003458f0e1436e3804e11c807f550e9` 的 [CI39133477530](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39133477530/attempts/1) lean、state-check、dashboard 三项全部成功。下载的声明及公理产物与本机逐字节相同，SHA256 `f07f0ed4bf81cdaee4e34a91dfdb4905d03ef1fc94510ad9d5195f636f90cef7`；17 个新显式声明均仅依赖正常基础公理。C039 绑定此版本记录为 BUILT/AUXILIARY，未作独立论文级验收或覆盖提升。
