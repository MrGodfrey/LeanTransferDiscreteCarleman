# T253 / C269 独立本机验收

- checked_sha: `032d2ae56bb04dd52015641301e4f4903fc0a1ab`
- mathematical_base: `51c2b03bbc06cc44d7d55e9bb12a91bbb7971285`
- reviewed_at: `2026-10-20T10:04:07+00:00`
- reviewer: 独立本机 Agent `accept_spatial_lemma`
- result: **PASS，11/11 显式声明（10 定理、1 定义），未发现缺陷。**
- axiom_check: **PASS**
- accepted_scope: **AUXILIARY；原盒域 H²∩H¹₀ 的同一光滑零边界序列，在完整原 H² 弱 jet 图拓扑中强收敛。保持 18/26，P023 不提升。**

已完整读取固定 `Carleman/Spatial/BoxStrongH2Density.lean`、全部 raw 完整类型及公理、analysis/MATH_SPEC/台账，并核对原稿 `paper/main.tex:2659–2665`。本批为原 Corollary A.2 的后续边界密度路线提供盒域的完整拓扑接口，不证明一般曲边域密度，也未把经典统一 Hessian 估计传递到所有原弱状态。

## 实际数学、假设及量词

1. **全部分量重建真实 L² 场。** `derivativeFieldAssembly` 是有限 Sym 坐标注入及求和构成的实际 CLM，`derivativeFieldAssembly_component` 精确恢复每个分量。新重建定理经 `derivativeComponent_ext` 得整个向量 L² 类相等；后者使用有限坐标的 AE 身份和真实 Lp.ext，不用任意代表的处处值。分量收敛先在有限函数空间中给乘积极限，再由同一装配 CLM 的连续性得到完整欧氏 L² 场极限，最后以重建恒等式识别原 Uₙ/u。没有以标量零阶收敛代替高阶字段，也没有输入一个未经证明的有界逆。
2. **完整原 jet 拓扑。** `WeakSobolevJet` 是 0,…,m 各阶真实 L² 导数字段有限乘积中的弱链子空间。新定理先对每阶使用上项，再经 `tendsto_pi_nhds` 与 `tendsto_subtype_rng` 返回该真实子类型拓扑。已读 `SobolevTopology`：规范是有限乘积图范数，原全部分布测试身份给闭性及完备性；该规范等价于全部阶 L² 范数之和。这里没有把 value 映射的 L² 诱导拓扑当成 Hᵐ 图拓扑，也没有误称两种数值规范完全相等。泛型结论适用于任意给定 m、d 和局部有限资格的 ν，不要求空间测度整体有限。
3. **全空间测试的实际全阶限制。** `allOrderJetOn φ S m` 明确定义为 `restrictSubdomain(S⊆univ)(φ.allOrderJet m)`。实际 allOrderJet 用光滑迭代方向导数、排序词置换不变性和原完整弱测试身份构造所有字段；限制映射逐字段取真实 subdomainLp，并通过原子域测试的支撑消去域外积分来保存全部弱链。新 component 身份沿 `derivativeComponent_subdomain`、原 allOrderJet_component、两次 toLp_ae 及真实限制测度单调性证明。结果是同一 φ.multiTest 的实际受限 L² 类；value 的零阶 Sym.nil 身份也精确恢复 φ.toLp。没有假设原任意 H² 状态的全空间零延拓仍然 H²，也没有增加域外正则性。
4. **一、二阶的准确 AE 代表与方向顺序。** 一阶分量是实际 D_{v₀}φ。二阶 `v₁::v₀::nil` 经 multiTest_cons 先得到 D_{v₁}(D_{v₀}φ)，即实际二阶 CLM 的参数次序 [v₁,v₀]；`coordinateDerivative v` 则展开为 iteratedFDeriv 的 [v₀,v₁]。源码先用真实 CLM 求值微分，常基向量的导数项为零，再明确调用 φ 的 C∞ 所给 `isSymmSndFDerivAt` 交换二阶参数。没有仅凭 Sym 标签忽略经典导数次序。所有最终等式均为原 `volume.restrict S` 下的 a.e. 身份，不给任意 Lp 类增添节点或边界点值。
5. **误差辅助接口与最终密度输入区分。** `allOrderJetOn_two_tendsto_of_errors` 明确把 h0/h1/h2 作为辅助输入；它覆盖 k=0,1,2 的每个 Sym 指标，零阶用唯一 nil，一阶拆一次 cons，二阶拆两次 cons 后使用向量 `![i,j]`。每一项调用实际 `lp_tendsto_of_representative_L2_error`：原 Lp 差的范数经 Lp.coeFn_sub 和已证 AE 代表身份，等于给定 Bochner L² 误差。因此误差有限性来自真实 Lp 类，不能以无穷 eLpNorm 的 toReal 默认值伪造极限。最后将全部分量收敛通过第 1、2 项装配。最终盒域定理没有保留这些误差输入，而是内部调用已有真实构造取得它们。
6. **同一原状态、同一序列及完整边界。** 最终输入是任意正边长坐标盒上的原完整弱 H² jet u，以及其 H¹ 截断属于实际 `dirichletJetSpace`。直接重读 `exists_box_dirichlet_compact_h2_approximation` 及其调用：原 negativeLaplacian 由 u 的实际二阶字段内部给出，奇 Poisson 扩张及已证扩大盒 H² 正则性得到同一状态的扩张；开放原盒上的全弱 jet 值单射识别限制等于原 u。真实全偶卷积给所有一二阶误差及统一尾段的全部 frontier 零值。一个固定紧支光滑截断在原盒闭包上等于 1，使同一序列全空间紧支；开盒内局部相等保持所有经典导数。没有为不同分量分别选择不同序列、子列或目标状态。新定理直接保留该同一 U，继而证明其完整 H² 极限恰是原 u。
7. **每项是真正 H¹₀，而非另加边界条件。** 对 Uₙ 的完整 H² jet 截断，value 身份给 Uₙ 的原域 L² 类。盒的开放、凸、有界、非空条件均由 aᵢ<bᵢ 内部供应，再调用实际 `smooth_boundary_zero_mem_dirichletJetSpace`。该定理已读：真实边界零值使 indicator 跨边界 Lipschitz，内缩/光滑逼近进入原 H¹ 图拓扑中的测试闭包，最后由同值合法 H¹ jet 的唯一性识别当前截断。`dirichletJetSpace` 确为原域紧支测试 span 的 H¹ 拓扑闭包，不是预设的点态零边界子集。因此所有 n 同时具备真实 H¹₀ 资格，无须把它作为近似序列额外输入。
8. **范围与退化维数。** Uₙ 是 `SpatialTest univ`，并在原真实 frontier 上处处为零；没有要求它属于 `SpatialTest S`、在边界邻域消失或法向导数为零，故未把 H²∩H¹₀ 偷换成 H²₀。最终量词先选一个 U，再要求所有 n、所有边界点及完整 H² 强收敛；无统一收敛速率或随盒变化的算子范数声称。d=0 时正阶 Sym 纤维为空、零阶仍为单一 nil，有限装配与分类均合法；盒的几何和底层密度定理也允许该退化情形。一般 S 的限制/分量身份不擅自要求 S 光滑，H¹₀ helper 的凸有界开放非空条件则明确保留并在盒实例清偿。

## 全部声明逐项结论

声明省略共同前缀 `Carleman.`；源码行为固定 `BoxStrongH2Density.lean`，raw 行为固定完整类型起点。清单从固定 T253/C269 台账分别提取，两份完全一致，并独立与源码及 raw 比对。

| 源码 / raw 行 | 声明 | 结论 |
|---|---|---|
| 15 / 44127 | `derivativeFieldAssembly_components` | PASS；所有真实分量装配后恢复同一向量 L² 类。 |
| 21 / 44131 | `derivativeField_tendsto_of_components` | PASS；有限坐标乘积极限经真实装配 CLM 转为完整场强极限。 |
| 30 / 44140 | `WeakSobolevJet.tendsto_of_components` | PASS；全部阶字段与原完整弱 jet 子类型拓扑。 |
| 42 / 44149 | `SpatialTest.allOrderJetOn` | PASS（定义）；实际全阶光滑 jet 的原域弱限制。 |
| 46 / 44152 | `SpatialTest.allOrderJetOn_component` | PASS；每阶每个 Sym 分量是实际受限 multiTest L² 类。 |
| 58 / 44157 | `SpatialTest.allOrderJetOn_value` | PASS；精确零阶原 L² 身份。 |
| 64 / 44161 | `SpatialTest.allOrderJetOn_component_one_ae` | PASS；真实一阶方向微分的受限 AE 身份。 |
| 72 / 44167 | `SpatialTest.allOrderJetOn_component_two_ae` | PASS；实际二阶链式、方向次序与真实 Hessian 对称性。 |
| 92 / 44173 | `SpatialTest.allOrderJetOn_dirichlet` | PASS；真实 frontier 零值内部给原 H¹₀ 闭包资格。 |
| 100 / 44179 | `SpatialTest.allOrderJetOn_two_tendsto_of_errors` | PASS；真实代表误差、全部 0/1/2 阶 Sym 覆盖及完整强极限。 |
| 139 / 44205 | `exists_box_dirichlet_strong_h2_approximation` | PASS；全部原 H²∩H¹₀ 状态的同一紧支光滑零边界序列、每项 H¹₀ 及完整 H² 强收敛。 |

## 固定依赖与本地证据

实际 Carleman 导入闭包 **259 文件**，其中 **258 旧文件**相对 mathematical_base 逐 Git blob 不变，唯一新增数学模块为本批模块。直接读取实际 `DerivativeFieldAssembly`、`SobolevJet`、`SobolevRealization`、`SobolevTopology`、`SpatialTestAllOrders`、`SubdomainRestriction`、`SmoothLaplacianL2Limit`、`BoxCompactSmoothDensity`、`BoxDirichletSmoothDensity`、`SmoothBoundaryDirichlet`，并核对 coordinateDerivative 的原定义及一二阶公式。没有以旧报告替代实际新调用、测度限制和方向次序核查。

进一步独立比较既有已接受版本的关键完整闭包：`BoxCompactSmoothDensity` 的 **254 文件**和 `SmoothLaplacianL2Limit` 的 **256 文件**均与 T160 proof `d5a8ab859e4413c6eb950702df73990e356c3786` 不变；`SpatialTestAllOrders` 的 **78 文件**与 T216 proof `17b0a22b45b9d314f90414b72d3c3198ef129f0d` 不变；`SmoothBoundaryDirichlet` 的 **118 文件**与 T138 proof `d1dca8884990c684f923a4938e40a6cc88e1645f` 不变。原盒密度入口的实际实现及 T159/T160 冻结报告已重读，未把给定逼近误差当作最终原状态前提。

相邻 T252 冻结报告亦已全文读取并核对单文件提交 `313d9a74553d37d3f013422560a21efe5279e569`，checked_sha 为本报告 base、reviewed_at=`2026-10-20T09:56:02+00:00`，14/14 PASS；当前固定 proof 中报告逐字节相同（11033 bytes，SHA256 `1569a58928d462027024897eb0f876cc38da6acc9a97413cbfbe5099b5c407e9`）。本批盒密度没有借该固定图传输接口声称一般曲边域密度已经完成。

Lean **4.35.0**，编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib lock 与实际无修改 checkout 同为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。11 项名称、命名空间、顺序及 10 theorem/1 def 与固定源码、T253/C269 台账、raw 精确匹配；根导入和全部 `#check`/`#print axioms` 齐全。AGENTS、PROJECT_OPERATIONS、state/README 与此前已读协议摘要一致。

- `/tmp/carleman-t253-local-evidence.json`：source=local、PASS，checked/source 均为本报告 proof，finished_at=`2026-10-20T09:58:53.549877+00:00`；实际 `lake build Carleman` 和 `lake env lean tools/CheckAxioms.lean` 执行记录均 exit 0。
- `/tmp/carleman-t253-local-source-manifest.txt`：**1050 项、113967 bytes**，SHA256 `88b9daaa4a113b6c736c11d40d2b304ee5ae834187706ffbc96a11d7a0dd340b`。独立枚举固定提交全部 tracked `.lean` 和三个工具链配置，路径集合、唯一性及各项摘要全部匹配实际 Git blob。
- `/tmp/carleman-t253-target-build.log`：**3439 jobs** 成功，107 bytes，SHA256 `5662ef3eafda87b645997d4e1feb201876310f28131fc5c6b7191af40a96bff8`。`/tmp/carleman-t253-build.log`：**4292 jobs** 成功，80 bytes，SHA256 `c5417c22f4e844b9f5ad447e8d6ae7da24d3f9176206646a828e849a252d5ad7`。`/tmp/carleman-t253-axioms.log` 为 0 bytes。
- `/tmp/carleman-t253-box-strong-h2-density-local-axioms.txt`：**3399885 bytes**，SHA256 `41f0b0fc17b5e17ef4b318e2d3b041d8d6e54eb7513c2b0f27ab90b8a44918c3`。11 项完整类型与公理逐项核对；全文件 4058 个公理列表均仅含 `propext`、`Classical.choice`、`Quot.sound`，另有 10 个无公理记录。实际末行确认 **10108 声明递归审计 PASS**；全命名空间 `privateToUserName`/`collectAxioms` 白名单逻辑相对 base 不变，无 sorryAx 或新增数学公理。
- 原稿相对 base 不变，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本次核对固定本地执行证据，未重跑全库、未查询远端 CI/看板，未将本地成功称为 CI 成功。

无修复项。接受 **AUXILIARY 原盒 H²∩H¹₀ 的完整 H² 拓扑光滑零边界逼近**，保持 18/26。正文与 reviewed_at 冻结后仅单文件提交本报告，不修改数学、台账、原稿、根导入、公理工具或其他报告，不 push。
