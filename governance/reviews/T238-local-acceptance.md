# T238 / C254 独立本机验收

- checked_sha: `8cf9572cab17a3474e176724f820509861b8bf09`
- mathematical_base: `77a0dc79f9a1d256ecae73c15a7e8eebe10ce6c1`
- reviewed_at: `2026-10-20T07:57:49+00:00`
- reviewer: 独立本机 Agent `accept_spatial_foundations`
- result: **PASS，11/11 显式声明（10 定理、1 定义），未发现缺陷。**
- axiom_check: **PASS**
- accepted_scope: **AUXILIARY；真实非线性剪切的全测试弱链式、同一状态完整 H¹ 传输及 H¹₀ 闭包保持。覆盖保持 18/26，P023 不提升。**

已完整读取固定 `Carleman/Spatial/GraphShearWeakTransport.lean`、全部 raw 完整类型和公理、analysis/MATH_SPEC/台账及原稿 `paper/main.tex:2659–2665`。另直接读取真实剪切和限制测度、弱测试、弱乘积、一阶字段组装、H¹₀ 闭包与值唯一性等相关实现。原 Corollary A.2 要求完整 Dirichlet 实现与一般凸域正则性；本批只是其边界图路线中的弱一阶传输，不能直接算作该原文命题完成。

## 实际对象与数学核对

1. **原域与真实测度。** F(x)=x+ψ(x)e_r 是 T237 的实际 homeomorphism，逆为 x−ψ(x)e_r，假设 ψ 沿法向全部实平移不变。T 为任意原目标开域，S 字面等于 F⁻¹T；两端分别使用 `volume.restrict T` 与 `volume.restrict S`。真实 Jacobian=1 和限制换元已在旧实现内部证明，`homeomorphPullbackLp F hm` 因而是这两个原 L² 类之间的真实复合线性等距 P，AE 值为 u∘F。没有任意密度、替代域、额外保测度前提或有限体积假设。ψ 的全局 Lipschitz 假设控制斜率，不要求高度函数本身全局有界。
2. **先证明真实法向弱链。** 对任意原弱 D_ru=v 和任意 S 内真实紧支光滑测试 φ，令 χ=φ∘F⁻¹。支撑条件 `F.symm⁻¹'S⊆T` 由 F(F⁻¹x)=x 内部给出；χ 的全局光滑和紧支资格由实际逆 homeomorphism 供应。原分布积分身份经真实保体积换元传到 χ。逆测试链式中的法向修正为 `(D_rψ)D_rφ`，已证明 D_rψ=0，故严格得到 D_r(Pu)=Pv。该 helper 甚至不需 Lipschitz 或 T 开放，只需相应原测试身份与真实光滑剪切；没有先假定变换后弱导数。
3. **零导数乘子的合法弱乘积。** `mul_of_derivative_zero` 从已有 D_eu=v、实际有界且域内光滑 w、真实 AE 身份 D_ew=0 出发，构造零导数乘子并验证其 map 为零。调用的原弱乘积公式通过测试 wφ 得到 D_e(wu)=wv+(D_ew)u，随后才消去零项。原测试的紧支在开域内，使 wφ 成为真正全空间紧支光滑测试；并非把形式 Leibniz 法则当成假设。用于斜率时，w=D_iψ 是已证明的实际有界乘子，其法向导数为零由 T237 的实际斜率平移不变性供应。
4. **完整弱链式及正负号。** 对已有 D_iu=v_i、D_ru=v_r，仍使用同一 χ=φ∘F⁻¹。代码逐个合并有限条 AE 代表等式，证明严格 L² 身份
   `Pχ=φ`，
   `P(D_iχ)=D_iφ−w_iD_rφ`，
   其中 w_i(x)=D_iψ(x)。逆链式先出现 D_iψ(Fx)；由固定法向平移的导数不变性在 t=ψ(x) 处代入，才合法化为 D_iψ(x)，没有对随 x 变化的平移直接求导而漏项。P 的真实内积等距将原弱身份变为
   `⟨Pu,D_iφ⟩−⟨Pu,w_iD_rφ⟩=−⟨Pv_i,φ⟩`。
   已证明的法向链与零法向导数乘积又给
   `⟨Pu,w_iD_rφ⟩=−⟨w_iPv_r,φ⟩`。
   合并后得到真正的 `D_i(Pu)=Pv_i+w_iPv_r`，修正项为加号。全部原 S 测试均覆盖；不使用经典 u 导数、不可数 AE 例外集合并、预设 Piola 身份或变换后梯度。
5. **同一状态的全部 H¹ 字段。** `graphShearPullback` 以 P(value u) 为值，以每个 `P(D_i u)+w_iP(D_r u)` 为梯度分量；前项对所有 i 的真实弱链作为 `firstComponentJet` 的资格。已读取该组装实现：0 阶 scalar fiber 与完整 1 阶 Euclidean fiber 正确对应，所有坐标各出现一次。因此值定理精确识别原 L² 复合，梯度定理精确识别每个原弱分量，而不是构造具有同名字段的无关对象。
6. **完整图收敛及真实测试身份。** `graphShearPullback_tendsto` 保留完整原 H¹ 序列收敛，分别处理 0 阶与 1 阶字段：值经 P 和 scalar fiber 连续映射，全部梯度经原 field/component CLM、P、固定乘子和真实 `firstGradientAssembly` CLM。故其结论是完整 H¹ 图拓扑的序列连续性，足够用于实际闭包极限；不是仅值的 L² 收敛。对任一原光滑测试，P(toLp φ) 与实际 φ∘F 的 toLp 相等；S 的开放性及限制体积的 AE 域内资格使原 `value_injective` 适用，从而恢复两个**完整弱 jet** 相同。该唯一性由所有原弱导数测试给出，没有把任意相同 L² 值的未验证字段直接认作同一 jet。
7. **原 H¹₀ 闭包保持。** `graphShearPullback_dirichlet` 从定义在完整 H¹ 图拓扑中的测试 span 闭包取逼近序列；`exists_test_of_mem_test_span` 将每个成员还原为一个真实紧支光滑测试。由前项，拉回序列逐项正是源域 S 的真实测试 jet，因而属于 S 的原 H¹₀。完整图收敛和闭子空间性质使极限仍属于该 H¹₀。没有输入拉回状态的边界条件、点态零迹、目标域规则性或 H² 资格；本声明给保持方向，没有额外声明一个尚未包装的 H¹₀ 等距同构。
8. **常数、积分资格及范围。** 值范数由 P 精确等距保持；每个实际梯度分量满足
   `‖P(D_i u)+w_iP(D_r u)‖≤(1+C)‖field₁u‖`。
   用 `firstGradientAssembly_norm_sq` 的准确全坐标平方和得
   `‖field₁(pullback u)‖²≤d((1+C)‖field₁u‖)²`。
   因子 d 来自真实 d 个坐标，C 是原 ψ 的全局 Lipschitz 常数，先于全部状态与逼近序列；无目标梯度常数或状态后选界。法向 i=r 时 w_r=0 与公式兼容，d=1 的剪切退化为平移仍成立；具体剪切显式需要 r:Fin d，不虚构 d=0 法向。任意开放空域也允许。所有弱积分是 L² 状态与真实 L² 测试/测试导数的配对，故可积；虽然旧通用换元 helper 使用全定义 Bochner 积分，当前没有借非可积积分的默认值建立空洞弱身份。

最终输入是给定的全空间 C∞、Lipschitz 且沿法向平移不变的 ψ，以及原开放 T 上任意真实 H¹ 状态；只有 H¹₀ 保持声明另要求原 H¹₀ 成员。未要求 u 光滑、H²、有限模式或已有变换后导数。本批尚未从原边界图构造/局部化这样的 ψ，也未传输 H²、原椭圆 PDE 矩阵或完成凸域统一估计；因此 P023 和 18/26 覆盖保持不变。

## 全部声明逐项结论

名称统一带前缀 `Carleman.`；源码行在固定 `GraphShearWeakTransport.lean`，raw 行在固定审计文件完整类型处。

| 源码 / raw 行 | 声明 | 结论 |
|---|---|---|
| 15 / 42646 | `IsWeakSpatialDerivative.graphShear_normal_pullback` | PASS；实际逆测试和真实换元直接传输法向弱链。 |
| 43 / 42657 | `IsWeakSpatialDerivative.mul_of_derivative_zero` | PASS；真实弱乘积及零导数乘子，未预设目标链。 |
| 62 / 42666 | `IsWeakSpatialDerivative.graphShear_pullback` | PASS；所有原测试的完整非线性弱链式，修正项正号正确。 |
| 134 / 42682 | `WeakSobolevJet.graphShearPullback` | PASS；同一 L² 复合和全部实际弱分量装配 H¹。 |
| 146 / 42698 | `WeakSobolevJet.graphShearPullback_value` | PASS；精确原值复合身份。 |
| 154 / 42705 | `WeakSobolevJet.graphShearPullback_gradient` | PASS；每个真实梯度分量与同一斜率乘子的身份。 |
| 165 / 42718 | `WeakSobolevJet.graphShearPullback_tendsto` | PASS；完整 H¹ 图拓扑的序列连续性。 |
| 193 / 42728 | `WeakSobolevJet.graphShearPullback_test` | PASS；原光滑测试的真实拉回与完整弱 jet 相等。 |
| 202 / 42735 | `WeakSobolevJet.graphShearPullback_dirichlet` | PASS；真实 H¹₀ 测试闭包保持。 |
| 215 / 42743 | `WeakSobolevJet.graphShearPullback_value_norm` | PASS；原标量 L² 范数精确等距。 |
| 220 / 42751 | `WeakSobolevJet.graphShearPullback_gradient_bound` | PASS；完整梯度平方和及 d(1+C)² 的真实统一界。 |

## 依赖与固定本地证据

导入闭包 **207 个 Carleman 文件**，其中 **206 个旧文件**相对数学基线逐 Git blob 不变。直接完整读取本批模块、`NonlinearGraphShear`、`WeakDerivative`、`FirstComponentJet`、`FirstGradientAssembly`、`DirichletSpace`，并核对 `SobolevRealization.value_injective`、`SpatialTestOperations` 以及已审且不变的 `WeakProduct` 和限制乘子接口。T237 冻结报告全文读取：提交 `6e96dffd9f2d128ff3d66d6b6d0e163e8cd0b4d6`，reviewed_at=`2026-10-20T07:50:54+00:00`，24/24 PASS；其报告未代替本次对实际剪切、逆、斜率、限制测度和积分调用的直接检查。

mathlib 实际 checkout 无修改，与固定 lock 一致为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。已直接读取 `Lp.compMeasurePreservingₗᵢ`、AE 复合/范数及 `MeasurePreserving.integral_comp'` 实现，确认真实 Lp 和积分传输。Lean 4.35.0，编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`。根导入和 11 项 `#check`/`#print axioms` 齐全。

- `/tmp/carleman-t238-local-evidence.json`：source=local、PASS，checked/source 均为本报告 proof，finished_at=`2026-10-20T07:54:00.483634+00:00`；真实 `lake build Carleman`、`lake env lean tools/CheckAxioms.lean` 执行记录均 exit 0。
- `/tmp/carleman-t238-local-source-manifest.txt`：**1035 项、112327 bytes**，SHA256 `763c7440f87b88488ac26747ebc8222b2b030cb686a8595d48f3400929a9d3f9`。独立枚举固定提交全部 tracked `.lean` 及三个工具链配置，路径集合、唯一性和逐项摘要与固定 Git blob 全部匹配。
- `/tmp/carleman-t238-target-build.log`：**3387 jobs** 成功，112 bytes，SHA256 `841dcb77eaa7a25023da7eebae557c88569af9178d0be4069da05b29e91aeca5`。`/tmp/carleman-t238-build.log`：**4277 jobs** 成功，80 bytes，SHA256 `62ed22808b1b1a6fa0c70449c50d85db6bc905f4826d78cc53e0fe4376f51cd5`。`/tmp/carleman-t238-axioms.log` 为 0 bytes。
- `/tmp/carleman-t238-graph-weak-transport-local-axioms.txt`：**3286046 bytes**，SHA256 `36cf2de54faf0db4bd16dec06182cfe7227440e012b69c308e5b10c7aca0d987`。11 项完整类型逐项核对；全部 **3877 个显式公理记录**仅含正常基础公理 `propext`、`Classical.choice`、`Quot.sound` 或无公理。全命名空间 `privateToUserName`/`collectAxioms` 白名单审计逻辑相对 base 不变，实际末行确认 **9826 声明递归审计 PASS**，无 sorryAx 或额外数学公理。
- 原稿与数学基线相同，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本次核对固定本地执行证据，未重跑全库，未查询远端 CI/看板，也未把本地成功称作 CI。

无修复项。接受本批 **AUXILIARY 非线性弱 H¹ 及 H¹₀ 传输**，保持 18/26。正文与 reviewed_at 冻结后仅单文件提交本报告，不修改数学、台账、原稿、根导入、审计或其他报告，不 push。
