# T067 / C083 独立本机验收

- checked_sha: `604328efce1cc28e4d6fe6cadcdaa039ee0e76a3`
- base_commit: `1f04be4f79db9d40ac1af37271eb8e9dc58639a3`
- reviewer: 独立本机数学验收 Agent `/root/accept_spatial_lemma`
- result: `PASS`（固定版本 15 项可升 REVIEWED；仅本报告所列 AUXILIARY 范围）
- axiom_check: `PASS`
- reviewed_at: `2026-10-18T22:05:02+00:00`
- scope: `AUXILIARY`。仅清偿 m=1、V=H¹₀ 的允许权保持性及真实平方权残差 H¹₀ 资格；不宣称算子域保持、交换子、一般 m 或完整 A2。原文仍 **12/26**。

## 固定范围与全部声明

依项目 `AGENTS.md`、`governance/PROJECT_OPERATIONS.md`、`state/README.md` 与数学规格，使用 `git show` 读取固定提交四模块全部源码、实际展开类型及调用依赖，对照原 `paper/main.tex` 的 A2、Appendix A 和 Section 6 Step 3。没有用执行者说明或构建成功代替数学核查；后续工作区文件不在范围。

15 项精确匹配固定 C083/T067 及 `/tmp/carleman-dirichlet-weights-declarations.json`。四模块在 `Carleman/` 下，root 均已显式导入。每项实际数学类型、本机及同 SHA 远端递归公理均通过：

| 完整声明 | 固定位置及实际结论核对 |
| --- | --- |
| `Carleman.firstDerivativeInjection` | `Spatial/FirstGradientAssembly:14`；将实数通过真实 CLM 注入 `DerivativeFiber d 1` 的指定 Sym 坐标。 |
| `Carleman.firstDerivativeInjection_component` | 同文件；真实 L² 坐标提取为 i=j 时 u，否则零类；使用 a.e. 零代表处理不同坐标。 |
| `Carleman.firstGradientAssembly` | 同文件；有限和装配 `Fin d → Lp ℝ 2 ν` 到原 Euclidean 一阶字段的真实连续线性映射。 |
| `Carleman.firstGradientAssembly_component` | 同文件；装配后每个 `Sym.cons i nil` 分量恰等于输入 v_i，无漏项或重复系数。 |
| `Carleman.firstProductFields` | `Spatial/FirstWeakProduct`；零阶为 w·value(u)，一阶为 w·field₁(u)+装配(dw_i·value(u))；这是明确字段构造，本身没有被当作弱导数结论。 |
| `Carleman.weakFirstProduct` | 同文件；开域、测度集中于域、w 域内光滑以及 dw_i a.e. 等于真实 fderiv 方向分量，实际推出上述字段满足完整弱 H¹ 身份。 |
| `Carleman.weakFirstProduct_value` | 同文件；新 jet 的标量值精确等于真实乘子 map，不是只范数等价。 |
| `Carleman.weakFirstProductCLM` | 同文件；在真实 H¹ 有限 L² 字段图范数上为连续线性算子；附加的局部有限测度实例用于真实弱导数唯一性。 |
| `Carleman.clm_mem_closed_span` | `Spatial/DirichletWeakProduct`；任意 CLM 在生成元上进入原 span，即保持该 span 的拓扑闭包；不需要像闭或错误的闭包等式。 |
| `Carleman.weakFirstProductCLM_test` | 同文件；任意完整 SpatialTest 的乘积 jet 等于真正 `φ.mulOn` 的 jet，经真实值相同与弱唯一性识别全部字段。 |
| `Carleman.weakFirstProductCLM_mem_dirichlet` | 同文件；将上一测试身份和 CLM 闭包保持应用于原 dirichletJetSpace，覆盖全部 H¹₀ jet。 |
| `Carleman.boundedSmooth_map_mem_dirichlet` | 同文件；从 BoundedSmoothOn 内部选择实际有界 wordDerivative 一阶乘子，对任意原 H¹₀ 标量类证明 w.map 保持性。 |
| `Carleman.allowed_multiplier_boundedSmooth` | `Weights/DirichletAllowedWeight`；原 SmoothOnClosure 及有界开域内部供应每个真实 q^τ exp(ηqρ) 的 BoundedSmoothOn，任意 TimeWeight、τ、t 及 |η|=1。 |
| `Carleman.allowed_weight_mem_dirichlet` | 同文件；全部原 H¹₀ 标量状态的实际允许权 map 仍在 H¹₀；没有节点、网格或额外状态正规性前提。 |
| `Carleman.allowed_squared_residual_mem_dirichlet` | 同文件；u、I∈H¹₀，任意真实 H¹ jet e 的值为 σ²u−I，则 e∈原 dirichletJetSpace。两次保持性和弱导数唯一性清偿资格。 |

## 真实字段与完整弱乘积

已直接检查 `DerivativeFiber d 1=EuclideanSpace ℝ (Sym (Fin d) 1)`、`derivativeComponent` 及 `scalarZeroFiber` 的定义。`Sym.oneEquiv` 将 Fin d 与全部一阶多重指标一一对应。注入使用 PiLp 的真实连续线性等价、坐标 pi 映射和标准标量 id/zero；装配对全部 i 作有限 CLM 和，再证明任意坐标提取准确。i≠j 分支没有假定 Lp 零类的选定代表处处为零，而是显式使用 `Lp.coeFn_zero` 的 a.e. 身份。d=0 时有限空和、空一阶字段均合法，不引入单点零测假设。

`firstProductFields` 的两个字段都是实际 L² 类：有界乘子保持 L²，有限 CLM 装配保持 L²。`weakFirstProduct` 对所有弱身份的 k、α、i 展开：m=1 强制 k=0、α=nil，再将新零阶坐标化为 w.map(value u)，将一阶坐标化为 w.map(∂ᵢu)+dw_i.map(value u)。它真正调用原 `IsWeakSpatialDerivative.mul`，而不是把目标梯度当作未经约束的字段输入。

该依赖已逐行核对：对任意原 `φ : SpatialTest S`，将原弱身份应用于真实 φ·w；其导数由真实 fderiv 乘积法则、hdw 的 a.e. 等式及测度集中于 S 得到。用真实 L² 配对中有界实乘子的对称性移项，得到正确负号的完整分布乘积公式。测试族是所有光滑紧支于 S 的函数，没有限制到有限元子空间或一小组测试。

一般弱乘积引理显式要求实际导数联系 hdw，而后续 `boundedSmooth_map_mem_dirichlet` 内部清偿它。因而通用接口允许输入 dw 不意味着最终结论保留任意梯度或未经证明的导数假设。

## H¹ 图拓扑、测试乘积和闭包

已直接读取 `SobolevTopology`：WeakSobolevJet 是有限 L² 导数字段积的闭子空间，范数为该积的图范数；其完整性与原所有弱测试身份的闭性相容，且该范数和所有字段 L² 范数之和等价。`weakFirstProductCLM` 的连续性逐字段证明：零阶由真实 valueCLM、w 的 L² CLM 和 scalarZeroFiber 复合；一阶是 w 的字段作用与各 dw_i 标量作用经有限装配之和。使用 induced 子空间拓扑和 continuous_pi，未将 H¹ 拓扑偷换成标量 L² 拓扑。加法/数乘通过真实值身份及弱导数唯一性提升为整个 jet 相等。

`SpatialTest.mulOn` 只需 w 在开 S 内 C∞。x∈S 时由开域邻域得到真实局部光滑乘积；x∉S 时，x 不属于 φ 的闭支撑，故 φ 在 x 邻域恒零，wφ 也恒零，即使 w 在域外没有连续性仍全空间光滑。乘积的闭支撑包含 φ 的闭支撑，紧性和紧含于 S 均实际保留。没有假设 w 本身紧支或有全空间光滑延拓。

`weakFirstProductCLM_test` 先证明标量 L² 值相同，再以原开域上全部弱测试所给的唯一性识别整个 jet；没有只匹配零阶而忽略梯度。唯一性依赖 `spatial_eq_zero_of_tests` 的完整紧支光滑测试分离 L² 类，已核对其有限维、局部有限测度及 a.e. 集中于域的前提；对 volume.restrict S 均由实际实例和 `ae_restrict_mem` 供应。

`clm_mem_closed_span` 使用连续像的正确包含关系 `P(closure span A)⊆closure(P(span A))`，再用生成元假设和线性性得 `P(span A)⊆span A`。固定 mathlib 的 `Submodule.topologicalClosure_map` 确实是此方向的包含，无闭像要求。实例的 A 正是全部 SpatialTest 的真实 sobolevJet 集；原 `dirichletJetSpace` 定义就是其 span 的 H¹ 图拓扑闭包。由此证明的是项目原 H¹₀，未引入未证明的点态零边界或迹刻画。

## 内在导数、原允许族与常数依赖

已直接读取 `IntrinsicMultipliers`、`IntrinsicSmoothClosure`、`IntrinsicDerivatives`。BoundedSmoothOn 的定义是域内真实 C∞，以及每个有限阶段的全部实际 iteratedFDeriv 一致有界。`intrinsicWordMultiplier [i]` 的值是实际 `wordDerivative [i] w.value`，可测性来自开域内光滑及测度集中；有界性来自真实坐标张量范数比较和有限阶导数界。`intrinsicWordMultiplier_derivative [] i` 在域内以开邻域将该 wordDerivative 识别为真实 fderiv 方向分量。因此最终 hw 不只是命名为“光滑”的抽象界，也没有额外指定一个导数族。

SmoothOnClosure 明确要求 profile 在 closure S 上连续、在 S 内 C∞、各阶域内实际 Fréchet 导数有连续闭域延拓。它不要求对任意域外代表在边界求导；已核对其 congr 性质及由常见邻域光滑假设得到它的定理。有限维有界域闭包紧，连续导数延拓逐阶取界，再合成有限阶公共界，实际供应 BoundedSmoothOn。这个条件对应原 `paper/main.tex:291` 固定的 ρ∈C∞(closure Ω)，不把此前仅 C² 的辅助接口悄悄强化后宣称同一接口已完成。

真实 multiplier 的值是 q(t)^τ exp(ηρ(x)q(t))；`allowed_multiplier_boundedSmooth` 与依赖使用的 q(t)^τ exp(q(t)(ηρ(x))) 仅作实数乘法交换。TimeWeight.lower 给 q≥1，正值保证任意实幂合法；|η|=1 精确覆盖两种符号。τ、t 任意，故包含论文 |τ|≤τ*、t∈[0,T] 的全部原允许族。倒数由 τ、η 同时取负得到，因此原 σ⁻¹ 也被覆盖；不需要另选空间 profile 或增加权的数值条件。

这里对固定权的乘子/导数界及 H¹ CLM 范数可以依赖 q、τ 和时刻，因为结论是固定权的空间成员资格，没有声明一个独立于这些参数的算子范数界。定理对全部 TimeWeight、时间、τ、符号及全部状态成立；没有网格、h、qmax 小量条件、T 上下界或节点假设，也未把辅助的所有实 τ 保持性用作扩大其他数值估计的允许族。原有界 Lipschitz 域满足此处所需的有界开域条件；此阶段不额外要求凸性或非空。

## 平方权残差及原文边界

`allowed_squared_residual_mem_dirichlet` 对任意 u、I 的真实 L² 类要求它们属于原 H¹₀。先两次实际应用 σ 保持性，得到 σ.map(σ.map u)∈H¹₀；用 `BoundedMultiplier.mul_map` 识别为 (σ.mul σ).map u，再由子空间减法得到 σ²u−I∈H¹₀。这里没有将 σ² 误认为仍必须满足 |η|=1 的单次权，而是合法地连续使用同一原 σ 两次。

给定 e 是任意已经满足全部弱身份的真实 H¹ jet，且 value(e)=σ²u−I。`mem_dirichletJetSpace_iff` 的逆向用弱导数唯一性将 e 与原 H¹₀ 标量像中的见证 jet 识别，故结论确实是 e∈原闭包。没有从值恒等式为一组任意梯度赋予 H¹₀ 资格，也没有预设 e 的节点来源、紧支代表或更高正则性。

原 Section 6 Step 3（1569–1593 行）的节点 I 已由先前阶段证明在完整 V_h⊆H¹₀，T064–T066 的 e 已是真实 H¹ jet 且具有所需值身份。本定理因此能清偿这些实际残差的 H¹₀ 资格；其调用所需原 SmoothOnClosure 明示保留。已读取 [T066 验收](T066-local-acceptance.md)，固定 checked SHA 正是本阶段基线；本阶段没有改写该接口或旧误差常数，也不声称将新结论接入所有后续封装已自动完成。

原 A2（354–360 行）同时要求 V 和 D(A) 保持及交换子估计；Appendix A（2615–2667 行）还涉及一般 m、域识别和椭圆正则。本批仅完成 m=1、V=H¹₀ 的权及逆权保持，另补 Step 3 残差资格。算子域保持、一般 H² 乘积/插值、椭圆正则、交换子或完整 A2 均不由这 15 项推出，原文完成数保持 12/26。

## 固定依赖和构建证据

四模块的项目 import 闭包共 51 模块，其中 47 个既有模块与基线逐字节一致。已直接核查本批实际调用的 ComponentNorms、FirstOrderSobolevJet、SobolevJet、SobolevRealization、SobolevTopology、WeakDerivative/Unique/Product、SpatialTestSobolev、DirichletSpace、MultiplierContinuity、IntrinsicMultipliers、IntrinsicSmoothClosure、IntrinsicDerivatives、AllowedWeight 和 SpatialComparison 等关键定义及证明。未以旧报告替代当前调用前提核对。

原稿 SHA256 仍为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean pin 为 `leanprover/lean4:v4.35.0`，mathlib pin 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，本机实际 mathlib HEAD 相同且工作树干净。CI workflow、工具链及检查脚本未改；CheckAxioms 仅增加本批 15 项 `#check @...` 和 `#print axioms ...`，原全 namespace 递归检查逻辑保留。

已读取固定本机 `/tmp/carleman-dirichlet-weights-full.log`，实际包含 `Build completed successfully (3665 jobs).` 及全部 **5062** 个 Carleman 声明递归审计 PASS。固定 `/tmp/carleman-dirichlet-weights-local-axioms.txt` 实测 **1,492,616 bytes**，SHA256 **`ef7d2ea661d6f533854d4885f3e62cca430e92eabe4d41c3c7a4aa90ff4aac46`**。15 项完整展开类型逐名核对，每项仅有 `propext`、`Classical.choice`、`Quot.sound` 三项正常基础公理。检查器以 privateToUserName 识别项目 namespace 并对全部声明递归 collectAxioms，覆盖定义生成的辅助声明，未只检查 15 个显式入口。

已独立读取 GitHub 实际 run、jobs 和 artifacts API：[main/push CI 39170347012 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39170347012/attempts/1) 为 completed/success，head SHA 精确等于本次 checked_sha。三项 job 均为相同 SHA 且 completed/success：state-check（117801901799，2026-10-18T22:01:01Z）、lean（117801902046，22:04:14Z）、dashboard / snapshot（117802655965，22:04:26Z）。同次原始证据 artifact `lean-ci-result`（12151854262）与 `lean-declaration-evidence`（12152182989）均绑定相同 run/SHA 且未过期。

已直接读取 `/tmp/carleman-dirichlet-weights-main-ci/result.json`：status PASS，checked_sha 与 source_head_sha 均为 `604328efce1cc28e4d6fe6cadcdaa039ee0e76a3`，ci_url 精确对应上述 attempt，finished_at 为 `2026-10-18T22:03:17.578304+00:00`，targets 为 Carleman；实际 Lean 4.35.0（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）和 mathlib pin 均匹配。结果生成时间与各 job 完成时间分开记录，没有用较早生成的 result 推断尚未结束的 job 已通过。

已读取 `/tmp/carleman-dirichlet-weights-main-axioms/axioms.txt`，与固定本机副本逐字节比较完全一致：**1,492,616 bytes**、SHA256 **`ef7d2ea661d6f533854d4885f3e62cca430e92eabe4d41c3c7a4aa90ff4aac46`**。远端逐名复核本批 15 项，并检查全部 1442 条显式公理输出，均仅使用上述标准基础公理；末行实际为全部 **5062** 声明递归审计 PASS。未使用后续工作树 `.ci/axioms.txt` 替代本次产物。

## 验收决定

**C083：PASS，可升 REVIEWED，scope 保持 AUXILIARY。** 固定版本全部 15 项的实际类型、数学证明、原假设、完整测试/状态空间、真实 H¹ 拓扑、a.e. 身份、依赖公理与同 SHA 正式 CI 均已独立核实，未发现需要修复的数学缺陷。

本批确实清偿原 m=1 能量空间 H¹₀ 的允许权及逆权保持性，并使具有准确值身份的真实平方权残差进入原 H¹₀ 闭包。没有清偿 D(A) 保持、交换子、一般 m 或整个 A2，也不提升完整原文命题；原文仍 12/26。本次仅写本报告，未修改证明、台账、原稿或 root 导入，未 commit/push。
