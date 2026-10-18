# T057 / C073 独立本机验收

- `checked_sha`: `fbcd888532fe88caff4907495fad399fe6feeb55`
- `base_commit`: `14bdf0cb11fcc8ac2c51297c2307fb5745ee49b5`
- `semantic_checked_at`: `2026-10-18T20:51:29+00:00`
- `reviewed_at`: `2026-10-18T20:54:05+00:00`
- `result`: **PASS**。
- `axiom_check`: **PASS**。
- 范围：**AUXILIARY**。完整真实 H¹₀ jet 的全空间零延拓、实际全空间弱导数、各字段范数及限制身份。完整 V_h 节点表示及原加权投影仍未完成，不提升完整原文覆盖，完成计数保持 12/26。

本报告直接读取固定提交两模块的实际证明、全部 8 项完整类型、相关依赖及递归公理产物，并对照原 `paper/main.tex` 与 `governance/analysis/T057-dirichlet-zero-extension.md`。执行者说明及旧报告没有替代语义核查；后续工作树增量不参与本次验收。

## 全部 8 项声明

名称均加前缀 `Carleman.`；源码位置相对于固定提交的 `Carleman/Spatial/`。

| # | 声明 | 源码位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `SpatialTest.dirichlet_full_test_pairing` | `DirichletTestPairing.lean:13` | PASS；域内紧支光滑 ψ 与任意全空间测试 φ、任意方向 e 的真实积分分部；ψ 及其实际导数的域外零值给域积分身份。 |
| 2 | `dirichlet_full_test_pairing` | `DirichletTestPairing.lean:51` | PASS；实际 L² 配对在完整 H¹ jet 图拓扑连续，沿全部紧支光滑测试的线性张成闭包传到每个 H¹₀ 状态和每个坐标方向。 |
| 3 | `dirichlet_zeroExtend_weak_derivative` | `DirichletZeroExtension.lean:12` | PASS；结果明确为 volume/univ 上、对全部全空间 SpatialTest 的弱导数，导数恰为原方向弱导数的零延拓。 |
| 4 | `derivativeComponent_zeroExtend` | `DirichletZeroExtension.lean:41` | PASS；任意阶 fiber 的实际分量提取与 L² 零延拓交换，正确处理域内 a.e. 身份和域外零值。 |
| 5 | `WeakSobolevJet.zeroExtendDirichlet` | `DirichletZeroExtension.lean:53` | PASS；实际逐字段延拓 0、1 阶 L² 数据，用全空间弱身份组装完整 H¹ jet。 |
| 6 | `WeakSobolevJet.zeroExtendDirichlet_value` | `DirichletZeroExtension.lean:68` | PASS；空多重指标分量给实际标量值的精确零延拓身份。 |
| 7 | `WeakSobolevJet.zeroExtendDirichlet_field_norm` | `DirichletZeroExtension.lean:73` | PASS；对全部 k∈Fin 2，完整 Euclidean fiber 的 L² 范数准确保持。 |
| 8 | `WeakSobolevJet.zeroExtendDirichlet_restrict` | `DirichletZeroExtension.lean:78` | PASS；对所有字段作 Lp.ext，限制回原域得到原 jet 本身，不仅是 value 相等。 |

## 原文对应与范围

原 `paper/main.tex:1469–1485` 规定 V=H¹₀(Ω)、纯梯度形式及完整 `V_h={v∈H¹₀(Ω):v|K∈P₁}`。本阶段证明该真实 H¹₀ 定义下的零延拓辅助定理，为后续把完整分片仿射 H¹ 状态识别成连续节点状态提供跨边界的弱导数依据。它不构造节点表示，也不删除前阶段投影结论中的显式节点表示前提。

`dirichletJetSpace S` 是全部域内紧支光滑测试函数实际弱 H¹ jet 的线性张成在 H¹ 图拓扑中的闭包；`dirichletSubspace S` 是该空间经 value 的真实 L² 像。没有把零边界点值作为定义或额外假设。已有 `mem_dirichletJetSpace_iff` 和开域上 value 单射使标量 H¹₀ 成员与唯一实际 jet 相对应，本批覆盖这个完整空间，而非光滑或节点状态的子集。

实际完整类型只需 S 开、原真实 H¹₀ jet 成员条件。没有有界性、凸性、光滑边界、网格、连续代表或正维数前提；相对于原有界凸多面体是更一般的辅助结论。无权、无时间、无新估计常数。虽分量交换引理支持任意阶 k，本批只构造 H¹ 零延拓，不声称一般 Hᵐ₀ 的高阶延拓定理。完整 V_h 节点表示、加权投影和其他 P1/连续分析义务仍待，AUXILIARY 范围准确。

## 全部测试函数与实际 H¹ 闭包

已核对 `SpatialTest S` 的定义：真实函数 value、全空间 C∞、紧支集，以及 tsupport(value)⊆S。它容纳全部域内紧支光滑测试，未被收缩为有限、分离变量或特定多项式测试族。全空间 `SpatialTest univ` 的支撑条件没有额外限制，因此第二项配对定理的 φ 可以跨越原域边界，不能被误解为仅域内测试。

`SobolevTopology` 给出的 jet 拓扑是所有真实 L² 导数字段的有限乘积图拓扑，与各字段范数之和等价，不是仅标量 L² 像上的拓扑。value、field 和 derivativeComponent 的连续线性映射均由真实坐标投影/乘子构造。配对等式两侧是这些映射与固定实际 L² 测试或测试导数的内积，因此等式集合闭。`exists_test_of_mem_test_span` 用真实 zeroTest/addTest/smulTest 及其 jet 身份把任意有限线性组合重新实现为一个全族测试，随后 `closure_minimal` 覆盖整个 dirichletJetSpace。没有把近似序列存在、导数收敛或边界配对作为额外前提。

## 原始积分分部与全空间身份

对 ψ∈SpatialTest S 和 φ∈SpatialTest univ，紧支 C∞ 性内部给两者的 Lipschitz 界。已查看固定 mathlib 的 `LipschitzWith.integral_lineDeriv_mul_eq` 实际声明：`∫D_eψ·φ=∫D_{−e}φ·ψ`，此处以真实 volume 和 φ 的紧支性使用。光滑性把 lineDeriv 识别为实际 Fréchet 导数，方向 −e 的线性性提供负号，故目标 `∫ψ D_eφ=−∫D_eψ φ` 的符号和参数次序准确。

ψ 的 tsupport 包含于 S；对 x∉S，ψ(x)=0，且 x 不属于其闭支集，因此 fderiv ψ(x)=0。两个全空间被积函数于是都在 S 外为零，可以准确化成域积分；没有要求 φ 支撑于 S，也没有假设 ∂S 零测。实际 ψ/φ 及其导数的 L² 代表身份来自 MemLp.toLp，内积与积分转换全部按正确的限制测度 a.e. 处理。测试及实际导数字段的 L² 性保证配对可积，未依靠不可积函数默认积分为零。

沿上述闭包传递后的定理对每个坐标方向 i 和每个 φ∈SpatialTest univ 成立。`dirichlet_zeroExtend_weak_derivative` 再把两边使用实际 `integral_mul_zeroExtendLp` 从全空间指示函数延拓积分化到 S，并用测试代表身份回到该配对。最终经 `IsWeakSpatialDerivative.iff_integral` 得到的正是 `IsWeakSpatialDerivative volume univ eᵢ ...`。没有把已知 `volume.restrict S/S` 的弱身份改名为全空间身份；可能的边界分布项消失有真实 H¹₀ 闭包依据。

## 零延拓、分量、范数和限制

`zeroExtendLp` 实际是 S.indicator(u) 的 MemLp.toLp 类，支持一般 NormedAddCommGroup 值；L² 合法性和范数等式来自真实指示函数范数定理。它不是任意命名的等距嵌入。域外为零及域内 a.e. 等于 u 的身份已经在依赖中证明。

`derivativeComponent_zeroExtend` 首先用 `ae_restrict_iff'` 将原域分量 a.e. 身份转成全空间 a.e. 的条件式；在 S 内用该身份，在 S 外用 fiber 的真实零向量分量为零，最后 Lp.ext 给等价类相等。该步骤同时覆盖空多重指标和所有一阶坐标，未遗漏完整梯度的任何分量。

`zeroExtendDirichlet` 的底层字段是 `fun k => zeroExtendLp … (u.val k)`，对 m=1 的唯一导数层 k=0 和空多重指标逐项验证全空间弱身份。value 身份来自 k=0 的分量交换；字段范数定理量化 k∈Fin 2，保留 0 阶 scalar fiber 和 1 阶全部 Euclidean 梯度 fiber 的实际 L² 范数。限制定理使用真实 restrictRegionLp 的 a.e. 代表及零延拓的域内身份，对每个字段证明相等，再用 Subtype.ext 得整个 jet 相等。

d=0 时无坐标方向，弱导数条件相应为空，0 阶字段仍被延拓、限制及保范数；一阶 fiber 为空索引的零空间。证明没有构造不存在的单位向量，也没有除以 d 或假设 Nontrivial。空域、全域和非连通开域均未被额外排除。这里不从一般 H¹ 直接声称零延拓保持弱导数；必要的 H¹₀ 成员条件始终保留。

## 固定声明版本与递归公理

两新模块的 Carleman 导入闭包共 69 个模块，其中 67 个既有模块相对 base 逐字节不变；`Carleman.lean` 明确导入两个新模块。AGENTS、流程规则、原论文、Lean/mathlib pin 和 CI 流程未在该差异中改变。原论文 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

固定 `/tmp/carleman-dirichlet-extension-full.log` 实际包含 `Build completed successfully (3625 jobs).`。固定 `/tmp/carleman-dirichlet-extension-local-axioms.txt` 中 8 项完整类型与源码一致，8 项递归 `#print axioms` 均仅有正常基础公理 `propext`、`Classical.choice`、`Quot.sound`。已核对实际审计程序遍历所有 Carleman（含内部生成）声明，递归 `collectAxioms` 并拒绝白名单外项；末行确认全部 4890 项通过。显式打印的 1332 项不同声明公理集合扫描也没有未许可项，没有 sorry 或未证明数学公理。

本机固定产物为 1,385,779 bytes，SHA256 `22891f3318a83b925787f935e3ccac610b4ee69d20840b8c40452a0981ecdd83`。固定工具链为 Lean 4.35.0，mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`。

## 远端证据及最终结论

已独立读取真实 [main/push run 39165132995](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39165132995/attempts/1)、attempt 1，head SHA 精确匹配本次 checked SHA，顶层 completed/success。三项 jobs 均 completed/success：lean `117786368706`、state-check `117786368913`、dashboard / snapshot `117786956606`。Lean job 的实际构建、记录 checked source、上传两项证据及收尾步骤也全部 success。

已独立核对同次 artifact 元数据：`lean-ci-result` id `12150029136` 和 `lean-declaration-evidence` id `12150228275` 均绑定该 run 与同一 head SHA。实际读取 `/tmp/carleman-dirichlet-extension-main-ci/result.json`：status=PASS，checked_sha/source_head_sha 均为 `fbcd888532fe88caff4907495fad399fe6feeb55`，ci_url 精确对应该 run/attempt，finished_at=`2026-10-18T20:52:03.503291+00:00`，target 为 `Carleman`。Lean 4.35.0（commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）和 mathlib pin 均一致。

实际读取 `/tmp/carleman-dirichlet-extension-main-axioms/axioms.txt` 并与固定本机产物逐字节比较：完全相同，1,385,779 bytes，SHA256 `22891f3318a83b925787f935e3ccac610b4ee69d20840b8c40452a0981ecdd83`。在远端产物再次核对全部 8 项实际完整类型和递归公理集合，均通过，末行确认全部 4890 项审计通过。

最终结论：**T057 / C073 PASS，可以将 C073 升为 REVIEWED，保留 AUXILIARY。** 8 项声明及所声称范围通过，未发现数学缺陷。完整一致 P1 节点表示及原加权投影仍待，不提升完整原文覆盖，完成计数保持 12/26。本 Agent 仅写本验收报告，未修改证明、台账、root 导入或原稿，未 commit/push。
