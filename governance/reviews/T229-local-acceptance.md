# T229 / C245 — 完整 Proposition A.1 独立论文级验收

- checked_sha: `d1dabe5404212ce3dd399028a79233e3da4e324b`
- mathematical_base: `a914d2ede5d27b37e30708efaff64fdf1b783d2d`
- reviewed_at: `2026-10-20T06:38:00+00:00`
- reviewer: 独立验收 Agent `/root/accept_section3`
- verdict: **PAPER PASS — 完整 P022 / Proposition A.1；4/4 显式声明 PASS；T226 的 F1 已清偿。**
- evidence_mode: 固定提交的本机构建、完整递归公理审计、逐文件源码 manifest 与独立数学审查。按现行用户指令，不查询看板，不等待或引用远端 CI。

## 判定与原文范围

直接读取固定版本 `paper/main.tex:333–376` 的 A1–A3、`2615–2654` 的 Proposition A.1 及证明，并核对此前的域、允许权与范数定义。原命题取全部 `V=H₀ᵐ(Ω)`、真实一般系数形式，假设实对称 `W²ᵐ,∞` 系数、形式强制性以及原算子的 `H²ᵐ` 域与图正则估计，结论为所有允许权的 A1–A3。

本次不仅接受两个包装模块：重新核对它们所返回的实际原空间、形式、算子、平方根图以及旧 A2/A3 接口和关键证明。固定最终入口 `Carleman.higherCoefficient_spatial_operators` 现已包含原 A1 第 353 行的完整平方根内容，并与原域、图正则性及完整 A2/A3 指向同一个 `higherCoefficientOriginalForm`。未发现剩余原命题缺项或新增目标估计前提，允许将 C245 与 P022 标记为独立验收通过。

原图正则性仍是 Proposition A.1 自身的假设；本报告不将其解释为一般域椭圆正则性证明。P023、P024、连续 Carleman 估计以及其他论文结果不因本次验收而完成。台账与覆盖计数由主执行者另行更新。

## 全部新增声明

已读以下四项的固定源码、完整展开类型、实际证明及递归公理输出；结构同时逐字段检查。

| 声明（完整名） | 固定源码位置 | 独立核对与结论 |
| --- | --- | --- |
| `Carleman.OriginalForm.formSqrtDomain_eq` | `Carleman/Section3/OriginalSquareRoot.lean:15` | `range(conformingEmbed)=V` 的真实值空间等式，反向由任意原 V 成员的弱 Sobolev jet 给出；没有缩小为光滑核或算子域。PASS。 |
| `Carleman.OriginalForm.SquareRootData` | `Carleman/Section3/OriginalSquareRoot.lean:18` | 算子实际类型为 `V →ₗ[ℝ] L²`；字段分别为非负性、全伴随图、双向平方组合图、全 V 能量恒等式。字段量化所有环境空间的图变量及所有原 V 测试。PASS。 |
| `Carleman.OriginalForm.exists_squareRootData` | `Carleman/Section3/OriginalSquareRoot.lean:28` | 内部构造真实平方根并传输全部四个字段；没有将平方根或目标性质作为输入。PASS。 |
| `Carleman.higherCoefficient_spatial_operators` | `Carleman/Spatial/HigherSpatialOperators.lean:17` | 对同一实际系数原形式返回平方根数据、完整原域等式、稠密性、闭图、非负/自伴图、图界和统一全允许权 A2/A3。PASS。 |

原始审计中的四项完整类型分别从第 41646、41651、41660、41665 行开始；四项均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。

## F1 的实质核对

T226 冻结报告拒绝将 P022 视为完整，原因是当时没有证明同一原 H 上 `D(A^(1/2))=V`、完整组合域上的 `A^(1/2)²=A` 和全 V 能量身份。本批确实清偿这一缺口。

1. T228 的 `formSqrtDomain` 是实际嵌入的值域。新 `formSqrtDomain_eq` 用真实弱 jet 的存在性证明它恰好是 `OriginalForm.V`。`OriginalForm.dense` 保证其在同一 `L²` 中稠密。
2. `exists_squareRootData` 使用相等子空间之间的两个 `Submodule.inclusion`。它们不改变任何 H 值，互逆由子类型值及证明无关性给出。新 `Ahalf=S.comp f` 是实际线性算子。
3. `adjoint_graph` 的左边对全部原 V 成员作内积测试，右边给出该原 V 中的真实图成员；两个方向都经 inclusion 转移。因此是完整无界自伴图，不仅是对称性或一个域上的单向配对。
4. `square_graph` 对全部 `x,f∈H` 作双向等价，左边显式要求 `v∈V`、`u∈V`、`u=Ahalf v`、`Ahalf u=f`，右边正是同一原 `model.operator` 的完整图。中间成员条件给出真正平方组合域，没有把该条件省略或只在原 D(A) 上证明等式。
5. 全 V 能量身份利用 `valueEquiv.surjective` 和 `scalarForm_value` 回到同一原形式。没有把 `sqrt(a(v,v))` 命名为算子，也没有把能量形式换成新定义。

重新读取了关键底层构造：`inverseH` 是原 coercive form 的实际逆算子；T227 的实 Hilbert 正根给出 `B²=inverseH`；T228 的 `inverseSqrtLift` 由稠密延拓和原形式配对构造。其下界给闭值域，原能量空间中的稠密性给满射，进而证明 `range B=range embed`。根算子作为 B 的实际逆，获得完整自伴图与双向平方图。这里没有有限维、谱截断、复 Hilbert、原状态光滑性或额外正则性假设。正自伴平方根及其完整域和能量身份足以实现原 A1 的平方根表述。

## 原 A1–A3 逐项映射

| 原要求 | 实际对象、证明与量词检查 | 结论 |
| --- | --- | --- |
| 全部 `H₀ᵐ` 与闭合稠密形式空间 | `HigherDirichletSpace` 是全部 `SpatialTest` 的真实 Hᵐ jet 闭包；值单射识别真实 L² 类。`ConformingHilbert` 的嵌入值域正是原 V，完整 Hilbert 范数而非任意等价范数。 | PASS |
| 全实对称 `W²ᵐ,∞` 系数及实际积分形式 | `MultiDerivativeIndex` 包括所有阶数 ≤m 的多重指标，保留低阶和非对角项；`BoundedWeakCoefficient` 的各有序弱导数由实际测试配对连接，混合导数识别由弱唯一性证明。`CoefficientJetForm`/`HigherCoefficientForm` 给出原有限积分和，AE 对称性足够，未要求光滑系数或跨边界延拓。 | PASS |
| A1 的有界性、强制性及原 associated A | 真实有限系数 L∞ 乘法给形式有界性，强制性是原命题的显式假设。`OriginalForm.associated_iff` 是对全 V 的原变分关系，`CoerciveForm` 内部供应稠密域、闭图、非负性和完整自伴图。 | PASS |
| 原 `D(A)=H²ᵐ∩H₀ᵐ` 及图正则性 | 输入 `hD` 仅要求原 associated domain 包含于 H²ᵐ，比原已假设的域等式弱；`CoefficientDifferentialOperator` 通过真实弱分部积分和全测试闭包证明反向包含及实际微分表达式。输入 `hgraph` 是完整 `SobolevHilbert.ofJet` 的 H²ᵐ 范数图界；输出的旧 jet 范数界只是其推论，完整原界仍由显式原假设保留。 | PASS |
| A1 平方根域、算子平方及能量 | 上述新 `SquareRootData` 在同一 V/A/a 上给出完整四字段，F1 清偿。 | PASS |
| A2 正权/逆权保持 V 与 D(A) | 真实弱乘法法则、全 H₀ᵐ 闭包稳定性及域等式供应保持性；`AllowedFamily.inverse` 使用反号与 `-τ`，并保留 τ 的绝对值范围。不是假设权后状态已经在域内。 | PASS |
| A2 实际交换子及严格低阶幂 | `CoefficientDifferentialOperator` 识别实际 A；`CoefficientCommutator` 中以 `σ·σ⁻¹=1` 消去最高阶项，得实际 `[A,σ]σ⁻¹v`。求和指标 `Fin (2*m)` 恰为 `j=0,…,2m−1`，因子为 `q^(2*m−j)`，右端是原 canonical 弱导数字段 L² 范数。 | PASS |
| A3 双权上界 | 同一真实积分形式逐项 Cauchy–Schwarz；实际逆权恒等式与各阶加权弱导数给 `Nσ(v)Nσ⁻¹(w)`，两变量均为全部 V。 | PASS |
| A3 `σ²v` 下界 | 同一实际 `w=σv` 的原形式强制性，加上严格低阶共轭余项和可选小参数 Sobolev 插值吸收，得到 `cNσ(v)²−C‖q^mσv‖₂²`。平方测试的 V 资格内部供应，没有把此目标下界作为前提。 | PASS |

`SmoothOnClosure` 要求真实闭包连续代表及全部阶数的内部导数连续延伸，覆盖原固定闭包光滑空间权；其邻域光滑构造已存在。`IsBoundedLipschitzDomain` 给实际开、有界、局部 Lipschitz 图，不增加边界光滑性或椭圆正则假设。最终 d、m 为任意自然数，尤其覆盖原 d,m≥1；省略原连通性、权的负性或时间导数预算，仅扩大本空间命题的适用范围。

最终量词顺序为先固定域、系数、原强制性/图假设与空间函数 r，再内部选择 `ρ.value=r` 和正 `c,C,Ccomm`，随后才 `∀ TimeWeight w, ∀ τStar`；`AllowedFamily` 内部再量化全部时刻、双符号、允许 τ 及全部状态。故原任意 T、固定有限 τ* 和原 q 类均被覆盖，常数不依赖 T、q 的大小、时刻或状态。空间微分不作用于标量 `q^τ`，因此常数在 τStar 之前并不漏项。原 N 范数使用 canonical 弱导数字段；系数常数通过有限系数/弱导数界和原形式强制常数进入，没有网格、有限维或额外目标估计。

## 依赖版本与独立审查

已读取以下冻结报告的全文，并核对实际依赖版本。报告不是本次数学判断的替代物。

| 冻结报告 | proof / 报告 commit | 本次复用边界 |
| --- | --- | --- |
| T226 | proof `4728609fbece53cc6afcc9013b94592eb23ee87d`；报告 `63c553825231ccf22f1efb72dc2f10ed4e666fde` | 明确保留旧 F1 发现，重审新补项；`HigherAnalyticData` 的 304 模块闭包逐 blob 与该 proof 相同。 |
| T227 | proof `4573638d5529914e0140c25f4dfe3689be92afaa`；报告 `cf3b8b7e99df3b1548a86f172f01f6a4ca154fac` | `RealOperatorSquareRoot` 的单模块 Carleman 闭包不变，复用已独立证明的实 Hilbert 正根；核对其实际调用与类型。 |
| T228 | proof `a914d2ede5d27b37e30708efaff64fdf1b783d2d`；报告 `794655ea939bd5d711faa65a3c3cd50d74621e89` | `FormSquareRoot` 的 8 模块闭包逐 blob 不变；本次重新阅读全文 `FormInverse`、`FormSquareRootLift`、`FormSquareRoot`，检查实际域/配对/满射/平方图。 |

两新入口合并 Carleman 导入闭包共 310 模块，其中 308 个既有模块与数学基线逐 blob 相同。直接重读的旧关键实现还包括 `OriginalForm`、`HigherAnalyticData`、`HigherAllowedData`、`AllowedFamily`、`AllowedWeightData`、`HigherCoefficientForm`、`WeakCoefficientJet`、`HigherDirichletSpace`、`CoefficientJetForm`、`CoefficientCommutator`、`HigherWeightedCoercivity`、`CoefficientDifferentialOperator`；并检查插值、真实加权范数、局部 Lipschitz 图与闭包光滑接口。未把未来工作树的 T230 等增量计入审查。

## 固定本机构建与公理证据

- 原始结果：`/tmp/carleman-t229-local-evidence.json`，`status=PASS`、`source=local`、`checked_sha=source_head_sha=d1dabe5404212ce3dd399028a79233e3da4e324b`，完成于 `2026-10-20T06:26:56.944598+00:00`；`lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 均 exit 0。
- 固定源码 manifest：`/tmp/carleman-t229-local-source-manifest.txt`，1026 个唯一条目，111304 bytes，SHA256 `0e5f9415da91599f3ce561c7ebfe577bf59ab1986860699e4133748c399c5aa2`。独立核对全部条目的原始字节哈希及完整路径集合，与固定 Git 的全部 `.lean` 文件和三个构建配置逐项一致。
- 定向日志：`/tmp/carleman-t229-target-build.log`，3517 jobs 成功；177 bytes，SHA256 `72b96b65a7ac31def9b11dc9f57c4483f6028847270483f4013798c267e5f5e8`。
- 全库日志：`/tmp/carleman-t229-build.log`，4263 jobs 成功；81 bytes，SHA256 `56a26b01b63e1b21fdf8878b252138a8f4766cae43bb10b66960fc8894c48ca2`。
- 原始完整类型/公理输出：`/tmp/carleman-t229-spatial-operators-local-axioms.txt`，3201422 bytes，SHA256 `084f506edea932843ddbddb454414167628f93307086e141e340e614f2f77a2a`；末行实际为 `Axiom audit passed for all 9534 Carleman declarations.`。空的 `axioms.log` 仅是 stderr，不作为通过证据。
- 固定审计程序对环境中全部 Carleman 声明运行递归 `collectAxioms`，白名单严格为上述三个基础公理。四项新声明均有 `#check @` 和 `#print axioms`；新文件没有 `sorry`、`admit`、新公理或 `native_decide`。独立解析显式公理输出也未发现白名单外依赖。
- Lean `4.35.0`，编译器 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；固定 mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679` 与 `lakefile.toml`、`lake-manifest.json` 和实际干净的 mathlib checkout 一致。
- 固定原稿 SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`；原稿未因本批实现改写。

最终发现：**无待修复缺陷；原 Proposition A.1 完整通过。** 本报告只对上述固定证明版本签发；签发后正文和 `reviewed_at` 冻结。
