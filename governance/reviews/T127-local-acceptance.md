# T127 / C143 独立本机验收

- `checked_sha`: `b7491fa1b22b01515e8d0c428f35a3dbe301c34f`
- `base_commit`: `8bfc0cb3d9a3d394805cfbb9720d903fc139bdfe`
- `reviewed_at`: `2026-10-19T06:33:16+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：实际有界测试泛函的同常数 Hilbert 代表，原全部紧支光滑测试的 L² 弱导数判据，以及逐测试极限下有界弱导数的存在性。尚不完成原凸域 Dirichlet H² 正则性或 `prop:analytic-realizations`，P023 不提升，原文保持 **14/26**。

本 Agent 直接读取固定 Git 对象的三模块全部证明、五项完整展开类型、实际关键依赖、治理协议、T127 分析、MATH_SPEC 和 C143/T127 条目，并对照原稿及本地 Grisvard 相关页面。执行者说明、历史验收标签和 CI 均未替代数学审查。后续未提交正则性代码、工作树增量及变化中的 `.ci/axioms.txt` 不属于本次版本。

## 全部五项声明

名称省略 `Carleman.`；源位置以 `Carleman/Spatial/` 为根。清单顺序与固定 C143、T127 和交付 JSON 完全一致。类型行号来自独立下载并与固定本机副本逐字节相同的原始 axioms.txt。

| # | 声明 | 固定源位置 / 完整类型行 | 独立结论 |
|---|---|---|---|
| 1 | `exists_inner_of_bounded_test_functional` | `BoundedTestRepresentation.lean:12` / 27104 | PASS；任意实 Hilbert 空间、实际线性单射 J 和泛函 L，经 range J 上的 Hahn–Banach 延拓及 Riesz 表示得到范数≤同一 C 的代表。 |
| 2 | `exists_weakSpatialDerivative_of_test_bound` | `WeakDerivativeBoundedTest.lean:16` / 27110 | PASS；从原全部紧支光滑测试上的 L² 测试范数界，构造真实原域 L² 坐标弱导数，保持常数 C。 |
| 3 | `exists_weakSpatialDerivative_iff_test_bound` | `WeakDerivativeBoundedTest.lean:48` / 27122 | PASS；反向使用实际弱身份和 Cauchy–Schwarz，与第2项构成同一 C 的精确 iff。 |
| 4 | `exists_weakSpatialDerivative_of_test_limits` | `WeakDerivativeBoundedLimit.lean:14` / 27134 | PASS；逐测试配对收敛、逐测试最终弱身份和候选导数最终统一范数界，足以构造极限状态的真实弱导数。 |
| 5 | `exists_weakSpatialDerivative_of_strong_limit_bounded` | `WeakDerivativeBoundedLimit.lean:33` / 27159 | PASS；原 L² 强收敛通过内积连续性供应第4项的配对收敛，无候选导数收敛假设。 |

## 原文定位与本阶段边界

原 `paper/main.tex:2659–2664` 的 `prop:analytic-realizations` 要求固定有界凸多面体或盒上的 Dirichlet Laplacian 满足原空间分析假设，证明引用 Grisvard 的 Theorem 3.2.1.2 来供应 D(A)=H²(Ω)∩H¹₀(Ω) 及椭圆正则估计。该完整结论还需要解、Hessian 先验界、域正则性和算子域识别，不能从本批五个泛函与极限引理直接推出。

已实际核对本地 [Grisvard 1985 原书](</Users/wangyu/Documents/math/article/Grisvard1985-Elliptic Problems in Nonsmooth Domains.pdf>)：文件为22,737,765 bytes、422页；视觉读取 PDF 第159–161页，即印刷147–149页。第147页给出凸域光滑内外逼近引理和 Dirichlet H² 定理；第148页使用光滑内域解、统一 H² 界及零延拓字段的有界性；第149页用每个紧支测试最终包含于内域的身份，识别极限二阶分布导数为 L² 函数。

本批选择等价的有界泛函表示路线，免去预先选择候选导数的弱收敛子列：先从原测试配对的极限得到有界分布泛函，再由 Hahn–Banach/Riesz 构造 L² 代表。这是上述极限识别步骤的基础工具。第2–5项实际证明的是一个给定坐标 i 的一阶弱导数；后续必须对真实一阶字段逐坐标应用并组装二阶 jet，不能把本批直接称为完整 Hessian 或 H² 正则定理。原稿的引用键为 Grisvard2011；本次直接核对的是提供的1985版本及相同定理编号，没有修改原文或文献元数据。

实际光滑内域上的 Dirichlet 解、统一 Hessian/Miranda–Talenti 估计、域穷竭、原解及原算子域的识别均未在本批内部供应。本报告不将这些后续前提或完整原 Corollary A.2 宣称完成，C143 仅为 AUXILIARY。

## Hilbert 表示保留常数且没有隐藏完备性

第1项的 V 只有实向量空间结构；H 是实际完备实内积空间。J:V→H 为线性单射，L:V→ℝ 为真实线性泛函，输入 C≥0 及对所有 x 的 |Lx|≤C‖Jx‖。证明以 `LinearEquiv.ofInjective` 将 V 与真实线性子空间 range J 识别，定义 l=L∘e⁻¹；子空间范数就是 H 中的范数，因此界严格仍为 C，没有依赖 J 逆的另一个算子范数。

`l.mkContinuous C hb` 给真实连续泛函 f。已读取固定 mathlib 的 `exists_extension_norm_eq`：它延拓到整个 H 的 g，且 ‖g‖=‖f‖，不要求 range J 闭或完备，也不要求 range J 稠密。再使用 `InnerProductSpace.toDual` 的实际线性等距等价得到 v；其逆映射范数保持，故 ‖v‖=‖g‖=‖f‖≤C。`toDual_symm_apply` 和延拓在 e x 上的身份给 ⟨v,Jx⟩=Lx，内积方向和符号正确。

V 不需要拓扑、范数或完备性；J 不需要另给连续性；仅 H 的完备性用于 Riesz。C=0、平凡测试空间或平凡 H 都包含，未除以 C。代表不在任意预设的候选类中，而由真实全空间连续泛函构造。这里使用正常 Classical.choice，不是新增的表示公理。

## 全部真实测试、实际弱导数与精确 iff

已直接展开 `SpatialTest`、`IsWeakSpatialDerivative`、`SpatialTestSobolev`、`SpatialTestOperations`、`SobolevRealization` 和 `WeakDerivativeUnique`。SpatialTest 的输入为任意全空间 C∞ 标量函数、紧支和 tsupport⊆S；测试 L² 类与方向导数 L² 类分别来自该函数及实际 Fréchet 导数的 MemLp.toLp。紧支保证真实可积性，全部内积也由 L² Cauchy–Schwarz 保证，未使用形式占位或不可积积分的默认值。

`IsWeakSpatialDerivative` 明确量化所有这样的测试，并要求

\[
\langle u,\partial_i\varphi\rangle_{L^2(S)}
=-\langle v,\varphi\rangle_{L^2(S)}.
\]

已有 `iff_integral` 用真实 toLp 的 a.e. 身份将它识别为原 Lebesgue 分部积分式。v 和 u 都属于同一 `Lp ℝ 2 (volume.restrict S)`；没有混用全空间范数或把原域测试换成有限测试集。

第2项令 P 为全部实际测试 Sobolev jet 的线性 span，J 为其原值映射。`WeakSobolevJet.value_injective` 的来源是开域上全部光滑紧支测试所确定的真实弱导数唯一性；限制测度满足 a.e. 落在 S，因此它的全部条件在此清偿。其证明先由真实分布基本引理确定零类，再对相邻阶弱身份归纳，不依赖本批新表示定理，因而没有循环。

`exists_test_of_mem_test_span` 逐项处理零、加法和实数倍：这些运算保持全空间 C∞、紧支及支集包含，并保持真实 jet。因此任意 x∈P 恰可写为一个真实测试 φ 的 jet。原 hb 对这一个 φ 直接给 |Lx|≤C‖Jx‖，不会因把测试分拆求和而增加常数。泛函实际定义为 Lx=−⟨u,Dx⟩；D 是一阶真实纤维的 i 坐标。`sobolevJet_derivative` 将其严格识别为同一测试的实际坐标 Fréchet 导数 L² 类。

第1项得到 v 后，对每个原测试的 jet 应用表示身份，得到 ⟨v,φ⟩=−⟨u,∂ᵢφ⟩，从而是所要求的弱导数，负号正确。第3项反向直接由同一弱身份和 |⟨v,φ⟩|≤‖v‖‖φ‖≤C‖φ‖，常数无损。没有预设 u 已有任何弱导数或 Sobolev 正则性。虽然导入了 DirichletPoincare 模块，此处只使用测试 jet 的精确方向分量身份，实际声明不要求域有界或 Poincaré 常数。

## 逐测试极限、量词和无需候选导数收敛

第4项在任意开域 S 上给定实际 u、U_n、V_n∈L²(S)。其 hlim 仅要求每个固定测试 φ 的 ⟨U_n,∂ᵢφ⟩ 收敛到 ⟨u,∂ᵢφ⟩；hweak 是 ∀φ、最终 n 有相应分部积分身份；hbound 是最终 n 有 ‖V_n‖≤C。每个测试的最终阈值可以不同，类型没有把 ∀φ eventually 偷换成 eventually ∀φ。

证明对一个任意固定 φ，交合 hweak φ 与 hbound 的最终集合，然后用 Cauchy–Schwarz 得到 |⟨U_n,∂ᵢφ⟩|≤C‖φ‖。绝对值连续和 `le_of_tendsto` 将闭不等式传到极限；ℕ 的 atTop 非平凡性由实际过滤器实例供应。对全部 φ 得到同一 C 的测试界，再调用第2项构造 v。V_n 可以不收敛，且不要求其任何子列已知弱收敛。也没有声称新 v 就是某个预设 V 的极限。

第5项明确保留 U_n→u 的原 L² 强收敛、每个 n 的真实弱身份、V_n 最终统一界。连续内积把强收敛转为第4项所需的每个测试配对收敛，恒真的弱身份给逐测试 eventual。它没有要求导数强收敛、原状态光滑、统一点态支配函数或 H² 零延拓。

所有五项保留 C≥0 的同一常数，支持无界开域、任意维数和空域；第2–5项以 i:Fin d 指定实际坐标，d=0 时没有该坐标，未在零维虚构导数。第4项可用于域穷竭，只要将具体内域问题的字段作为真实 L² 类并另外证明逐测试最终身份；本批没有提前宣称这些内域数据已经存在。原时间 T、网格和允许权不出现在本辅助阶段，不发生相应量词收紧。

## 固定依赖、构建及递归公理

三新模块的 Carleman 导入闭包共36模块，其中33旧模块与已验收基线 `8bfc0cb3d9a3d394805cfbb9720d903fc139bdfe` 逐字节不变。另独立核对关键旧来源：SpatialTestOperations 的31模块闭包和 DirichletPoincare 的33模块闭包，相对 [T040](T040-local-acceptance.md) 固定证明 SHA `4f669626b3228adea39a16fbf6c1d22313763331` 均完全不变。已实际读取关键证明，而非只引用旧报告。固定 root 导入三模块；新增源码没有 sorry、admit、额外 axiom 或 native_decide。

原稿及治理协议、Lean 和 mathlib pins 与 base 不变；原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean 固定4.35.0，mathlib pin 及本机实际干净 HEAD 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。直接读取的 mathlib Hahn–Banach/Riesz 源码来自该 pin。

实际 `/tmp/carleman-bounded-limit-target.log` 记录3169 jobs构建成功，`-full.log` 记录3892 jobs构建成功及6787声明递归审计PASS。固定 `/tmp/carleman-bounded-limit-local-axioms.txt` 为 **2,085,893 bytes**，SHA256 **`94b2ec60a7ea2cb40147fcb603c70b448a8df5b2973b20ff74e6effe2d87b025`**。五项完整展开类型与清单一致，全部依赖仅为 `propext`、`Classical.choice`、`Quot.sound`。

已扫描全文2362条非空及8条无公理打印记录，未发现其他公理。固定 `CheckAxioms` 的递归主体与 base 相同，对环境内经 privateToUserName 识别的全部 Carleman 声明执行 collectAxioms，包含私有及生成声明；最终6787项审计PASS不是仅五项显式打印检查。

## 同 SHA 正式 CI 与自行下载的原始产物

本 Agent 独立经 GitHub connector 查询 [main CI 39210179049 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39210179049/attempts/1)。run 为 main/push，head SHA 精确匹配，最终 completed/success，`updated_at=2026-10-19T06:32:28Z`。三 job 全部 completed/success：state-check **117921583743**、lean **117921583917**、dashboard / snapshot **117922526076**。已等待 Lean 缓存收尾及 dashboard 完成，没有把提前上传产物当成完整 CI 成功。

同 run 原始 artifact：`lean-ci-result` **12167078533**，压缩产物492 bytes，digest `sha256:845599af0b9e8ee383515cb0cc4d481f95e464066dfe59021285f241263de33b`；`lean-declaration-evidence` **12167720896**，压缩产物191696 bytes，digest `sha256:67f4a8233ef3e9a74bce73f2dafa00719288b2ccd4d62ef558a663d5bd39755c`。两份 workflow_run 元数据均绑定该 run、main 和完整 proof SHA。本 Agent 自行执行两次 `gh run download 39210179049`，下载至约定 `-main-ci` 和 `-main-axioms` 目录，两次均 exit 0。

实际 `/tmp/carleman-bounded-limit-main-ci/result.json` 为 **PASS**，`checked_sha=source_head_sha=b7491fa1b22b01515e8d0c428f35a3dbe301c34f`，targets 为 Carleman，`finished_at=2026-10-19T06:31:12.398703+00:00`，ci_url 指向上述 run/attempt。Lean 编译器提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib 为上述 pin。解压 result 为537 bytes，SHA256 `b718676943e8bc40f83865052571f0f6f421a01d83af8aaca453dc70490d219b`。

独立逐字节比较 `/tmp/carleman-bounded-limit-main-axioms/axioms.txt` 与固定本机副本，完全一致：**2,085,893 bytes**、SHA256 **`94b2ec60a7ea2cb40147fcb603c70b448a8df5b2973b20ff74e6effe2d87b025`**，末行实际为 **6787项全声明递归审计PASS**。五项实际类型及三项基础公理均由该同版本原始证据确认，未使用后续工作树的公理产物。

## 验收决定

**C143：PASS，可升级为 REVIEWED，scope 保持 AUXILIARY。** 五项声明未发现需修复的数学缺陷。同常数 Hilbert 表示、原全部真实测试、实际 L² 弱导数、精确 iff、逐测试最终量词及无候选导数收敛的极限构造均已独立核实；同 SHA 三项正式 CI 和自行下载的原始公理证据一致。

本批没有完成原 `prop:analytic-realizations` 或 Grisvard 整个正则定理，P023 不提升，原文保持 **14/26**。本次仅新增本报告，未修改实现、台账、原稿或 root，未 commit/push。签发 UTC 如上固定；最终核对并通知主 Agent 后冻结本报告及时间戳。
