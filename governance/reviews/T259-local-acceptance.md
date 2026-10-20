# T259 / C275 独立本机验收

- checked_sha: `0a4c425a254d6bc108651a078b6c0adbcc02b9f5`
- mathematical_base: `41f754d3e85d22b62c6e6229f5629bee782b0bc6`
- reviewed_at: `2026-10-20T10:49:20+00:00`
- reviewer: independent local Agent `/root/accept_spatial_lemma`
- result: **PASS，9/9 显式定理；无阻断缺陷或修复项。**
- axiom_check: **PASS**
- evidence_source: **local**；独立核验固定源码和本地实际执行证据，不查询 CI/看板，不重复全库构建。
- scope: **AUXILIARY，18/26；原非空有界有限严格半空间交的 Dirichlet H² 正则性、完整估计和实际算子域等式。尚不提升整项 P023 / Corollary A.2。**

## 原文与实际范围

完整读取固定 `Carleman/Spatial/FiniteHalfspaceRegularity.lean`、全部九项展开类型及公理、T259 analysis、MATH_SPEC 对应段、原 `paper/main.tex:2659–2665`。原 Corollary A.2 要求指定凸多面体/盒上的 Dirichlet Laplacian 满足全部空间解析假设。本批真实清偿其关键 H² 正则性与图估计，不把尚待装配的平方根/权接口整包宣称完成。

具体几何是 `S={x | ∀ i, b i < ℓ i x}`，指标有限，ℓᵢ 为真实连续线性泛函，S 有界，有实际一点 c 满足所有严格不等式，且 d>0。它覆盖原满维非空有界凸多面体的半空间表示，在所有正维均成立，特别包含原 d=2,3。没有法向独立性、非冗余表示、直角面、光滑角点或预设边界光滑性条件。非空与 d>0 保留为明确前提；不把本批写成空域或零维实例。

令 `N_d=card(Sym(Fin d,2))`。输出的原域二阶字段平方界为 `‖field₂ v‖²≤N_d²‖f‖²`，给定原弱解的二阶范数界为 `‖field₂ v‖≤N_d‖f‖`。这是原完整对称二阶字段的真实 L² 范数；不是最优常数 1 的有序 Hessian 估计。完整 H² 范数亦由原 L² 载荷控制。最终实际 `model.domain` 精确等于同一 L² 空间里的 `sobolevSubspace d 2 … ⊓ dirichletSubspace S`，并对其真实 `domainSobolevJet` 给出正图估计常数。

## 全部九项声明

省略名称共同前缀 `Carleman.`。源码行是固定新模块，raw 行是固定原始公理文件完整类型起点。固定 C275/T259 清单、源码声明及审计条目逐项相同。

| 源码 / raw 行 | 声明 | 独立结论 |
| --- | --- | --- |
| 13 / 44778 | `IsWeakNegativeLaplacian.unique_dirichlet` | PASS；任意有界开正维域的同载荷原 H¹₀ 弱解，经实际 associated graph 和零移位 resolvent 唯一性恢复整个 H¹ jet 相等。 |
| 26 / 44784 | `finite_halfspace_isOpen` | PASS；有限个真实连续泛函严格不等式的交是开集。 |
| 32 / 44787 | `exists_finite_halfspace_dirichlet_H2_solution` | PASS；内部选择含同一内点的真实 shifted exhaustion、真实限制载荷解、同状态 H² lift 及统一 Hessian 界，原域极限有原 Dirichlet 值、实际 −Δv=f 和 N_d² 平方界。 |
| 69 / 44796 | `finite_halfspace_dirichlet_H2_regular` | PASS；从上述存在解用实际弱解唯一性识别其完整 H¹ 截断为给定 u，保持同一 f；非负量合法开方给 N_d 范数界。 |
| 88 / 44809 | `exists_finite_halfspace_dirichlet_H2_estimate` | PASS；原有界几何先选 slab 半径 R，K=(2R)²+2R+N_d 先于全部 u/f；原 Poincaré、梯度能量与 Hessian 界控制真正完整 H² 范数。 |
| 117 / 44821 | `finite_halfspace_dirichlet_domain_le_h2` | PASS；实际 form-operator domain 的任意原状态由完整图刻画给弱解，新正则性给同值真实 H² jet。 |
| 130 / 44828 | `finite_halfspace_dirichlet_domain_eq_h2` | PASS；新 H² 包含与原 domain≤H¹₀，加上真实全 H¹₀ Green 公式的反向包含，得到完整域等式。 |
| 142 / 44836 | `dirichlet_graph_estimate_of_weak_estimate` | PASS；泛型 helper 明示 hD/hreg，实际弱 lift 与 canonical jet 经原值唯一性完全识别，Creg=max(1,K)>0。 |
| 168 / 44855 | `finite_halfspace_dirichlet_graph_estimate` | PASS；具体终点内部清偿 hD/hreg，不把目标正则性或域包含遗留为额外输入。 |

## 实际证明检查

**原弱解唯一性。** `IsWeakNegativeLaplacian` 使用全部原 `SpatialTest S`，不是一个较小测试族。`dirichlet_operator_graph_iff` 将这套身份通过实际 H¹₀ 测试闭包延拓到原完整能量空间，给真实 associated operator 的元素 z,w。两者满足 A z=f=A w，故调用已构造的 coercive-form resolvent 在 r=0 的唯一性。实际旧证明来自 Lax–Milgram 变分解与原嵌入，不是新假设的 PDE 唯一性、H² 正则性或 Dirichlet 边界点值。取得 L² 值相等之后再用开放域完整弱射流的值注入性，得到 u=v 的整个 H¹ 等式。

**真实 shifted 内域与全部层。** 由原 c 的所有严格不等式，真实指数和 `halfspaceExpSum` 趋零，选择 N 使 c∈inner(N)。取 Tₙ=inner(N+n)，单调性保证同一个 c 在每个 Tₙ，供所有层的边界正则性与强密度调用。开放性、Tₙ⊆S 和单调性均使用真实已证指数和几何。对任意 x∈S 选一层 n 含 x，随后 n≤N+n，故 x 也在 Tₙ；这证明完整 shifted 尾序列仍覆盖 S，没有把覆盖偷换成偶然子列或只覆盖较小域。

**内解及统一常数实际供应。** 每个 Tₙ 的弱解由实际 coercive Dirichlet form 的零移位 resolvent 构造，载荷严格是 `subdomainLp (hTS n) f`。T246 的真实 smooth-inner 正则性给 Uₙ，且完整 H¹ 截断精确等于该内解、实际 negativeLaplacian 等于同一限制载荷；由此原 H¹₀ 资格也保留。T258 对这个真实原 H²∩H¹₀ 状态给

```text
‖field₂ Uₙ‖ ≤ sqrt(N_d) ‖f|Tₙ‖ ≤ sqrt(N_d) ‖f‖.
```

后一不等式用真实 L² 限制算子的范数收缩，乘数 sqrt(N_d) 非负。统一性与 n、图册、分割及各内解无关；没有把有限层正则性常数拿来充当统一常数。随后 choose 取得的 Uₙ、H¹₀ 资格、载荷身份和界是同一批对象。

**原域测试、弱极限与 N_d²。** 已完整读实际 `exists_dirichlet_H2_of_exhaustion` 及关键调用。它只将内解的 H¹₀ 截断真实零延拓至 S；候选 Hessian 各分量只是 L² 零延拓，不宣称这时存在全空间或原域 H² 零延拓。原有界域的同一 slab 给全部 H¹ 预算，内部构造同一原 H¹₀ 闭子空间的有界弱子列；其值/梯度都沿同一严格递增子列弱收敛。

对每个原 compact SpatialTest，实际单调开穷竭与 compact support 给最终整个支撑落在 Tₙ。这时原测试本身可合法视为 Tₙ 测试，真实延拓配对给正确负号的 Hessian 弱身份及同一 f 的 Poisson 身份。所需最终索引可以依赖测试；证明不非法选择对全部测试同时有效的单一索引，也不交换不可数 AE 集。沿共同子列，这些最终身份仍成立。候选 Hessian 不需预设收敛或全域弱身份：实际有界测试/Riesz 构造给原弱梯度的全部二阶导数，真实混合弱导数交换后装配完整 Sym 字段。原全部测试上的 RHS 唯一性给 negativeLaplacian v=f，原 H¹₀ 闭包保留。

该旧极限定理的输出是 `‖field₂ v‖²≤N_d·C²`。本批代入 C=sqrt(N_d)‖f‖，实际 `sq_sqrt` 需要的 N_d≥0 由自然数基数给出，于是确为 N_d²‖f‖²。额外 N_d 来自逐分量界求和；本批未声称消除了它或保留 classical 常数 1。

**给定原状态与完整 H² 估计。** 存在解 v 的值在原 `dirichletSubspace S`，通过已证 `mem_dirichletJetSpace_iff` 识别其 H¹ 截断的真实 H¹₀ 成员资格。其完整弱方程由实际 negativeLaplacian 身份给出。新唯一性据此把该截断识别为输入的任意原弱解 u；不是只证明存在一个未关联的 H² 解。取平方根时两边非负，无除以 ‖f‖ 或 Hessian 范数，零载荷情形同样成立。

由 hb 先选 R>0、全 S 上 ‖x‖≤R，取真实坐标 i=0，得 |xᵢ|≤R。实际弱方程以原 u 测试给梯度界 ‖field₁u‖≤2R‖f‖，原 H¹₀ Poincaré 再给值界 ≤(2R)²‖f‖。完整 H¹ 截断身份识别 v 的第 0/1 字段；实际 `norm_le_sum_fields` 与真实零阶字段范数身份给

```text
‖v‖ ≤ ((2R)² + 2R + N_d) ‖f‖.
```

R 和 K 仅由固定几何/维数选取，在全部 u/f 量词之前；不依赖内域索引、状态、载荷、时间或允许权。不宣称 K 在所有原域之间统一，也不误将完整 jet 范数直接等同于 Hessian 半范数。

**实际域等式与 canonical jet。** 对任意真实 domain 元素，取原算子值 f，完整 graph iff 给同值 H¹₀ 弱解；其新 H² lift 的值等于该原 domain 元素，故进入原 sobolevSubspace。原 model 的 domain≤V 与新包含给正向交空间包含；反向 `h2_dirichlet_le_domain` 实际用完整 H¹₀ Green 配对构造原 associated domain 元素，算子值确为真实负 Laplacian。没有另造较小 domain 或只核查光滑 core。

泛型图估计的 hD/hreg 明确存在于其类型，具体最终定理分别调用本批新域包含和统一弱估计清偿。`domainSobolevJet` 是通过真实 Sobolev 值等价所取的 canonical 全阶 jet；证明核对它的实际值正是原 z，并以弱唯一性将它完全等于有界的 v。因此 Creg=max(1,K) 在全部 z 之前为正，右端是真实同一 model.operator z；没有对任意选定代表的边界值作推断。

## 依赖边界及独立前置报告

实际 Carleman 导入闭包 **313 模块**，其中 **312 个旧模块相对 mathematical_base 全部 Git blob 不变**；仅新 `FiniteHalfspaceRegularity.lean`。本批直接核对 `WeakConvexHessian` 全文、原指数和几何与 T246 调用，以及 `DirichletExhaustionLimit`、`DirichletH2ApproximationLimit`、`SpatialTestExhaustion`、`DirichletExtensionHessianTest`、`DirichletSubdomainSolve`、`DirichletWeakSolve`、`DirichletWeakSubsequence`、`WeakH2BoundedLimit`、`WeakH2BoundedTest`、`WeakLaplacianLimit` 的关键实际证明。原梯度 form、全图识别、Green 反向包含、resolvent 唯一性与 canonical jet 定义也直接复核；不重新审核无关历史。

已全文读并验证 T258 正式冻结报告：`governance/reviews/T258-local-acceptance.md`，报告提交 `8b4fa0e5f90c6d70abbc834880571d878e5184cd`，checked_sha 为本批 base，reviewed_at=`2026-10-20T10:44:39+00:00`，9/9 PASS；11,615 bytes，SHA256 `1ae08efc1fb341147d18dee4e1922ad6ee90c4b2667493b0cb6cb575100c3036`。**该报告提交晚于 T259 proof，作为分离冻结验收证据读取，不声称它已在该 proof 树内。** 其实际 sqrt(N_d) 界、完整原 H² 强密度和 classical 界传递资格与这里的调用一致。

另核对关键旧源与已接受版本一致：T246 `FiniteLocalH2Gluing` 对 `ebc85ddad04c9b4008fa5b3e89a05696eff19bfb`，指数和几何对 `721b761224ad1b6425466bc956417ddce7f41908`，`DirichletDistribution`/`DirichletLaplacian` 对 `3d5aa9cec281974bef7da9d37ffa11a8f9f75670`。内域 H²、强密度和本批原域穷竭之间没有循环使用本批目标正则性。

## 精确本地证据

- `/tmp/carleman-t259-local-evidence.json`：source=local、PASS，checked/source SHA 均为本报告 proof；根构建/公理命令实际 exit 0，finished_at=`2026-10-20T10:46:15.207387+00:00`。固定任务 local_validation 同样记录目标/根/公理全部 exit 0。
- `/tmp/carleman-t259-local-source-manifest.txt`：**1,056 项、114,622 bytes**，SHA256 `400fa13124e87061330a90fad8ba154e965c415cc04a845ec17919159fed2e24`。独立枚举固定提交全部 tracked Lean 源及三个工具链配置，路径集、唯一性与每一项 Git blob 摘要均吻合，未使用未来工作树。
- `/tmp/carleman-t259-target-build.log`：**3,511 jobs** 成功，114 bytes，SHA256 `1dd1f314c6e79f9c0ad12ef474e531029b279f2b4937db42a6041d6cef74c4a4`。
- `/tmp/carleman-t259-build.log`：**4,298 jobs** 成功，80 bytes，SHA256 `7767faa9a7dfe1590d698f9a42f2aeb1a5b26e26b29236fb0e9b187db18afc8e`。`/tmp/carleman-t259-axioms.log` 为 0 bytes。
- `/tmp/carleman-t259-finite-halfspace-regularity-local-axioms.txt`：**3,455,016 bytes**，SHA256 `52a50bd1a30a4c92aaf59e875c35baa78dd82558e89f32d0ad0acf531a2f09eb`；实际末行 **10,291 声明递归审计 PASS**。九项完整类型与依赖公理均逐项核对；全 raw 的 4,145 个公理列表仅含正常 `propext`、`Classical.choice`、`Quot.sound`，另有 10 个无公理记录。无 sorryAx 或新增数学公理，递归收集/白名单逻辑相对 base 未改。
- 根模块 import 与九项 `#check`/`#print axioms` 完整。Lean 4.35.0 / compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib lock 和干净 checkout 同为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。
- 原稿相对 base 不变，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`；AGENTS/治理协议摘要与已读版本相同。本批只核验已有真实本地执行产物，没有声称 reviewer 重新运行全库或远端 CI 通过。

**接受 T259/C275 的上述 AUXILIARY 范围。** 具体原域结果已无预设光滑穷竭、内解、目标 H² 或统一界输入；实际给定弱解的完整正则性、完整范数控制及 associated operator 域等式均完成。整条 Corollary A.2 空间接口仍待包装和独立验收，本报告不提升 18/26 覆盖。正文与 reviewed_at 在单文件提交后冻结；不改数学、台账、其他报告，不 push。
