# T265 / C281 独立本机数学验收

- checked_sha: `307dfe985c233861eaa26acda1cc2f6ab30596d7`
- base_commit: `a53469931caaf52a06accc38b94778d5e007a5b8`
- reviewed_at: `2026-10-20T11:36:44+00:00`
- reviewer: `accept_spatial_lemma`（独立于实现者）
- result: **PASS，10 / 10 显式定理，无阻断缺陷**
- axiom_check: **PASS**
- scope: **AUXILIARY**；覆盖保持 **20 / 26**，不提升 P024。
- evidence_source: **local**；未查询 CI/看板，未重跑全库或不变依赖。

已直接读取固定 Git 对象的三个新增模块、全部实际打印类型、对应分析与 MATH_SPEC、原稿及关键实际依赖。报告定稿后冻结正文与时间，仅提交本报告。

## 原文对应和实际范围

原稿 `paper/main.tex:2672–2730` 的 Proposition A.3 要求原域上全部弱周期状态的热 Carleman 估计，2730 行使用密度传递。本批是一般多面体证明路线中从真实内域回到原域的**空间**逼近环节，保留原 Dirichlet 梯度形式、原 L² 载荷和同一给定原解。

对原有界开域 S、d>0、任意递增开穷竭 Tₙ⊆S，原解 u∈H¹₀(S) 满足真实弱负 Laplacian 方程、每个内解 vₙ∈H¹₀(Tₙ) 满足同一个 f 的实际限制载荷，则本批证明
\[
E_0v_n\longrightarrow u\quad\text{于完整弱 H¹ jet 拓扑},
\qquad
E_0(f|_{T_n})\longrightarrow f\quad\text{于原 }L^2(S).
\]
后一结论对任意范数加法群值 L² 场成立。对任意原关联算子图系数 z，内部构造每个内域的真实图系数 Zₙ，精确满足
\[
A_nZ_n=(Az)|_{T_n},
\]
并得到 E₀ 值、全部真实弱梯度、E₀ 算子载荷分别强收敛到 z 的对应原字段。最终具体定理内部供应任意固定平移 N 后的指数和内穷竭 \(T_n=\mathrm{halfspaceSmoothInner}(\ell,b,N+n)\) 的全部集合条件。

这不是把 \(E_0Z_n\) 视为原算子图元素的“图范数收敛”：代码从未断言 \(E_0Z_n\in D(A_S)\)，也没有断言 \(A_S(E_0Z_n)=E_0(A_nZ_n)\)。零延拓只在真实 H¹₀ 状态和 L² 字段层面使用。周期轨道、时间导数、加权时空能量及最终原域热估计尚待后续，不计 P024 完成。

## 逐声明核对

以下均在 `Carleman` 命名空间。实际三模块源码顺序、固定 T265/C281 清单、根导入与审计打印项一致，共 10 个 theorem。

| 模块 / 行 | 声明 | 实际核对与结论 |
|---|---|---|
| DirichletExhaustionStrong:14 | `WeakSobolevJet.extendDirichlet_pairing_extend` | **PASS**。两个实际 H¹₀ jet 的一阶字段均按真实 L² 零延拓；限制—零延拓互逆与真实内积伴随给精确梯度配对身份，常数 1。 |
| :23 | `IsWeakNegativeLaplacian.subdomain_orthogonal` | **PASS**。原方程对延拓后的任意内域 H¹₀ 测试合法；内方程对同一测试合法；真实载荷限制伴随消去右端，得到 \(\langle\nabla(u-E_0v),\nabla E_0w\rangle=0\)。没有假设目标正交性。 |
| :48 | `dirichlet_subdomain_gradient_best_test` | **PASS**。对 w=v 和内域真实紧支测试各用正交性，得 \(\|e\|^2=\langle e,\nabla(u-\phi)\rangle\)，由 Cauchy–Schwarz 得最佳测试界；零误差情形不作非法除法。 |
| :74 | `dirichlet_subdomain_norm_best_test` | **PASS**。差 jet 真实属于外域 H¹₀，以外域固定 slab Poincaré 及完整有限字段范数界得到 \(\|u-E_0v\|\le(2R+1)\|u-\phi\|\)。未把 jet 范数误写成梯度半范数或错误的范数恒等式。 |
| :93 | `dirichlet_exhaustion_strong_H1` | **PASS**。原 H¹₀ 闭包供应任意精度的一个真实 SpatialTest；紧支撑的递增开覆盖给统一尾段支撑资格，故每个充分大 n 均满足误差界，得到同一 u 的完整序列强收敛。 |
| SubdomainLpLimit:12 | `subdomainZeroExtend_restrict_ae` | **PASS**。原 L² 代表的实际限制、真实零延拓，给 \(E_0(f|_T)=1_Tf\) 在原限制测度下 a.e. 相等；区分 T 内/外，未把任意代表当逐点相等。 |
| :23 | `subdomainZeroExtend_restrict_tendsto` | **PASS**。用可数 `ae_all_iff` 统一所有 n 的代表身份；每点最终属于 Tₙ 给 a.e. 收敛；平方差被真正可积的 \(\|f\|^2\) 支配，得原 L² 强收敛。 |
| :42 | `subdomainZeroExtend_restrict_tendsto_of_exhaustion` | **PASS**。从真实单调性和覆盖推出逐点最终成员资格，不增加共同进入时刻或有限测度假设。 |
| InnerGraphLimit:15 | `exists_dirichlet_exhaustion_graph_approximation` | **PASS**。对每个原 z 和全部 n 用真实零位移 coercive resolvent 构造 Zₙ；精确限制载荷身份内部证明；同一完整 H¹ 极限经 value/field CLM 给值及梯度极限，算子载荷极限由上项给出。 |
| :61 | `exists_halfspaceSmoothInner_graph_approximation` | **PASS**。原有限严格半空间有界域内部给原/内开性、包含及内域有界性；指数和逐点最终进入及单调性给任意固定 N+n 的完整穷竭。结论没有另给穷竭、解、中心、初始内域非空或目标收敛的输入。 |

上述 10 项完整类型已从固定 raw 的 45715–45820 附近逐项核对；所有显式前提均在源码和最终结论中保持，没有用较小测试族或较小原状态空间替代原对象。

## 关键数学与量词

**原 H¹₀ 与弱测试。** 直接复核了 `DirichletSpace` 的定义：真实全 SpatialTest 的线性张成在完整 H¹ jet 拓扑中的闭包。`exists_test_of_mem_test_span` 通过实际紧支光滑函数的加法、数乘及 jet 值唯一性，把有限线性组合重新表示为一个真实测试。`isWeakNegativeLaplacian_iff_dirichlet` 由真实配对连续性把完整紧支弱身份延拓到任意 H¹₀ jet，因而测试 v 本身以及其零延拓均合法，没有要求 v 光滑。

`DirichletZeroExtension` 从原 H¹₀ 闭包的全空间测试配对证明实际一阶弱导数零延拓；`DirichletSubdomainExtension` 再真实限制到 S，并用闭包连续性证明属于 H¹₀(S)。已读实际 value/field 身份和 `SubdomainZeroExtension` 的内积伴随证明。这里始终只有一阶弱链，不曾跨边界引入二阶零延拓。

**正交与全序列。** 两个方程的右端都是同一 f 与同一测试的实际 L² 配对。正交减法符号正确：
\[
\|\nabla(u-E_0v)\|^2
=\langle\nabla(u-E_0v),\nabla(u-\phi)\rangle.
\]
全范数控制使用外域 S 的有界性选 R>0 和一个坐标 i，常数 2R+1 与内域、n、u、f、测试无关。对给定 ε、u 先取 \(\|u-\phi\|<\varepsilon/(2R+1)\)，再由真实紧支撑和单调开穷竭选尾段 N。这个 N 可以依赖测试和 ε；但结论对所有 n≥N 成立，未选择稀疏子列、未使用弱紧性或预设逼近序列。

**L² 代表与支配。** `subdomainLp_ae` 的 a.e. 身份先在实际 T 限制测度下取得，再以可测 T 转为原 S 测度下的条件身份。零延拓在 T 外确实为零；故平方差在 T 上为 0，在 S∖T 上为 \(\|f(x)\|^2\)。Lp 自带 MemLp 资格内部给该平方可积性。可数 n 的零测例外统一合法；没有不可数交换或沿代表点值的未经证明收敛。所用 `LpDominatedLimit` 实际证明 \(\|u-v\|_{L²}^2=\int\|u(x)-v(x)\|^2\)，然后用 DCT 与平方根传到强拓扑。

**真实关联算子。** `boundedDirichletOriginalForm` 的双线性型就是全部弱梯度的 L² 内积；外域 slab Poincaré 内部供应 coercivity，真实 H¹₀ 的完备性及稠密嵌入给原关联算子。直接读取了 `FormSolve` 的真实变分求解构造：`resolvent 0` 属于真实关联域，且其 operator 值精确等于给定载荷，不假设已有逆或解。每个内域调用的载荷是原 `B.graphA z` 的实际限制。

`dirichletDomainJet_graph` 从真实算子图双向刻画和全 jet 值唯一性得到同一原 z 的 H¹₀ jet 及真实弱方程。`graphOfDomain`、`graphDomain`、`graphH`、`graphA` 的实际投影身份保证没有换解或只匹配抽象标签。通过同一 H¹ 全序列极限的两个实际连续字段投影得到值和梯度极限；算子载荷虽在各自不同的图内，却有精确的限制身份可供独立 L² 极限。

**几何及边界情形。** 最终具体结果对任意固定 N、全部原图系数 z 成立，N 在 z 前量化；从原严格半空间点 x 的有限指数和趋零得到最终成员资格，再用单调性给平移后的覆盖。任意 N 的初始内域可能为空，证明不要求其有中心或非空，实际零空间上的变分构造仍合法。原域有界、开及 d>0 均显式；正维数用于选 Poincaré 坐标，不声称 d=0 情况。时间 T、网格、时间步长或 h/dt 条件完全没有出现在这些空间定理中。本批没有增加原问题的解正则性、紧嵌入或 H² 资格假设。

## 依赖边界与固定本地证据

实际递归 Carleman import 闭包共 **338** 个模块，**335** 个旧模块与基线逐 Git blob 不变，仅本批三个新增模块。已直接核对上述实际依赖及 `SpatialTestExhaustion` 的真实紧覆盖证明、`HalfspaceSmoothExhaustion` 的包含/单调/最终进入证明。没有重审或重建不变的全部历史。

台账中的 T264/C280 是阶段顺序依赖；独立枚举确认其三个模块 `InnerGraphDensity`、`DomainHeatIntegral`、`UniformInnerWeakHeat` **均不在本批数学 import 闭包中**。本报告没有将尚在独立验收中的 T264 宣称为已验收，也不以其热估计作为本批空间结果的前提。

独立读取 `/tmp/carleman-t265-local-evidence.json`：source=`local`、status=`PASS`、checked/source SHA 都是本报告 proof；根构建和递归审计命令记录 exit 0；finished_at=`2026-10-20T11:34:01.274493+00:00`。以下均为本次实际读取和哈希核验的固定产物，非本次重新构建。

| 证据（前缀 `/tmp/carleman-t265`） | 独立核对 |
|---|---|
| `-local-source-manifest.txt` | **1070 条，116119 bytes**；固定树全部 tracked `.lean` 与工具链三项配置逐 Git blob SHA256 相同，清单无重复或遗漏；整体 `d49648ed32f81e99a5daa5397822c588a72b3e80c9962923287e125c30fb7f75`。 |
| `-target-build.log` | `InnerGraphLimit` 构建成功，**3544 jobs**；104 bytes；`d2f3c51add1aa7c52ee57a4822437f3d4f1eaad3d5fa0294df25949fdcd90dfa`。 |
| `-build.log` | 根构建成功，**4312 jobs**；80 bytes；`af8edab910aa54f43703d46598b103fe5c9206c946b04357b2711ae59d140be6`。 |
| `-axioms.log` | 空 stderr，0 bytes。 |
| `-inner-graph-limit-local-axioms.txt` | **3530766 bytes**；`73c5a6532823c37ef4131c1ed6ba2736fb47424ebf3860668dcf392f6d63ae03`；实际末行 **10382** 项全命名空间递归公理审计 PASS。 |

本批 10 个声明都在实际根导入与 `#check` / `#print axioms` 中；各声明仅含 `propext`、`Classical.choice`、`Quot.sound`。raw 全部 **4209** 个显式公理列表也只含这三项，另有 **10** 项不依赖公理。递归审计代码与基线不变，无 `sorryAx` 或未经证明的数学公理。

Lean 为 4.35.0，编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；固定 lock 和实际干净 mathlib checkout 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。原稿与基线逐字节相同，SHA256=`492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`；已读治理文件的哈希与上一轮相同，继续遵守固定本地验收协议。工作树未来增量及动态 raw 均排除。

独立复核记录：`/tmp/carleman-t265-review-verification.json`；完整类型摘录：`/tmp/carleman-t265-reviewed-types.txt`。

## 验收决定

**10 / 10 PASS，无修复项。** C281 可按固定证明版本登记 REVIEWED / AUXILIARY。真正原弱解的完整 H¹ 全序列强收敛、实际限制载荷的 L² 强收敛、原全算子图系数的内域构造均成立。尚未完成周期时空和最终热 Carleman 极限，不提升 P024 或其他原文覆盖项。
