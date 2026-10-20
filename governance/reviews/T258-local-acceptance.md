# T258 / C274 独立本机验收

- checked_sha: `41f754d3e85d22b62c6e6229f5629bee782b0bc6`
- mathematical_base: `e90a9dc75ebc85da3ccb5dd1bb740fd3d255db1a`
- reviewed_at: `2026-10-20T10:44:39+00:00`
- reviewer: independent local Agent `/root/accept_spatial_foundations`
- result: **PASS，9/9 显式定理；未发现阻断缺陷或修复项。**
- axiom_check: **PASS**
- evidence_source: **local**；核对固定源码、真实本地构建及原始公理证据，没有查询远端 CI 或看板，没有重复全库构建。
- scope: **AUXILIARY，18/26；完成原指数和光滑内域的弱 Hessian 统一估计，不提升 P023。**

## 原文、实际对象与范围

读取固定 `Carleman/Spatial/WeakConvexHessian.lean` 全文、全部九项完整展开类型与公理输出、T258 analysis、MATH_SPEC 对应段以及原 `paper/main.tex:2659–2665`。原 Corollary A.2 要求凸多面体或盒上的 Dirichlet Laplacian 满足全部空间解析假设。本批是其凸域 H² 正则性路线中的统一二阶估计；尚未把内域解通过穷竭传到原多面体，也没有在本批构造原域弱解或装配整个 Corollary A.2。

设 `S = halfspaceSmoothInner ℓ b n`，`N_d = Fintype.card (Sym (Fin d) 2)`。本批最终两个定理对任意原 `u : dirichletH2JetSpace S` 证明

```text
‖WeakSobolevJet.field 2 u.val‖² ≤ N_d · ‖negativeLaplacian u.val‖²,
‖WeakSobolevJet.field 2 u.val‖ ≤ sqrt(N_d) · ‖negativeLaplacian u.val‖.
```

左端是原 `DerivativeFiber` 的全部无序二阶坐标分量的真实 L² 范数，右端是同一 jet 的实际负 Laplacian。`dirichletH2JetSpace` 保留完整 H² 状态与其 H¹ 截断的真实 H¹₀ 闭包资格，没有换成 H²₀、零法向导数空间或光滑状态。

最终输入为 `d>0`、有限半空间数据、原严格半空间交的有界性、所选内域的实际一点 `z`，以及任意上述原状态。光滑逼近、经典估计、图册、分割和目标 Hessian 界均不是最终输入。非空内域条件明确保留；没有宣称每个初始编号的内域都非空。泛型辅助定理允许其类型中的一般维数和域，最终具体结论明确使用 `d>0`。

## 全部九项声明

名称省略共同前缀 `Carleman.`。源码行号指固定 `WeakConvexHessian.lean`，raw 行号指固定原始公理文件中的完整类型起点。源码、固定 T258/C274 清单和对应 `#check` / `#print axioms` 条目逐项一致。

| 源码 / raw 行 | 声明 | 独立结论 |
| --- | --- | --- |
| 13 / 44718 | `realLp_norm_sq_of_ae` | PASS。任意实际实 L² 类与其 AE 代表的范数平方等于平方积分，由真实 L² 内积定义与积分 AE 同余推出。 |
| 22 / 44721 | `SpatialTest.allOrderJetOn_component_two_smoothD_ae` | PASS。实际 `Sym.cons j (Sym.cons i nil)` 分量恢复为 `D_j(D_i φ)`；通过真实 derivative test/Lp 身份保留内外次序。 |
| 31 / 44728 | `SpatialTest.allOrderJetOn_negativeLaplacian` | PASS。同一光滑 jet 的实际负 Laplacian 恰为 `-φ.laplacianOnLp S`，完整对角和与负号正确。 |
| 41 / 44731 | `SpatialTest.allOrderJetOn_negativeLaplacian_norm_sq` | PASS。真实负 Laplacian 范数平方等于原经典 Laplacian 平方积分；只在范数中消去负号。 |
| 47 / 44738 | `SpatialTest.allOrderJetOn_component_sq_le_hessian` | PASS。任意二阶 Sym 分量分解为两个实际坐标方向，其平方由全部有序 Hessian 平方和控制；积分可积性由有界域紧闭包与光滑性提供。 |
| 76 / 44743 | `SpatialTest.allOrderJetOn_hessian_bound_of_classical` | PASS。以真实字段范数平方精确拆分全部 Sym 分量，再逐项使用经典估计，得到准确因子 `N_d`。 |
| 92 / 44753 | `weak_hessian_bound_of_strong_density` | PASS。显式经典估计及真实完整 H² 强密度输入，通过字段投影与负 Laplacian 的连续线性映射传至同一原 `u`。 |
| 105 / 44764 | `halfspaceSmoothInner_weak_hessian_bound` | PASS。原内域的经典估计和完整强密度均由实际已证定理内部供应，得到任意原 H²∩H¹₀ 状态的平方估计。 |
| 117 / 44771 | `halfspaceSmoothInner_weak_hessian_norm_bound` | PASS。非负范数与非负平方根允许从平方估计开方，常数为 `sqrt(N_d)`；不除以状态范数或维数因子。 |

## 数学核验

### 真实积分、导数及范数

`smoothD e f x` 的定义是 `fderiv ℝ f x e`。`spatialLaplacian` 是真实坐标二阶 Fréchet 方向导数的对角和；`smoothHessianSq` 则是对两个坐标指标的完整有序双重平方和。新证明通过 `allOrderJetOn_component`、两次 `multiTest_cons`、`derivativeTest_toLp` 和实际 `derivativeLp_ae`，将原弱字段识别为这些导数，没有输入目标导数身份，也没有将无序指标直接视作有序矩阵。

负 Laplacian 的既有定义是各实际对角分量连续线性映射之和的负值。新第 3 项逐个对角项识别 Lp 身份，第 4 项再使用范数的负号不变及真实 `laplacianOnLp_ae`。因此实际作用仍为 `−Δ`，没有在弱方程层面遗漏负号。

对任意 `α : Sym (Fin d) 2`，两次 `Sym.exists_eq_cons_of_succ` 得到 `j,i`，剩余零阶指标等于 `nil`。每个分量平方先被相应一行的非负平方和控制，再被全部行和控制。两端的积分有限性不是作为目标估计输入：由光滑导数连续性及有界域紧闭包先证明可积，再限制到 S，故 `integral_mono` 的前提实际成立。

`derivativeField_norm_sq` 是原 Euclidean 字段的精确平方范数分解，证明本身使用有限指标的真实 AE 分量身份和有限可积求和。这里没有不可数 AE 量词交换。当前采用“每个 Sym 分量均不超过完整经典 Hessian 积分”的简洁上界，因此求和的系数确为 `N_d`。**本批没有证明弱 Sym 字段的 sharp 常数 1；T251 的常数 1 属于完整有序经典 Hessian 平方和。** 两者在类型、证明和范围中保持区分。

### 同一弱状态的完整强极限

实际 `HasSmoothDirichletH2Approximation u` 给同一列全空间紧支光滑测试，每项在 S 的整个真实 frontier 上处处为零、H¹ 截断属于原 H¹₀，且其完整二阶 jet 在完整 H² 图拓扑趋于同一个 u。泛型第 7 项保留该输入，具体第 8 项内部调用已证强密度消去它。

`fieldCLM 2` 是完整有限乘积 L² 图空间上的实际投影；`negativeLaplacian` 是该空间上的实际连续线性映射。故同一序列的完整二阶字段范数平方与负 Laplacian 范数平方分别趋于同一 u 的对应量。`le_of_tendsto_of_tendsto` 将每项经典不等式传到极限。没有把仅标量 L² 收敛当作 H² 收敛，也没有选择另一个具有相同值的未识别 Hessian。

具体定理从真实 `halfspaceSmoothInner_compact` 得到 S 的有界性，从 T251 得到每个光滑零边值成员的经典估计，从 T257 得到上述完整强密度。固定域的连续映射只用于传递收敛，其算子范数没有乘入最终估计。常数 `N_d`、`sqrt(N_d)` 仅依赖 d，与 n、ℓ、b、所选内点、截断、图册、分割、逼近序列以及原状态无关。

### 关键依赖的实际复核

完整读取固定 `ClassicalConvexHessian.lean` 的证明。其真实薄层积分身份、非负边界通量及紧坏集论证先给固定 δ 的边界误差控制；薄层质量由有限 `∫S |Δg|` 控制。真实示性函数支配收敛先令 ε→0，再令 δ→0，得到经典有序 Hessian 的常数 1。即使中间几何量随内域变化，它们也已在 δ 极限中消失。具体指数和内域内部提供光滑性、紧性、实际边界非零导数与凸通量资格；本批并未将这些资格作为任意原弱 u 的光滑假设。

完整读取固定 `FiniteStrongH2Density.lean`。双截断返回真实 ηu；局部图域/内部模型的强密度通过固定连续映射运输；有限光滑分割的真实和恒等式使完整 jet 精确恢复原 u。有限和采用同一逼近索引，保留整个 frontier 零值、每项原 H¹₀ 和完整 H² 强收敛。该构造没有使用本批待证的统一弱 Hessian 估计，依赖不存在循环。

T257 正式冻结报告另以提交 `ce10da05a21b2b2bcf4ef5f5661d3da7f64927ae` 全文读取并核对：checked_sha 为本批数学基线，reviewed_at 为 `2026-10-20T10:37:23+00:00`，17/17 PASS；14108 bytes，SHA256 `637ab46137aa855d9fc8edb5c3e1ebcdc6731e2b0c79ff189d94e3b4457f3960`。**该报告提交晚于 T258 proof，作为分离的冻结验收证据使用，不声称它存在于本批固定树中。**

本模块的 Carleman 递归导入闭包共 304 个文件，其中 303 个旧数学源与数学基线逐字节相同，唯一新增数学源为 `WeakConvexHessian.lean`。直接复核上述实际依赖及 `ComponentNorms`、`SmoothDirectionalCalculus`、`SmoothLaplacianL2Limit`、`SmoothLaplacianProduct`、`WeightedHessianIdentity`、`WeakLaplacian`、`SobolevTopology`，不重复审核无关历史。

## 固定本地证据与公理

实际读取 `/tmp/carleman-t258-local-evidence.json`，其 `source=local`、`status=PASS`、`checked_sha=source_head_sha` 均精确绑定本报告 proof；`ci_url=null`。真实完成时间为 `2026-10-20T10:37:58.072757+00:00`。记录的 `lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 均 exit 0；同时读取相应实际日志和原始输出，不把本地结果称作 CI。

| 证据 | 实际核验 |
| --- | --- |
| `/tmp/carleman-t258-target-build.log` | 3489 jobs，成功构建本模块；106 bytes，SHA256 `e7066400c783271e78e889db70dd5ee685927bc7c9273b875a596c6d39087c0a`。 |
| `/tmp/carleman-t258-build.log` | 4297 jobs，完整 Carleman 目标成功；80 bytes，SHA256 `9766440632cbdb8a910b483e26d60b63c13ad7ec0ac32ff26672ebdb0b493768`。 |
| `/tmp/carleman-t258-local-source-manifest.txt` | 1055 个唯一条目，114509 bytes，SHA256 `df47a6746f0100d283e694a5afba4116edc195da6969995691a7cd5b1f76e48a`；逐项取固定 Git blob 算 SHA256 全部相同，路径集合与固定受跟踪 Lean 源及三个工具链配置精确一致。 |
| `/tmp/carleman-t258-weak-convex-hessian-local-axioms.txt` | 3448168 bytes，SHA256 `57dda6590b5f1a63a862fd694c25821a37da86eb52d35d07d8f62db98d3aad24`；完整递归审计 10281 项 PASS。 |
| `/tmp/carleman-t258-axioms.log` | 0 bytes；审计 stderr 为空。 |

九项完整展开类型、公理输出、根模块 import 和审计条目均存在。原始文件内实际解析 4136 条公理列表及 10 条无公理记录；所有公理仅为正常基础 `propext`、`Classical.choice`、`Quot.sound`。递归检查器相对于数学基线未改变，完整审计未发现 `sorryAx` 或新增数学公理。

工具链为 Lean 4.35.0（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）；锁定 mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`，实际本地 mathlib HEAD 相同且工作树干净。原稿 blob 与基线不变，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。后续工作树、动态审计和其它 Agent 的数学增量均未作为本次证据。

## 最终判定

**C274 / T258 在上述固定版本的 9/9 定理全部 PASS，可按实际 AUXILIARY 范围接受。** 已完成每个合格指数和光滑内域上、全部原 H²∩H¹₀ 状态的维数统一二阶估计；没有剩余目标密度或经典估计前提。

原多面体穷竭传递、原域 H² 正则性及完整解析接口仍不在本批结论内。保持 **18/26、P023 不升级**；未发现需要修复的数学缺陷。报告签发后冻结正文与 reviewed_at。
