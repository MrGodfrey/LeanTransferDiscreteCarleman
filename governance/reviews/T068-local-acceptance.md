# T068 / C084 独立本机验收

- `checked_sha`: `3eeba97f7b274bd8ffd473d2f57aad2b4e722845`
- `base_commit`: `604328efce1cc28e4d6fe6cadcdaa039ee0e76a3`
- `reviewed_at`: `2026-10-18T22:11:48+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：m=1真实弱负Laplacian乘积公式、实际H¹₀乘积资格及原完整Dirichlet form-operator域的允许权保持。统一交换子估计、H²椭圆正则性及完整Appendix A尚待，原文完整结果计数保持 **12/26**。

按任务要求先用git rev-parse HEAD核实完整SHA，随后从该提交导出固定快照。独立读取三新模块全部证明、10项实际展开类型、相关定义及调用依赖，对照原 `paper/main.tex` A2与Appendix A。执行者说明与CI均未代替数学验收，后续工作区增量不属本报告。

## 全部10项声明

完整名称均以前缀 `Carleman.` 开始；顺序与交付JSON完全一致。固定位置均在 `Carleman/Spatial/` 下。

| # | 声明（省略 Carleman.） | 固定位置 | 独立数学核对 |
|---|---|---|---|
| 1 | `weakGradientPairing_coordinates` | `WeakProductComponents.lean:16` | PASS；实际一阶Euclidean字段的L²内积展开为所有Fin d坐标内积，Sym.oneEquiv确保每个分量恰计一次。 |
| 2 | `weakFirstProduct_component` | `WeakProductComponents.lean:22` | PASS；实际乘积弱jet的每个坐标为w D_i u+(D_iw)u，明确保留系数与真实fderiv的a.e.联系。 |
| 3 | `weak_product_coordinate_test` | `WeakProductComponents.lean:36` | PASS；对任意原SpatialTest调用完整弱乘积法则，分部积分负号准确，未要求状态二阶导数。 |
| 4 | `weakGradientPairing_product_test` | `WeakLaplacianProduct.lean:14` | PASS；逐坐标乘积测试给pair(∇(wu),∇φ)=pair(∇u,∇(wφ))−Σ〈2D_iw D_iu+D_i²w u,φ〉。 |
| 5 | `IsWeakNegativeLaplacian.mul` | `WeakLaplacianProduct.lean:37` | PASS；对全部SpatialTest得到实际−Δ(wu)=w f−Σ(2D_iw D_iu+D_i²w u)，f为原弱负Laplacian。 |
| 6 | `smoothLaplacianCorrection` | `DirichletOperatorProduct.lean:14` | PASS；实际wordDerivative [i]和[i,i]对应真实一阶／同方向二阶导数，有限L²和定义修正项，无自由占位系数。 |
| 7 | `boundedSmooth_weakLaplacian_product` | `DirichletOperatorProduct.lean:22` | PASS；内部构造上述真实导数乘子，同一个乘积jet同时具有精确value、真实H¹₀闭包资格与完整弱负Laplacian身份。 |
| 8 | `boundedSmooth_dirichlet_operator_product` | `DirichletOperatorProduct.lean:44` | PASS；原完整图刻画把乘积弱身份转为真实原算子域成员及精确算子等式，不假设H²。 |
| 9 | `boundedSmooth_map_mem_dirichlet_domain` | `DirichletOperatorProduct.lean:56` | PASS；从任意原域z经图刻画取得H¹₀ jet和Az，再乘积并返回同一域，覆盖全部原域。 |
| 10 | `allowed_weight_mem_dirichlet_domain` | `DirichletOperatorProduct.lean:69` | PASS；原内禀SmoothOnClosure及有界开域内部供应允许权的真实BoundedSmoothOn，所有TimeWeight、τ、t及η=±1均适用。 |

## 全坐标与真实弱测试

weakGradientPairing的定义就是两个实际一阶L² Euclidean字段的内积。所用firstDerivativeField_inner先以L²内积的真实积分定义展开有限分量和，再通过Sym.oneEquiv在Sym(Fin d) 1与Fin d之间换指标。每个坐标出现一次，没有把CLM算子范数替代Euclidean字段，也没有加入额外维数倍数。

weakFirstProduct由零阶实际乘法及一阶字段w∇u+firstGradientAssembly((D_iw)u)构造。assembly的实际坐标投影逐一恢复给定L²分量，其弱导数资格对每个i由原IsWeakSpatialDerivative.mul证明。新坐标引理展开的正是这个已具有完整弱测试身份的jet；dw并非任意字段，因为hdw明确要求其value a.e.等于实际fderiv(w.value)在第i个真实正交基向量上的值。

原SpatialTest是全空间C∞、紧支且支集包含于S的真实函数；没有限制为有限测试集、节点函数或某个选择出的稠密子集。已直接复核mulOn：w仅在开S内光滑也足够使wφ全空间光滑，因为S外每点附近φ恒为零；乘积支集仍包含于φ原紧支。其实际L²值及实际导数均由逐点乘积法则与a.e.类身份识别。因此测试wφ和(D_iw)φ都合法，不要求在域外对w作光滑延拓。

弱乘积法则使用原弱身份测试wφ，导数展开后给〈wu,D_iφ〉=−〈wD_iu+(D_iw)u,φ〉。第3条新声明直接对任意φ调用这一身份。第4条再以dw_i作为乘子应用一次，故要求dw_i本身在S光滑，以及ddw_i a.e.等于其实际同方向导数；这些联系在实际类型中全部保留。

## 负号、系数2与完整弱负Laplacian

记u_i=D_i u、w_i=D_iw、w_ii=D_i²w。逐坐标独立重算有

\[
\langle D_i(wu),D_i\phi\rangle
=\langle wu_i,D_i\phi\rangle+\langle w_i u,D_i\phi\rangle,
\]
\[
\langle u_i,D_i(w\phi)\rangle
=\langle wu_i,D_i\phi\rangle+\langle w_i u_i,\phi\rangle,
\qquad
\langle w_i u,D_i\phi\rangle
=-\langle w_i u_i+w_{ii}u,\phi\rangle.
\]

所以差恰为−〈2w_i u_i+w_ii u,φ〉。代码的inner_map_left、测试乘积导数及弱乘积身份逐项实现这三行，系数2来自两个真实一阶交叉项；没有把Δ与−Δ的符号混用。

IsWeakNegativeLaplacian u f定义为对全部φ∈SpatialTest(S)，〈∇u,∇φ〉=〈f,φ〉。应用原身份到合法测试wφ，再把真实乘子移到f侧，得到

\[
-\Delta(wu)=w f-\sum_{i=1}^{d}\bigl(2(D_iw)(D_iu)+(D_i^2w)u\bigr).
\]

右侧是实际L²元素：u、全部D_i u及f均在原L²，w、dw_i、ddw_i是已证明有界的实际乘子，有限和保持L²。无额外可积性前提，也未借不可积积分的默认值构造身份。通用引理不要求w正或可逆；允许权的正性在最后实例化中来自真实q^τ和指数函数。

## 真实wordDerivative与同一个H¹₀乘积jet

smoothLaplacianCorrection的系数由intrinsicWordMultiplier构造，value就是实际wordDerivative。wordDerivative由实际迭代Fréchet导数在真实坐标基上的取值定义；wordDerivative_cons在S内用ContDiffAt识别为外层方向的实际fderiv。因此空词[]给w，[i]给D_iw，[i,i]给D_i(D_iw)，没有不受约束的导数标签或二阶方向求和错误。

BoundedSmoothOn断言S内实际C∞以及每个有限阶的实际全Fréchet导数有界。intrinsicWordMultiplier从这些全导数界推出坐标词导数界，并在支持于S的真实限制测度上取得可测性和有界性；导数识别也是在S上的a.e.身份，不在边界或域外任意代表上强行求导。

第7条明确选p=weakFirstProduct，而非分别选择具有良好边界和良好方程的两个不同乘积。已复核所用H¹₀保持证明：weakFirstProductCLM在真实H¹图拓扑连续，且把每个原紧支光滑测试jet准确送到合法乘积测试的jet；闭包映射定理遂把原测试线性空间的H¹闭包送回自身。于是同一个p既有value(p)=w.map(value(u))，又属于dirichletJetSpace，并满足上述完整弱负Laplacian公式。没有从边界a.e.零值猜测H¹₀资格，也没有要求u有逐点边界代表。

## 原完整form-operator域

boundedDirichletOriginalForm的能量空间是真实H¹₀闭包的Hilbert实现，形式为原L²梯度内积。其有界性、对称性和由有界域Poincare推出的强制性已证明。原model.domain由完整变分条件构造：存在H¹₀能量代表v和f∈L²，使对全部能量测试z有a(v,z)=〈f,z〉；model.operator取这个由稠密性唯一决定的f。它未定义成H²∩H¹₀，也未通过有限维、谱截断或事先正则的核心限制域。

已直接复核dirichlet_operator_graph_iff的两个方向。原算子域成员先经完整operator_isAssociated转成真实H¹₀ jet和全部光滑测试身份；反向从全部SpatialTest弱身份出发，利用两侧对H¹图拓扑连续，把等式延拓到原测试span的整个闭包，即全部H¹₀测试，随后用原变分域定义产生同一model.domain成员及指定的算子值。虽然该依赖文件导入了另一个H²桥，实际图刻画的类型和证明不需要H²状态或椭圆正则性。

第8条把新乘积p及实际L²右侧送入这个双向图刻画，得到z∈原D(A)、z=wu和Az=w f−correction。第9条对任意原域z，先以f=Az调用正向图刻画，再用乘积结论和反向图刻画恢复wz∈同一原域。没有将待证域保持本身作为输入。因而实际原Dirichlet算子的乘积公式及域保持覆盖全D(A)，不仅是已知H²成员。

## 原SmoothOnClosure和全允许权族

SmoothOnClosure要求profile在closure S连续、在开S内C∞，且每阶实际Fréchet导数在closure S有连续延拓。这是项目已验证的原内禀闭包光滑接口。有限维有界域的紧闭包给各阶延拓的有限界，从而得到域内BoundedSmoothOn；不要求存在更大的光滑开邻域，不调用未经证明的Whitney扩张，也不把闭集上的任意ContDiffOn替代该接口。

allowed_multiplier_boundedSmooth实际处理q(t)^τ exp(ηq(t)ρ)。q(t)≥1，任意实τ、任意t和|η|=1保证函数有定义且光滑；原profile导数界通过真实指数链式法则给每个固定权参数的有限导数上界。SpatialProfile的实际乘子value与这个表达式逐点一致。最终定理对全部TimeWeight、τ、t、η及原域状态z量化；同时取(−τ,−η)就得到原σ⁻¹的保持性，故原有限允许指数族和两种符号均包含在结论中。

本批只证明固定乘子的域保持和精确算子乘积身份。BoundedSmoothOn中的绝对界可以依赖q、τ；没有把它写成统一于全部权参数的交换子常数。原A2还要求对[A,σ]σ⁻¹的统一相对导数估计，这仍需另行组装，不能由本次定理名称推定完成。d>0与原d≥1一致；弱配对引理允许d=0时空坐标和，而原算子入口明确保留正维数。有界开空域也不引入非法选点或除法。

## 固定依赖、构建与公理

三模块Carleman导入闭包共79模块，其中76旧模块与base完全不变，新增恰为本批三模块。另核对关键依赖闭包与各自已验收版本：C030 IntrinsicMultipliers的36模块对 `bed432f9ab0eebd8a31163608ff72c422299e93d`、C057 DirichletDistribution的57模块及GradientPairing的50模块对 `3d5aa9cec281974bef7da9d37ffa11a8f9f75670`、C083 DirichletAllowedWeight的51模块对 `604328efce1cc28e4d6fe6cadcdaa039ee0e76a3`，全部无变化。实际关键定义、乘积测试、H¹₀闭包、原变分域和内禀导数证明已直接读取。

原稿、已读取治理协议、工具链pin和CI工作流保持一致。原稿SHA256为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean为4.35.0，本机mathlib实际HEAD为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且工作树干净。root显式导入三新模块，CheckAxioms含全部10项的完整 `#check @...` 和 `#print axioms ...`。

10项实际展开类型逐一核对，每项只依赖 `propext`、`Classical.choice`、`Quot.sound`。固定本地全部1452条显式公理记录也无其他公理，无sorryAx。检查器通过privateToUserName遍历所有Carleman声明并递归collectAxioms，而非只检查本批公开入口。

`/tmp/carleman-dirichlet-operator-full.log` 实际包含 `Build completed successfully (3668 jobs).` 和 `Axiom audit passed for all 5099 Carleman declarations.`。固定 `/tmp/carleman-dirichlet-operator-local-axioms.txt` 为 **1,501,454 bytes**，SHA256 **`091f8fdaa9d703d6802d8e6238e6366b98740d03092b352efb7005dd40e6c493`**。

已独立通过GitHub connector读取 [main CI 39170881156 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39170881156/attempts/1)：main/push，head SHA精确匹配固定版本，run为completed/success。state-check（117803472291）、lean（117803472471）、dashboard / snapshot（117804107128）三项jobs均completed/success，实际工具链准备、构建、checked source记录、两份证据上传及同次快照步骤均success。同run的lean-ci-result artifact（12152775544）和lean-declaration-evidence artifact（12152646022）均绑定固定SHA。

已实际读取 `/tmp/carleman-dirichlet-operator-main-ci/result.json`：status PASS，`checked_sha=source_head_sha=3eeba97f7b274bd8ffd473d2f57aad2b4e722845`，targets为Carleman，`finished_at=2026-10-18T22:09:51.647460+00:00`，ci_url与上述run/attempt一致。实际Lean 4.35.0提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib为上述pin。

原始远端 `/tmp/carleman-dirichlet-operator-main-axioms/axioms.txt` 与固定本机副本已独立逐字节比较，完全相同：**1,501,454 bytes**，SHA256 **`091f8fdaa9d703d6802d8e6238e6366b98740d03092b352efb7005dd40e6c493`**。另逐名复核远端10/10完整展开类型及各自正常基础公理集合，1452条显式公理记录没有其他公理；末行实际为 **`Axiom audit passed for all 5099 Carleman declarations.`**。无sorryAx，未混用其他SHA或后续工作区产物。

## 验收决定

**C084：PASS，可升级为REVIEWED，scope保持AUXILIARY。** 固定10项未发现负号、系数、坐标、测试范围、边界资格、原算子域、真实导数或允许权范围方面需要修复的缺陷；实际展开类型、递归公理及同SHA正式main CI均已独立核实。

本批完成m=1真实Dirichlet域保持及精确乘积公式；统一交换子估计、H²正则性、一般H² N3、完整Appendix A及完整P1命题仍待，原文保持12/26。本次仅写本报告，没有修改数学代码、台账、原稿或root导入，没有commit/push。
