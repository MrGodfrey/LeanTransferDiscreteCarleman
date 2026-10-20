# T247 / C263 独立本机验收

- checked_sha: `e84f958461360997f4705a75d4eaa6d3c77d2b21`
- mathematical_base: `ebc85ddad04c9b4008fa5b3e89a05696eff19bfb`
- reviewed_at: `2026-10-20T09:17:52+00:00`
- reviewer: 独立本机 Agent `accept_spatial_lemma`
- result: **PASS，11/11 定理，未发现缺陷。**
- axiom_check: **PASS**
- accepted_scope: **AUXILIARY；经典光滑零边值的真实法向梯度比例、全部切向方向的 Hessian 二次型比例，以及原指数和的实际 Hessian 非负性。保持 18/26，P023 不提升。**

已完整读取固定 `Carleman/Geometry/LevelBoundaryHessian.lean`、11 项 raw 完整类型及公理、analysis/MATH_SPEC/台账，对照原稿 `paper/main.tex:2659–2665`。本批服务原 Corollary A.2 的凸域正则性证明，给经典边界几何身份；不把经典函数的边界点值替换成一般 H² 状态尚未证明的迹，也不声称原完整正则性或统一估计。

## 实际数学及假设核对

1. **Hessian 是原函数的真实二阶导数。** `smooth_directional_fderiv_eq` 对固定 v 的导数求值函数实际应用 `fderiv_clm_apply`，给
   `D[y↦Df(y)v](x)w = D(Df)(x)w v`。
   外层方向 w 和内层求值 v 的顺序保持准确；没有靠交换两方向来掩盖导数顺序，也没有自行定义一个候选 Hessian 当作导数。
2. **二次复合消项由实际微分推导。** 对全局 C∞ h/G、G(c)=c、DG(c)v=v、Dh(c)=0 及 h∘G 在 c 邻域恒值，先用邻域相等的导数局部相等得到 `Dh(Gx)(DG(x)v)=0`。再对这个实际 CLM 求值乘积求导：`fderiv_clm_apply` 的两项是 Dh(Gc) 作用于 D[DG(·)v](c)v，以及 D[Dh∘G](c)v 作用于 DG(c)v。前者因已知 Dh(c)=0 消失；后者经真实链式、G(c)=c 和 DG(c)v=v 化为 D²h(c)[v,v]。左侧局部恒零给该值等于 0。相关可微性均由 h/G 的 C∞ 实际导数和复合供应，未把二阶链式或目标 Hessian 身份作为输入。
3. **一阶图恒值身份使用原坐标映射。** G(x)=x+(ψ(x)−x_r)e_r，ψ(c)=c_r 给 G(c)=c；实际 DG 的完整坐标修正项给
   `Df(c)v+(Dψ(c)v−v_r)D_rf(c)=0`。
   局部恒值是在 c 的真实邻域而不是仅在 c 上；后续求导因此合法。这里是图投影，不要求它可逆，也没有误用可逆 shear 的导数。
4. **法向比例在所有方向成立。** 对 g∘G 恒 a、u∘G 恒 0 分别应用上一身份，消去同一个 `(Dψ(c)v−v_r)`。非零原 D_rg(c) 保证除法合法，得到整个实际连续线性泛函
   `Du(c)=q·Dg(c)`，`q=D_ru(c)/D_rg(c)`。
   这不是只在基向量或某个切向方向上的等式。在欧氏识别下即梯度比例；声明没有把 Dg 归一化为单位法向，也没有对 q 预设正负。
5. **切向 Hessian 比例使用同一固定 q。** q 是在给定 c 处算出的标量，h=u−qg 的两次微分中 q 都是常数；没有错误地忽略一个随 x 变化的商的导数。上一比例先给 Dh(c)=0。对真实切向条件 Dg(c)v=0，图恒值的一阶身份及 D_rg(c)≠0 给 Dψ(c)v=v_r，从而 DG(c)v=v。h∘G 在原邻域恒为 −qa；应用第 2 项并用实际二阶线性规则得到
   `D²u(c)[v,v]=q D²g(c)[v,v]`。
   最终 q 在所有 v 之前选择，同一个 q 同时满足完整梯度及全部切向二次型身份。结论写的是每个切向 v 的对角二次型，没有额外宣称已单列证明混合切向双线性公式或曲率通量。
6. **一般正则水平 helper 明示较强边值输入。** 一般 g 版本要求全局解析 g、Dg(c)≠0、全局 C∞ u，以及 u 在整个水平 `g=g(c)` 为零。T244 内部给实际 C∞ 图、非零方向导数、含 c 的开邻域和真实图点身份；据此构造两条真正的邻域恒值身份，而不是假设图复合导数为零。解析 g 降为 C∞ 合法；raw 的外层 `⊤`（ω）和 `↑⊤`（C∞）已区分。一般 helper 的 whole-level 条件被明确保留，随后具体应用确实内部清偿。
7. **整个原水平 1/2 都是真实 frontier。** 设原指数和 gₙ(z)<1/2、gₙ(c)=1/2。对 openSegment(z,c) 中任意 y=αz+βc，α、β>0 且 α+β=1，原凸性给
   `gₙ(y)≤αgₙ(z)+β/2<1/2`。
   严格性来自 α(1/2−gₙ(z))>0，故整个开线段位于原内域。实际闭线段包含在开线段闭包中的定理把端点 c 放进原内域闭包；gₙ(c)=1/2 排除内域本身，原内域开放遂给真正 frontier 成员资格。没有借“非零梯度”直接假设 frontier=level，也没有漏掉远处水平点。
8. **最终只要求原 frontier 零值。** 对给定实际 frontier 点 c，已验收的原边界正则性供应 gₙ(c)=1/2 与 Dgₙ(c)≠0。任意 x 满足 gₙ(x)=gₙ(c) 时，第 7 项将 x 送入原 frontier，所以最终给定的 `∀x∈frontier, u(x)=0` 足以供应一般 helper 的 whole-level 条件。没有给最终声明额外增加整个水平集的独立零值前提，也没有把近边界的一个水平分支当作全部水平集。
9. **原指数和的真正二阶非负性。** 令 k=n+1。一阶实际导数沿 v 为 `∑ exp(k(b_i−ℓ_i x))(−kℓ_i v)`。对各项真实指数函数再次求导，第二个负因子与第一个相乘，得到
   `D²gₙ(x)[v,v]=∑ exp(k(b_i−ℓ_i x))(kℓ_i v)²`。
   有限求和、方向导数与 CLM-valued Hessian 的桥接全部显式；系数是 k²，没有漏掉 n+1 或误改符号。每项由指数正、平方非负给总和非负，适用于全部 x、v，无 PDE、内点或边界假设。它仅证明 gₙ 的 Hessian 非负；由于 q 未指定符号，本批没有错误推断 u 的切向 Hessian 也非负。

一般图 helper 的正则性及局部恒值条件明确；具体指数和应用内部供应图、原水平和非退化资格。最终 u 仍是全空间经典 C∞ 函数，边值是原 frontier 上的真实点值，而非 L²/H² 类的任意代表。没有 PDE 输入、积分可积性或能量预算声称；空指标及零维的 Hessian 平方和仍合法，不能满足相应内点加边界条件的情形不产生虚构非零法向。经典通量代数、Green 积分、保持边界的 H² 强密度、统一估计和穷竭仍需后续工作。

## 全部声明逐项结论

名称统一带前缀 `Carleman.`；源码行为固定 `LevelBoundaryHessian.lean`，raw 行为固定完整类型的位置。

| 源码 / raw 行 | 声明 | 结论 |
|---|---|---|
| 15 / 43607 | `smooth_directional_fderiv_eq` | PASS；真实方向求值导数与正确次序的 CLM 二阶导数。 |
| 23 / 43612 | `second_fderiv_comp_zero_of_tangent` | PASS；实际二次链式与 Dh(c)=0 消项。 |
| 45 / 43621 | `coordinateLevelMap_const_composition_derivative` | PASS；原图投影恒值的完整一阶身份。 |
| 58 / 43634 | `level_graph_gradient_multiple` | PASS；非零原方向导数合法消元给整个梯度泛函比例。 |
| 77 / 43649 | `second_fderiv_sub_smul` | PASS；固定标量的真实二阶线性规则。 |
| 91 / 43656 | `level_graph_tangent_hessian_multiple` | PASS；同一 q 及真实切向条件给二次型比例。 |
| 130 / 43673 | `regular_level_zero_gradient_hessian` | PASS；图资格内部构造，whole-level 零值在 helper 中明示。 |
| 147 / 43684 | `halfspaceSmoothInner_frontier_of_level` | PASS；原凸性、真实严格开线段和闭包给整个水平的 frontier 资格。 |
| 165 / 43690 | `halfspaceSmoothInner_zero_gradient_hessian` | PASS；仅原 frontier 零值内部清偿 whole-level 条件。 |
| 178 / 43705 | `halfspaceExpSum_second_directional` | PASS；原指数和实际 Hessian 的准确 k² 平方和。 |
| 202 / 43710 | `halfspaceExpSum_hessian_nonneg` | PASS；所有 x/v 的真实 Hessian 非负性。 |

## 固定依赖与本地证据

实际 Carleman 导入闭包 **218 文件**，其中 **217 旧文件**相对 base 的 Git blob 不变；唯一新增数学模块为本批模块。本次重读实际 `SmoothGraphHeightExtension` 的最终图构造与资格、`HalfspaceSmoothExhaustion` 的原指数定义/凸性/一阶导数/边界正则性，以及导入的 `SmoothLaplacianProduct`。mathlib 的 `fderiv_clm_apply`、邻域相等的实际导数规则和 `segment_subset_closure_openSegment` 已直接读取。

T244 冻结报告 `716031127e9645f4476e104ec26dd92d6c51f4bd` 与当前固定 proof 中内容相同，reviewed_at=`2026-10-20T08:48:04+00:00`、9/9 PASS；其已验收 proof `31c84b810ce9f75a97bc2fc5a5cae481a9252183` 的 **214 文件**闭包独立逐 blob 核对不变。接续阶段 T246 的一般 H² 成员结论没有被当作本批 u 的光滑性、边界点值或强密度证明。

Lean **4.35.0**，编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib lock 与实际无修改 checkout 同为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。根导入和 11 项 `#check`/`#print axioms` 齐全，清单精确匹配源码、T247/C263 台账和 raw。AGENTS、PROJECT_OPERATIONS、state/README 与此前已读协议摘要一致。

- `/tmp/carleman-t247-local-evidence.json`：source=local、PASS，checked/source 均为本报告 proof，finished_at=`2026-10-20T09:10:51.917821+00:00`；实际 `lake build Carleman` 和 `lake env lean tools/CheckAxioms.lean` 记录均 exit 0。
- `/tmp/carleman-t247-local-source-manifest.txt`：**1044 项、113317 bytes**，SHA256 `9ec62bcb915e2f8a1d5d6675e8df8b5d438aaad65c6ebf713deb3ef5322e448a`。独立枚举固定提交全部 tracked `.lean` 及三个工具链配置，路径集合、唯一性及逐项 SHA256 全部匹配固定 Git blob。
- `/tmp/carleman-t247-target-build.log`：**3403 jobs** 成功，110 bytes，SHA256 `f164fe8e10f743c52781381584b41ad22405dbbf6fdc06c64c0f36847ae827e4`。`/tmp/carleman-t247-build.log`：**4286 jobs** 成功，80 bytes，SHA256 `c3d6c11344b8aa095d36fae8f6835871de9c7ad9634a94bfa39a571718212b54`。`/tmp/carleman-t247-axioms.log` 为 0 bytes。
- `/tmp/carleman-t247-level-boundary-hessian-local-axioms.txt`：**3356771 bytes**，SHA256 `8f61b8b9c650097342af3bbc3bc35614c3a2d572b11a882b72d3bb4caeff4474`。11 项完整类型及公理逐项核对；全文件 3979 个公理列表均仅含 `propext`、`Classical.choice`、`Quot.sound`，另有 10 个无公理记录。实际尾部确认 **10000 声明递归审计 PASS**；全命名空间 `privateToUserName`/`collectAxioms` 白名单逻辑相对 base 不变，无 sorryAx 或额外数学公理。
- 原稿相对 base 不变，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本次核对固定本地执行证据，没有重跑全库，没有查询远端 CI/看板，也没有将本地成功称为 CI 成功。

无修复项。接受本批 **AUXILIARY 经典真实边界梯度/Hessian 身份与原指数和 Hessian 非负性**，保持 18/26。正文与 reviewed_at 冻结后仅单文件提交本报告，不修改数学、台账、原稿、根导入、公理工具或其他报告，不 push。
