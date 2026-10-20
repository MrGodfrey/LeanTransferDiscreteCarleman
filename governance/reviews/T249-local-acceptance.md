# T249 / C265 独立本机验收

- checked_sha: `c159999f8e61e66bab2d2a7023bc23eb5aa64d0b`
- mathematical_base: `c8fb6d0a150570c2a62ab9cc761d0f482af5aa6a`
- reviewed_at: `2026-10-20T09:30:30+00:00`
- reviewer: 独立本机 Agent `accept_spatial_lemma`
- result: **PASS，11/11 显式声明（10 定理、1 定义），未发现缺陷。**
- axiom_check: **PASS**
- accepted_scope: **AUXILIARY；真实全空间加权 Hessian 积分恒等式、原通量的精确坐标展开及梯度质量恒等式。保持 18/26，P023 不提升。**

已完整读取固定 `Carleman/Spatial/WeightedHessianIdentity.lean`、11 项 raw 完整类型和公理记录、analysis/MATH_SPEC/台账，对照原稿 `paper/main.tex:2659–2665`。原 Corollary A.2 要求整个 Dirichlet 正则性与统一椭圆估计；本批完成经典积分代数，尚未选择实际水平截断或通过极限得到该原估计。

## 实际数学及假设核对

1. **实际 Euclidean volume 和可积性。** 所有积分使用 `SpatialCoordinates d=EuclideanSpace ℝ (Fin d)` 的全空间 Lebesgue volume，不是抽象配对或替换测度。C∞ 紧支 f 与任意 C∞ g 的乘积连续且紧支，实际 `integrable_of_hasCompactSupport` 供应 L¹ 资格。f 的每个实际方向导数仍连续、紧支，故 `(D_e f)g`、`f(D_e g)`、fg 三项分别可积。调用 mathlib 全空间分部积分时也明确供应 f/g 在所需支持上的实际可微性；没有省略第三个 fg 可积条件。
2. **两次分部积分保留全部截断导数项。** 置 A=ηD_e f、B=ηD_v f，两者均真实 C∞ 紧支。先合法拆开 `∫A D_vg−∫B D_eg`，分别分部积分为 `−∫D_vA·g+∫D_eB·g`。实际乘积法则产生四项，其中 ηD_vD_e f 与 ηD_eD_v f 由真实二阶微分对称性消去，剩下
   `∫(D_eη D_vf−D_vη D_ef)g`。
   `smoothD_comm` 已直接核对：它把两个真实方向导数识别为原 CLM 二阶导数，再调用 C∞ 所给的实际对称性。各次 `integral_sub/add` 所用 A、B、D_vA、D_eB 乘积均有独立紧支可积证明。
3. **Hessian 配对的负号准确。** 在上一式取 f=D_vu、g=D_eu，原左侧是 `∫η(u_ev u_ve−u_vv u_ee)`。真实混合导数交换使其等于所需 `∫η(u_ee u_vv−u_ev²)` 的负数，因而右端准确为
   `−∫[(D_eη)(D_eu)(D_v²u)−(D_vη)(D_eu)(D_eD_vu)]`。
   没有删除 η 导数项或漏掉外层负号；u 不需要紧支或任何边界零值。
4. **全有序 Hessian 平方和及求和合法性。** `smoothHessianSq` 的定义是 `Σ_i Σ_j (D_iD_j u)²`，包含全部有序坐标对；不是只对 i≤j 求和，也不是未经系数核对的 Sym 商指标范数。`(Δu)²` 展开为全部 `Σ_iΣ_j u_ii u_jj`，逐项减去同一完整 Hessian 平方和。证明对每个左端 L_ij 给 η 乘光滑函数的可积性，对每个右端 R_ij 的两个项给 D_iη 或 D_jη 乘光滑函数的可积性，再作有限双和的积分交换和合并。不存在依靠非可积函数的总积分默认值使恒等式偶然成立的问题。
5. **通量严格等于已定义的原表达式。** 使用 T248 的实际
   `F(u,g)=Δu⟨∇u,∇g⟩−D²u[∇u,∇g]`。
   原梯度向量的真实基展开给第一项 `Σ_iΣ_j u_i g_i u_jj`；对二阶 CLM 的两个参数分别展开，显式交换有限求和次序并用实际方向求值导数身份，给第二项 `Σ_iΣ_j u_i g_j u_ij`。外层方向 i、内层求值 j 与原通量保持一致，不把 Hessian 的两个参数误配，也没有另定义一个为恒等式量身构造的 flux。该坐标展开只需 u 光滑，g 通过实际 `fderiv` 与其坐标向量参与代数。
6. **真实 Dη=−κDg 的代入和任意 κ。** 输入是所有 x 的真实连续线性泛函等式，不是候选梯度或已假设的积分等式。逐坐标代入 R_ij 后，原外层负号与 −κ 正确合并，得到
   `∫η[(Δu)²−HessSq(u)] = ∫κF(u,g)`。
   此 helper 的实际类型不另外要求 g 光滑或 κ 可测/有界；这不造成漏洞：整个 κF 逐点等于已证明可积的 `−Σ_ij R_ij`，所以整个积分函数的可测性和可积性随该身份成立。不能据此单独宣称 κ 或 F 可积，也没有在证明中非法拆出 κ 的积分。所有经典光滑 g 的预期应用包含在该更一般 helper 中。
7. **质量恒等式同样保留正负号。** 对明确 C∞ 的 g，逐坐标真实分部积分得到
   `∫ηΔg = −∫Σ_i(D_iη)(D_ig)`。
   每项 ηD_i²g 和 (D_iη)D_ig 都有真实紧支乘积可积性，有限和交换合法。再代入同一个实际 Dη=−κDg，使用原欧氏梯度的完整平方范数坐标和，得
   `∫κ‖∇g‖² = ∫ηΔg`。
   κ‖∇g‖² 整体逐点等于可积的负坐标和；κ 本身仍无额外资格假设。没有表面积、coarea 或未证散度定理输入。
8. **经典范围与待证步骤保留。** η 全局 C∞ 紧支；在 Hessian 主恒等式中 u 全局 C∞，在 Laplacian/质量恒等式中 g 全局 C∞。η、κ 不要求非负，u/g 不要求紧支、PDE 或零边界值；本批只是等式，不从 T248 的边界点通量非负擅自推断全空间或边界层积分非负。真实 η/κ 的构造及链式身份尚是下游义务。未给一般 H² 类指定经典边界值，未证明保持边界的强密度、边界层极限、统一估计或原多面体穷竭。

全坐标和在 d=0 仍有准确的空和意义，等式退化为 0=0；没有除以维数、梯度或 κ。所有积分等式对所列任意数据成立，没有隐含小参数条件或额外正性。`smoothHessianSq` 的 C∞ 仅由实际二阶导数有限平方和得到，不额外声称原弱 Hessian 范数已与之识别。

## 全部声明逐项结论

名称统一带前缀 `Carleman.`；源码行为固定 `WeightedHessianIdentity.lean`，raw 行为固定完整类型的位置。

| 源码 / raw 行 | 声明 | 结论 |
|---|---|---|
| 13 / 43778 | `compact_smooth_product_integrable` | PASS；真实连续紧支乘积的全空间 L¹。 |
| 18 / 43782 | `integral_smoothD_compact` | PASS；三项可积资格齐备的实际分部积分。 |
| 28 / 43787 | `weighted_mixed_derivative_pair` | PASS；两次分部积分、全部 η 导数项及真实混合交换。 |
| 59 / 43794 | `weighted_hessian_pair` | PASS；原 Hessian 配对与正确外层负号。 |
| 80 / 43804 | `smoothHessianSq` | PASS（定义）；完整有序坐标 Hessian 平方和。 |
| 84 / 43806 | `smoothHessianSq_contDiff` | PASS；实际二阶导数平方和的 C∞。 |
| 89 / 43809 | `levelBoundaryFlux_eq_double_sum` | PASS；原 T248 通量的准确双坐标展开。 |
| 126 / 43823 | `weighted_hessian_identity` | PASS；完整平方差与所有权导数项，有限双和可积拆合。 |
| 185 / 43838 | `weighted_level_hessian_identity` | PASS；真实链式输入给 ∫κF，整个函数经精确改写可积。 |
| 204 / 43844 | `weighted_laplacian_identity` | PASS；实际 Laplacian 的逐坐标分部积分。 |
| 230 / 43852 | `weighted_level_gradient_mass` | PASS；实际梯度完整平方范数及准确质量等式。 |

## 固定依赖与本地证据

实际 Carleman 导入闭包 **224 文件**，其中 **223 旧文件**相对 mathematical_base 逐 Git blob 不变，唯一新增数学模块为本批模块。已直接完整读取 `ConvexBoundaryFlux`、`SmoothDirectionalCalculus`，核对原通量定义、真实梯度/坐标展开及混合微分；读取 `WeakDerivativeStrongLimit` 的相关导入和实际积分接口，进一步核对 mathlib `LineDeriv.IntegrationByParts` 的全空间 Fréchet 分部积分定理及三项可积前提。没有把旧的弱极限接口当作本批未证明的逼近结论。

T248 冻结报告全文读取并核对单文件提交 `4b94173ca3a213557219fef2cb2c0e28743e89eb`，checked_sha 为本报告 base、reviewed_at=`2026-10-20T09:24:48+00:00`，14/14 PASS；当前固定 proof 中报告逐字节相同。其真实通量的点态符号结论没有代替本批积分、可积性或以后边界层极限的证明。

Lean **4.35.0**，编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib lock 与实际无修改 checkout 同为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。根导入和 11 项 `#check`/`#print axioms` 齐全，清单精确匹配源码、T249/C265 台账和 raw。AGENTS、PROJECT_OPERATIONS、state/README 与此前已读协议摘要一致。

- `/tmp/carleman-t249-local-evidence.json`：source=local、PASS，checked/source 均为本报告 proof，finished_at=`2026-10-20T09:27:26.292187+00:00`；实际 `lake build Carleman` 和 `lake env lean tools/CheckAxioms.lean` 记录均 exit 0。
- `/tmp/carleman-t249-local-source-manifest.txt`：**1046 项、113535 bytes**，SHA256 `ce449f4cd10ca9641bb260ac99a3ec63a3c39f4514b4427b757e77e68a23a28e`。独立枚举固定提交全部 tracked `.lean` 及三个工具链配置，路径集合、唯一性及逐项 SHA256 全部匹配固定 Git blob。
- `/tmp/carleman-t249-target-build.log`：**3409 jobs** 成功，112 bytes，SHA256 `a959b01d97eaa9734810c79579f83db2f163ea4e3929c7608db1d8eba970d9cd`。`/tmp/carleman-t249-build.log`：**4288 jobs** 成功，80 bytes，SHA256 `e85493281e89438bd4d77500d5c42d39ebe3842d291c7e5cfea4dc9f9657299f`。`/tmp/carleman-t249-axioms.log` 为 0 bytes。
- `/tmp/carleman-t249-weighted-hessian-identity-local-axioms.txt`：**3368861 bytes**，SHA256 `2bc4ab597da4f9e173390379bc72cf542b25274c5e0bc01c78fc8f4c44cb3230`。11 项完整类型及公理逐项核对；全文件 4004 个公理列表均仅含 `propext`、`Classical.choice`、`Quot.sound`，另有 10 个无公理记录。实际尾部确认 **10031 声明递归审计 PASS**；全命名空间 `privateToUserName`/`collectAxioms` 白名单逻辑相对 base 不变，无 sorryAx 或额外数学公理。
- 原稿相对 base 不变，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本次核对固定本地执行证据，没有重跑全库，没有查询远端 CI/看板，也没有将本地成功称为 CI 成功。

无修复项。接受本批 **AUXILIARY 真实加权 Hessian/通量及梯度质量积分恒等式**，保持 18/26。正文与 reviewed_at 冻结后仅单文件提交本报告，不修改数学、台账、原稿、根导入、公理工具或其他报告，不 push。
