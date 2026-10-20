# T254 / C270 独立本机验收

- checked_sha: `4a84f2b095e71ea776fa79ecf2d568f28270cbe1`
- mathematical_base: `032d2ae56bb04dd52015641301e4f4903fc0a1ab`
- reviewed_at: `2026-10-20T10:16:23+00:00`
- reviewer: 独立本机 Agent `accept_spatial_foundations`
- result: **PASS，28/28 显式声明（19 定理、8 定义、1 CompleteSpace instance）；未发现阻断或修复项。**
- axiom_check: **PASS**
- accepted_scope: **AUXILIARY，固定域和固定截断的真实 H²∩H¹₀ 连续换域及盒光滑逼近的截断传递；保持 18/26，P023 不提升。**

完整读取固定 `Carleman/Spatial/StrongH2CutoffTransfer.lean` 的实现、全部 raw 类型和公理，核对 analysis、MATH_SPEC、T254/C270 清单及原稿 `paper/main.tex:2659–2665`。原 Corollary A.2 要求原凸多面体/盒上 Dirichlet Laplacian 的完整解析假设；本批只清偿后续边界强逼近路线的固定截断连续性接口，不等同原命题或一般曲边域强密度。

## 数学、原对象及量词

1. **源空间与图拓扑正确。** `dirichletJetSpace` 是原域紧支 C∞ 测试的 H¹ 图闭包。`dirichletH2JetSpace` 精确取它在真实 H²→H¹ 截断下的 comap，故条件是 H²∩H¹₀，未改成 H²₀、零法向导数或点态零边界集合。截断逐字段保留原弱链，`norm_truncate_le` 在完整有限乘积规范下给界 1；闭性由该连续原像得到。`SobolevTopology` 的目标/源 H² 完备性来自全部分布配对闭等式构成的子空间，包含 0、1、2 阶真实 L² 场；不是仅零阶值的 L² 拓扑。新 CompleteSpace instance 无有限维或有界逆假设。实际 valueCLM 是零阶坐标的连续投影。
2. **泛型 lift 的假设和用途分明。** `dirichletH2LiftLinear` 明确输入实际连续标量值映射 P，以及每个源状态的目标 H² 存在性 hl。目标开放性和 restricted-volume 支撑资格使原弱导数唯一，因而任何所选合法 jet 的值决定全 jet；这真实证明选择的加法、实数乘法。图的双向等价为 `value(v)=P(u)`，不是只证明图包含于该闭集。两侧实际值映射连续，所以完整 H² 乘积中的图闭；mathlib 的 Banach 闭图定理给同一线性映射的连续性。该步骤没有给出随域、截断或内域索引变化的统一算子范数。具体截断调用中的 hl 在内部构造，没有遗留任意目标 H² lift 假设。
3. **实际值传递与零延拓边界。** `cutoffValueTransfer` 为 `M_η ∘ restriction_T ∘ restriction_S*`。已读实际 `ObservedRegionLp.restrictRegion_adjoint`：对开放 S，其伴随正是原 L² 零延拓；`subdomainZeroExtend` 则是该零延拓再取目标限制，AE 代表为 `1_S u`。因此新 map 确为 η·E₀u 在 T 的原 L² 类，不是任意替代 CLM。一般 S,T 不要求嵌套、全域有限测度或有界；η 的全局紧支光滑性内部供应实际有界乘子。零延拓的 H¹ 资格只用于原 H¹₀ 截断，未将任意 H² 状态的零延拓称为全空间 H²。
4. **目标 H² 由正确弱方程构造。** 对源 u∈H²∩H¹₀，令 v=truncate₁u、f=negativeLaplacian(u)。已读 `WeakLaplacian`：f 是实际二阶对角分量的负和，全部原测试满足 `(∇v,∇φ)=(f,φ)`。T242 的 `S∩tsupport η⊆T` 用于将源原测试闭包的截断像送入目标 H¹₀；相反方向 `T∩tsupport η⊆S` 用于把每个目标测试乘 η 后送回源域，使真实源弱方程可用。实际目标右端完整保留 `η E₀f − Σᵢ(2 Dᵢη Dᵢṽ + Dᵢᵢη ṽ)`，其中 ṽ 是真实 H¹ 零延拓再限制。没有使用未截断零延拓的跨边界 Poisson 方程。将该合法目标 H¹₀ 状态及实际 L² 右端送入 hreg 后得到 H²，且完整 H¹ 截断恰为该状态。
5. **目标正则性没有被隐藏。** `DirichletH2Regular T` 只断言每个已经给定的真实 H¹₀ 弱 Poisson 解存在同一 H² jet，不断言任意载荷可解，也不附带统一估计。泛型传递及最终泛型逼近定理明确保留该输入。四个实例则实际调用原盒正则性、上下全局图域弱正则性及原指数和 smoothInner 的局域装配正则性；均保留同一原状态的 H¹ 截断。图域所需 C∞、法向平移不变及高度/各斜率全局 Lipschitz 条件清楚在类型中；smoothInner 所需原半空间交有界及实际内点也明确。没有假设源 u 已有目标 Hessian、借用全凸域统一估计，或把这些几何资格冒充本批已自动构造。
6. **完整身份及强极限。** `cutoffH2Transfer_truncate` 以目标合法弱 jet 的值唯一性证明整个 H¹ 截断身份；随后直接从原测试闭包得到 H¹₀。`tendsto` 先将源完整 H² 强极限通过 `tendsto_subtype_rng` 放入已证闭的 H²∩H¹₀，再用同一固定 CLM 连续性；不是仅 value 收敛。AE 定理给精确 η·1_S·u。光滑身份中，原 S 上 AE 等式先用 `ae_restrict_iff'` 转成全空间条件式，再合法限制至 T；η≠0 时由 hTS 推出 x∈S，η=0 时直接消失。因此无非法将不同域的 AE 零集直接替换，也未将 AE 值当作边界点值；最终通过弱 jet 唯一性识别整个实际 `allOrderJetOn T 2`。
7. **真实 frontier 与同一逼近序列。** N={η≠0} 开，双向支撑包含给 S∩N=T∩N。所用 mathlib 恒等式正是 `frontier(S∩N)∩N=frontier S∩N`，故目标边界的每个 η 非零点确属源边界；η=0 点的乘积直接为零。无边界零测或未证迹刻画。最终定理从任意正边长原盒 H²∩H¹₀ 状态内部取得 T253 的同一全局紧支光滑 Fₙ，逐项原盒 frontier 零值、真实 H¹₀ 和完整 H² 极限全部保留。取 Uₙ=ηFₙ 后，实际光滑身份将每项等同连续传递像；真正目标 H¹₀ 及所有目标 frontier 零值分别成立。极限精确是 `cutoffH2Transfer u`，没有替换为未截断 u。结论先存在一条 U，再要求所有 n、所有边界点和完整强收敛，不按导数或测试分别选择序列。
8. **范围及退化情形。** 本批没有限制 d=2,3；泛型及盒结论包括 d=0，正阶空坐标与完整弱 jet/闭子空间论证一致；图域实例的 r:Fin d 自然限定其适用情形。S/T 开放性、双向全 tsupport 包含、目标 hreg 均在使用点明确保留；空目标的原 L²/jet 结论合法。没有声称跨域/穷竭统一常数、原曲边覆盖截断的存在、未截断状态的强逼近或弱 Miranda–Talenti 统一估计。以上后续事项仍需另外证明。

## 28 项清单及逐项结论

声明省略共同前缀 `Carleman.`；源码行指固定 `StrongH2CutoffTransfer.lean`，raw 行指固定原始公理产物中的完整类型起点。已将固定 C270 和 T254 两份清单、源码实际命名空间/种类/顺序及 raw 分别比对，完全一致。

| 源码 / raw 行 | 声明 | 结论 |
|---|---|---|
| 15 / 44220 | `WeakSobolevJet.truncateCLM` | PASS（定义）；原各阶字段截断，真实图范数界 1 给 CLM。 |
| 19 / 44224 | `dirichletH2JetSpace` | PASS（定义）；真实 H¹₀ 子空间在 H²→H¹ 截断下的 comap；没有零一阶边界要求。 |
| 23 / 44227 | `dirichletH2JetSpace_isClosed` | PASS；原 H¹ 测试闭包的连续原像，在完整 H² 中闭。 |
| 27 / 44230 | `dirichletH2JetSpace_complete` | PASS（实例）；闭子空间继承完整弱 H² Banach 完备性。 |
| 32 / 44233 | `dirichletH2ValueCLM` | PASS（定义）；子空间包含后取实际零阶 L² 字段。 |
| 36 / 44236 | `dirichletH2LiftLinear` | PASS（定义）；给定实际 P 与明确存在前提，目标开放域弱导数唯一性证明选择线性。 |
| 59 / 44241 | `dirichletH2LiftLinear_value` | PASS；选择得到的整个合法 jet 确有原 P 值。 |
| 65 / 44247 | `dirichletH2LiftLinear_closedGraph` | PASS；图精确等于实际 value(v)=P(u) 的闭集合。 |
| 85 / 44252 | `dirichletH2LiftCLM` | PASS（定义）；完整源、目标 H² Banach 闭图定理；未取 L² 诱导拓扑。 |
| 94 / 44257 | `dirichletH2LiftCLM_value` | PASS；CLM 升级不改变实际 value。 |
| 100 / 44263 | `DirichletH2Regular` | PASS（定义）；明确针对任意已给 H¹₀ 弱 Poisson 解的 H² 正则性谓词。 |
| 105 / 44265 | `dirichletH2Regular_box` | PASS；正边长原盒的既有真实弱正则性内部供应该谓词。 |
| 112 / 44268 | `dirichletH2Regular_graphEpigraph` | PASS；真实全局上图域、光滑高度、法向不变及高度/斜率 Lipschitz 条件准确保留。 |
| 120 / 44274 | `dirichletH2Regular_graphHypograph` | PASS；真实全局下图域，同一完整弱解正则性接口。 |
| 128 / 44280 | `dirichletH2Regular_smoothInner` | PASS；原有限半空间交有界及真实内点供应指数和内域的正则性。 |
| 139 / 44285 | `SpatialTest.cutoffValueTransfer` | PASS（定义）；实际限制伴随零延拓，再限制至目标域并乘 η 的 L² CLM。 |
| 144 / 44290 | `SpatialTest.cutoffValueTransfer_apply` | PASS；伴随等于实际零延拓；与 subdomainZeroExtend 精确一致。 |
| 151 / 44295 | `SpatialTest.cutoffH2_value_exists` | PASS；源 negativeLaplacian、双向支撑资格、实际截断弱方程和目标正则性构造 H²。 |
| 167 / 44300 | `SpatialTest.cutoffH2Transfer` | PASS（定义）；以上实际值映射的完整 H² 连续 lift，未输入目标 Hessian。 |
| 174 / 44305 | `SpatialTest.cutoffH2Transfer_value` | PASS；精确实际截断 L² 值。 |
| 181 / 44311 | `SpatialTest.cutoffH2Transfer_truncate` | PASS；全部一阶 jet 等于真实 H¹₀ 零延拓后的截断乘积。 |
| 194 / 44319 | `SpatialTest.cutoffH2Transfer_dirichlet` | PASS；通过真实测试闭包保持目标 H¹₀。 |
| 201 / 44325 | `SpatialTest.cutoffH2Transfer_tendsto` | PASS；源完整 H² 强极限经子类型拓扑和同一 CLM 得目标完整 H² 强极限。 |
| 210 / 44334 | `SpatialTest.cutoffH2Transfer_ae` | PASS；目标限制测度下的 η·1_S·u 真实 AE 身份。 |
| 222 / 44340 | `SpatialTest.cutoffH2Transfer_of_smooth` | PASS；域内 AE 身份合法转为条件全域 AE；整个目标 jet 识别为真实 ηφ。 |
| 242 / 44347 | `SpatialTest.frontier_mem_of_cutoff_agreement` | PASS；在开放非零集上两域相同，真实 frontier 恒等式逐点传递边界。 |
| 258 / 44351 | `SpatialTest.cutoffTransfer_boundary_zero` | PASS；非零点用真实源 frontier 零值，零点直接消失；覆盖全部目标 frontier。 |
| 268 / 44356 | `SpatialTest.exists_cutoff_box_strong_h2_approximation` | PASS；任意原盒 H²∩H¹₀ 的同一真实光滑序列，保持目标 frontier 零值/H¹₀，强收敛至精确截断状态。 |

## 固定依赖及本地证据

实际 Carleman 导入闭包 **295 文件**；相对 mathematical_base 的 **294 个旧文件逐 Git blob 不变**，唯一新增数学文件为本批模块。固定 root 已导入该模块；全部 28 项 `#check`/`#print axioms` 齐全，递归审计末段的白名单/`collectAxioms` 逻辑相对 base 不变。直接核对本批所调用的 `SobolevTruncation`、`SobolevTopology`、`SobolevRealization`、`DirichletSpace`、`ObservedRegionLp`、`SubdomainZeroExtension`、`DirichletSubdomainExtension`、`WeakLaplacian`、`BoundaryCutoffTransfer`、`BoxStrongH2Density`、`StrongH2GraphTransport`，以及 box/graph/smoothInner 三类实际正则性入口；未重新抄写或重跑不变历史。

已全文读取 T253 冻结独立报告，提交 `0d96050d902550448364db4c804cb1ede5f952bf`，reviewed_at=`2026-10-20T10:04:07+00:00`、11/11 PASS；本固定 proof 中报告逐字节一致，12051 bytes、SHA256 `90b3ad10c7f6366f71c627488fa147c1ed751ca5ea7ca0cc24c714b3078f4fba`。本次也直接读取实际盒密度结论及全 jet 分量/经典导数接口，而非仅引用验收结论。T252、T242 及其正则性依赖均在上述不变闭包内。

Lean **4.35.0**，编译器 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；固定 mathlib lock 与本机无修改 checkout 同为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。已读实际 Banach 闭图定理及 `frontier_inter_open_inter`，其条件与调用一致。

- `/tmp/carleman-t254-local-evidence.json`：source=local，status=PASS，checked/source 均为 `4a84f2b095e71ea776fa79ecf2d568f28270cbe1`；finished_at=`2026-10-20T10:08:20.690032+00:00`，实际 `lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 记录均 exit 0。固定台账定向目标记录也为 exit 0。
- `/tmp/carleman-t254-local-source-manifest.txt`：**1051 项、114077 bytes**，SHA256 `40545139491559ee6b70f8a7bcf9f3363d82e76ab3a40fe82fb5185f042d1e2d`。独立枚举固定提交全部 tracked `.lean` 和 `lean-toolchain`/`lakefile.toml`/`lake-manifest.json`；路径集合、唯一性及每一项 SHA256 均匹配实际固定 Git blob。
- `/tmp/carleman-t254-target-build.log`：实际本批目标 **3480 jobs** 成功，111 bytes，SHA256 `d870f8cfc00aae5b5377407eb07e31dc6110a5284534d8a67df1ba7317f1fb31`。`/tmp/carleman-t254-build.log`：实际根 **4293 jobs** 成功，80 bytes，SHA256 `663df2a94bdf6c1b9c40d16cdd2099a675864a4d900891a412e245f425052a03`。`/tmp/carleman-t254-axioms.log` 为 **0 bytes**。
- `/tmp/carleman-t254-strong-h2-cutoff-transfer-local-axioms.txt`：**3413817 bytes**，SHA256 `b68ab1b0d77d88f39c473bfc9c66d384ad391c57e49d261a562558c764a021be`。28 项实际完整类型与公理逐项读取。全文件 **4086 个公理列表**仅含 `propext`、`Classical.choice`、`Quot.sound`，另有 **10 个无公理记录**；末行实际确认 **10188 声明递归审计 PASS**。无 sorryAx 或新增数学公理。
- 原稿相对 base 不变，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本次只核验指定固定本地执行证据，未重复全构建，未查询远端 CI/看板，也未将本地验证称为 CI。

**无缺陷，接受 C270 的上述 AUXILIARY 范围；P023 及原文覆盖 18/26 不变。** 报告正文和 reviewed_at 冻结后只提交本报告，不修改数学、台账、原稿、根导入、公理工具、其他报告或未来 T255 工作树，不 push。
