# T209 / C225 独立本机验收

- checked_sha: `bf85c15d7a923ca6dce0a5d5fdf10f31c28e413b`
- base_commit: `7d343224295439a2c5b91f1128facfc9b42feafd`
- reviewed_at: `2026-10-20T04:15:54+00:00`
- reviewer: independent local Agent `/root/accept_spatial_lemma`
- result: **PASS — 11/11 显式声明（2 def、9 theorem），无阻断缺陷**
- axiom_check: **PASS**
- scope: **AUXILIARY；17/26 不变，P021 不提升**
- evidence_source: **local**；未查询或声称远端 CI 成功。

直接读取固定 Git 对象中两个新模块的全部证明、raw 完整类型、分析与 MATH_SPEC；对照原稿 `paper/main.tex:2389–2398` 的有限弱恒等式，以及原时间平均势定义和 `2926–2956` 的有限张量测试一致性。原稿 SHA256 仍为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

## 十一项声明

声明均在 `Carleman` 命名空间。前六项位于 `Control/TimeAveragedProductPotential.lean`，后五项位于 `Control/P1FiniteTestConsistency.lean`。

| 实际声明 | raw 行 | 核对结论 |
| --- | --- | --- |
| `Carleman.time_average_product_potential` | 38905 | **PASS**。真实逐胞元平均势乘状态后重构，其 J 像等于原重构平均势乘同一状态的 J 像。 |
| `Carleman.fixedTimeCellPotential` | 38914 | **PASS**。以 `g.period=T` 搬运同一个原 b，使用实际时间胞平均定义。 |
| `Carleman.fixedTimeCellPotential_bound` | 38924 | **PASS**。保留的上界字段精确等于 b.bound；实际 a.e. 有界性由平均构造供应。 |
| `Carleman.fixed_time_average_product_potential` | 38929 | **PASS**。在同一固定 T 的 Bochner/产品空间中保留上述精确乘法身份。 |
| `Carleman.fixedTimeCellPotential_value` | 38938 | **PASS**。值明确为 `dt⁻¹∫_(t_i,t_{i+1}] b(t,x)dt`，未替换原势或平均区域。 |
| `Carleman.time_average_reconstructed_weak_pairing` | 38943 | **PASS**。原平均势强一致性与保界内部供应，结合明确的状态弱极限、预算及测试强极限，得到同一 b、Y、φ 的势配对极限。 |
| `Carleman.p1FiniteTestSequence` | 38966 | **PASS**。在完整 conforming P1 空间构造所有 N+1 物理节点的原有限插值和。 |
| `Carleman.p1FiniteTestSequence_lift` | 38983 | **PASS**。实际 Galerkin 提升等于同一系数与同一空间插值的 Dirichlet 状态和。 |
| `Carleman.p1FiniteTestSequence_value` | 38992 | **PASS**。原 L² 值为同一 `nodalLp ψ.value` 的有限和，未对 Lp 类求节点值。 |
| `Carleman.full_p1_galerkin_finite_test_endpoint_consistency` | 38999 | **PASS**。原 k=0、k=N 的值分别强趋 η(0)ψ、η(T)ψ 的完整有限和，不要求端点消失或 dt→0。 |
| `Carleman.full_p1_galerkin_finite_time_test_consistency` | 39012 | **PASS**。同一全节点序列的前层值、后减前除 dt 的差商、前层完整弱梯度分别强趋原测试、时间导数和空间梯度。 |

## 数学、代表与条件边界

**同一原平均势。** `timeCellPotential` 将 b 限制到真实时间胞元与原空间测度的乘积，再按该胞元的真实正测度 dt 取第一变量平均。`averageFirst` 用 Fubini 的 a.e. 切片供应可测性及 a.e. 上界，并证明原 b 的代表改变不影响平均的空间 a.e. 类。value 等式在所定义代表上成立，保界结论是实际 a.e. 界；没有把保存的 bound 字段等同于最优 L∞ 范数。乘法身份只需空间测度 SFinite，弱配对极限另明确要求有限空间测度；零测度情形没有非法除以空间体积。

J 是实际 Bochner L² 到产品 L² 的线性等距映射。新精确身份使用 J 的真实分片重构 a.e. 公式及乘子 `map_ae`，对有限多个 i 合并空间零测例外，再经产品第二投影搬运。时间胞元严格不交，胞内重构势正好是对应平均势；胞外相应指示项为零，逐项得到两端同一 Lp 类。没有假设 J 满射或任意联合点态代表。固定 T 三个包装仅代入时间域等式，同一 b 未被换成另一个独立系数。

这条身份作用于环境 L² 的真实乘法，**没有**推出或使用 `P_X(bu)=bP_Xu`。已直接核对 T208 的实际弱测试式：投影只因测试属于 X 而在内积中消去，留下原环境势乘状态的配对。新身份恰好可用于此项，与投影算子不交换并不冲突。

**通用弱配对的实际输入。** `time_average_reconstructed_weak_pairing` 明确输入状态重构统一范数界、对 Bochner 空间全部测试的弱收敛至给定 Y，以及测试产品重构强趋给定有界 φ 的 L² 类。J 的弱连续性通过真实 Hilbert 伴随把任意产品测试拉回，不需满射。内部调用的平均势强收敛使用同一个 b、固定 T、dt→0；真实切片投影误差、Fubini 以及 `(2b.bound)²T` 支配供应所需收敛。

随后实际实乘子对称配对把势移到测试侧。误差估计为 `‖a_n v_n−bφ‖≤a_n.bound·‖v_n−φ‖+φ.bound·‖a_n−b‖`，给强收敛后与有界弱状态配对。新结论保留原 Y 与 b，不偷偷把弱状态升级为强收敛；也未宣称已替所有控制序列供应这些通用极限前提。空间无需细化、嵌套或光滑势。

**同一完整 P1 测试。** `p1FiniteTestSequence k=∑_l η_l(k·dt) testGalerkinState ψ_l` 属于完整 `M.conformingSpace (dirichletSubspace S)`。节点只取实际光滑 `SpatialTest.value`；旧成员证明由 FaceMatching、BoundaryFitted、原紧支测试的边界零值产生原 H¹₀ 资格，未输入新的零迹。lift 身份继承实际值映射的弱导数唯一性和线性性，故保留整个能量状态及全部梯度。有限和包括空索引；没有把完整离散状态空间缩成这些测试张成的空间。

端点证明只用实际空间值强收敛和固定系数 η_l(0)、η_l(T)。k=N 的时间严格为 `N·dt=g.period=T`；没有使用某个前一节点近似 T，也不假设时间系数连续或在端点为零。这里 maxDiameter→0 已足够，不需统一形状或 dt→0。

时间三项强一致性则保留原开凸域、有限测度、FaceMatching/BoundaryFitted、统一内球形状界 `diam(K)≤κr_K`、正内球半径、maxDiameter→0 和 dt→0。用于实际 Galerkin 提升的 d>0、有界 S 明示且符合原 P1 场景。η_l、f_l 在 `[0,T]` 连续并满足真实 `HasDerivWithinAt η_l (f_l t)`；不需区间外延拓。旧真实 FTC 把后减前差商识别为导数胞平均，再由实际投影强收敛及双线性张量连续性合成；无需除以 dt 的空间插值误差估计，因此没有 h/dt 耦合。新证明通过值/梯度 CLM 的 `compLpL` 连续性和真实时间重构/张量交换式传递极限，符号、i.castSucc/i.succ 与整个有限和一致，梯度是原全弱梯度。

这里 T 固定，未声称测试估计对 T 统一；未要求网格自由度固定或网格嵌套。本批给势与测试接口，尚未把完整 P1 控制序列的六项方程全部取极限，亦未声称本批构造状态时间迹或证明整体 P021。

## 依赖与固定本地证据

全文读取 T208 冻结报告 `82c6303e2eb3b2fccb6c3896df149f98d10e8c65:governance/reviews/T208-local-acceptance.md`（7/7 PASS，reviewed_at `2026-10-20T04:12:05+00:00`），并直接读取本批使用的 P1GalerkinTests 与 ConformingWeakTesting。新模块 Carleman 递归源闭包 **579** 文件，其中 **577** 个旧文件与基线 Git blob 全部相同。关键实际依赖闭包亦与已接受版本不变：P1GalerkinTests 349 模块与基线一致；P1TensorTestConsistency 155 模块与 `560e3aa8d23c22943b51dd7744da8174944b27ef` 一致；BochnerProductL2 27 模块与 `f0ab18741c799cd2d821174cfce77ffbb454fa20` 一致；AveragedPotentialWeakPairing 353 模块与 `9c62b704e83c3e25302aa14d665337a646beb8ee` 一致。已重读相关平均、弱强配对、P1 强逼近和时间 FTC 的实际证明，不重审无关历史。

独立读取 `/tmp/carleman-t209-local-evidence.json`，status=PASS、source=local、checked/source SHA 均等于本报告 proof，完成时间 `2026-10-20T04:12:07.261500+00:00`；实际全库构建和公理审计均记录 exit 0。核查的是执行记录及固定源码关联，不声称审核者重新运行全库。

| 证据 | 独立核验 |
| --- | --- |
| `/tmp/carleman-t209-target-build.log` | 两模块完成，3799 jobs；187 bytes，SHA256 `207d0460f0d74c104abe85b896bdfd3c8b4e6dbce91edb83e69cb942becf174f`。 |
| `/tmp/carleman-t209-build.log` | 根目标完成，4218 jobs；80 bytes，SHA256 `6d97e8a4e646cc964ac18d06c56523429e23e3daa43fed407635cedf3427b94f`。 |
| `/tmp/carleman-t209-axioms.log` | 0 bytes，stderr 为空。 |
| `/tmp/carleman-t209-conforming-potential-local-axioms.txt` | 2,990,346 bytes，SHA256 `f783fbb89a9316eccb5772b11579c0cd8c1a99519b511c5bb1a9935073629fb5`；末行确认 **9003** 项递归审计 PASS。 |
| `/tmp/carleman-t209-local-source-manifest.txt` | 106,611 bytes，SHA256 `a01be326a1bf7fb37b5c3a3f50d9ede632a275f5631ae32ffa01c39b3cf64b88`。独立枚举全部 tracked Lean 和三项构建配置共 **983** 项，集合完整无重复，每项摘要均与 proof Git blob 匹配。 |

十一项各仅依赖 `propext`、`Classical.choice`、`Quot.sound`；raw 全部 3519 条显式依赖列表及 9 条无公理输出均无白名单外项。固定审计循环使用 `privateToUserName` 与递归 `collectAxioms`，覆盖私有和生成声明；根实际导入两模块，十一项检查齐全。Lean 4.35.0/compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`、mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 及治理协议与固定配置一致。

**签发：C225 在上述 AUXILIARY 范围 PASS，无修复项。** 冻结正文与时间，只单独提交本报告，不修改数学、原稿或台账，不 push。
