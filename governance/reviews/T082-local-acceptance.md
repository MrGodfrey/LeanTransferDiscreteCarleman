# T082 / C098 独立本机验收

- `checked_sha`: `59452751f05398e3446ed5305638a1e20dc89061`
- `base_commit`: `e71006a89160b4a22833727048495aff3f9d2016`
- `reviewed_at`: `2026-10-19T00:09:38+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：原全局 H¹₀ 闭包供应局部物理盒的真实零面迹；原全部 H²∩H¹₀ 状态自动满足 B.1 的边界条件，并获得真实局部仿射、H¹ 残差及局部 Hessian 的统一 h² 界。原 B.1/P025 已于 T081 独立完成；本批不提升 B.2/P026，原文完整结果保持 **13/26**。

直接以 `git show` 读取固定四模块全部证明、16项实际展开类型及关键依赖，核对原 `paper/main.tex` Appendix B 的 B.1（TeX 2796–2836）及 B.2（TeX 2841–2869）如何使用全局 H²∩H¹₀ 状态。未以执行者说明、既有验收或 CI 代替本次数学判断；后续工作树增量不属范围。已读治理协议在本批未变。

## 全部16项声明

名称省略共同前缀 `Carleman.`；固定位置以 `Carleman/` 为根，顺序与交付 JSON、C098/T082 名单一致。

| # | 声明 | 固定位置 | 独立数学核对 |
|---|---|---|---|
| 1 | `subdomainLp_norm_le` | `Spatial/SubdomainContinuity.lean:14` | PASS；实际 eLpNorm 的限制测度单调性与上端有限性给真实 L² 类范数收缩，无伪范数替换。 |
| 2 | `subdomainLinearMap` | `Spatial/SubdomainContinuity.lean:20` | PASS；用真实限制代表及原加法／数乘的 a.e. 身份逐项证明线性。 |
| 3 | `subdomainCLM` | `Spatial/SubdomainContinuity.lean:39` | PASS；从第2项与范数上界1构造连续线性 L² 限制。 |
| 4 | `WeakSobolevJet.restrictSubdomain_norm_le` | `Spatial/SubdomainContinuity.lean:47` | PASS；各阶真实字段分别收缩，原有限乘积 max 图范数也收缩，适用于全部阶数 m。 |
| 5 | `WeakSobolevJet.restrictSubdomainLinearMap` | `Spatial/SubdomainContinuity.lean:53` | PASS；完整原弱 jet 每个字段的限制线性，全弱身份由已证明的实际限制构造保留。 |
| 6 | `WeakSobolevJet.restrictSubdomainCLM` | `Spatial/SubdomainContinuity.lean:65` | PASS；图拓扑中以界1打包实际限制，没有改用单独值的 L² 拓扑。 |
| 7 | `WeakSobolevJet.restrictSubdomain_test_value_ae` | `Spatial/SubdomainContinuity.lean:71` | PASS；原全局测试的局部值类仍 a.e. 等于同一个实际光滑函数。 |
| 8 | `weakJetBoxFace_bounded` | `Spatial/CoordinateBoxTraceContinuity.lean:13` | PASS；真实长度 L 的平方迹界和 valueCLM／field 范数界给固定盒上完整 H¹ 图范数的有界性。 |
| 9 | `weakJetBoxFaceCLM` | `Spatial/CoordinateBoxTraceContinuity.lean:39` | PASS；已有真实线性面迹用已证明界打包为 CLM，不自由假设迹连续。 |
| 10 | `weakJetBoxFaceCLM_apply` | `Spatial/CoordinateBoxTraceContinuity.lean:46` | PASS；CLM 作用精确等于既有真实弱面迹。 |
| 11 | `subdomainBoxFaceCLM` | `Spatial/DirichletBoxFace.lean:16` | PASS；完整全局 H¹ 图的实际局部限制与实际盒迹连续复合。 |
| 12 | `subdomainBoxFaceCLM_apply` | `Spatial/DirichletBoxFace.lean:22` | PASS；展开后是局部限制原 jet 的真正面迹，未另选状态。 |
| 13 | `subdomainBoxFace_test_zero` | `Spatial/DirichletBoxFace.lean:28` | PASS；全局测试支撑在 S 内、整个闭面在 Sᶜ，结合真实连续代表面迹识别推出零面 L² 类。 |
| 14 | `dirichlet_subdomain_box_face_zero` | `Spatial/DirichletBoxFace.lean:50` | PASS；实际复合 CLM 的闭核包含全测试张成及其原 H¹ 图闭包，即完整 dirichletJetSpace。 |
| 15 | `WeakSobolevJet.restrictSubdomain_truncate` | `Spatial/DirichletLocalAffine.lean:14` | PASS；两操作在各阶实际字段及弱证明上按定义交换，对任意 m≤n 成立。 |
| 16 | `dirichlet_h2_local_boundary_affine` | `Spatial/DirichletLocalAffine.lean:19` | PASS；从原全局 H²、值的 H¹₀ 成员资格与物理面几何自动供应 B.1 全部局部零迹，输出实际局部残差和原局部 Hessian 界。 |

## 实际 L² 限制与完整弱图

`subdomainLp hTS u` 是原代表在 volume|T 下的真实 L² 类：T⊆S 给限制测度单调性，原 MemLp 经 mono_measure 产生局部 MemLp，再用 toLp。它的代表与原 u 在 T 上 a.e. 相同。范数证明先将局部代表的 eLpNorm 换回原代表，使用测度单调性，再由原 L² 的 eLpNorm 有限正确转 ENNReal.toReal；未使用无穷范数转实数为零的退化行为。

加法与数乘的原 a.e. 身份通过 `ae_mono` 从 volume|S 下传到 volume|T，再与新限制类的代表身份相交，故所定义 LinearMap 真实线性。mkContinuous 的常数恰为1。底层范数收缩只要求 NormedAddCommGroup；线性打包另要求实赋范空间，实际展开类型没有无关的完备性、有限维、域有界或正测度前提。

已直接读取既有 `IsWeakSpatialDerivative.restrictSubdomain`：任意局部 SpatialTest 的同一实际函数，通过支撑包含关系成为原 S 的全局测试；该函数及其真实 Fréchet 导数在 T 外均为零，故相关 T 积分精确等于 S 积分。代表的 a.e. 还原后得到原完整弱积分分部身份。`derivativeComponent_subdomain` 还逐真实分量证明提取导数与限制交换，随后对所有阶数、多指标及坐标装配完整局部 jet。没有缩小测试族、指定方便的局部梯度或声称不合法的全空间弱零延拓。

`WeakSobolevJet` 的原拓扑来自有限乘积的真实 L² 导数字段，其范数为各阶范数的 max。第4项对每个字段使用真实 L² 收缩，再用字段范数≤原 jet 范数控制，得到完整图范数收缩。图连续性因此同时控制值和全部导数，正好是原 Dirichlet 闭包所用拓扑；没有把 H¹ 闭包换成标量 L² 闭包。限制与低阶截断都是对同一字段数组按索引选择，故第15项为真实定义等式，不增加可交换性前提。

## 实际盒迹在原 H¹ 图拓扑中的连续性

已核对使用的真实 `weakJetBoxFaceLinearMap`：它将原 H¹ jet 的值和第 i 个弱导数送入实际坐标盒迹。该迹经保测度坐标拆分、原完整弱测试得到的统一 a.e. 弱切片，以及切片唯一连续代表的端点构造。对连续代表确实等于真实面限制，对一般 H¹ 状态则仍是实际 L² 面类，不能解释成任意代表的边界点值。

固定正轴向长度 L=b_i−a_i 后，原实际估计为

`‖Tr_i u‖² ≤ (2/L)‖value u‖² + 2L‖field₁u‖²`。

令 V 为原 valueCLM，有 `‖value u‖≤‖V‖‖u‖graph`，而 `‖field₁u‖≤‖u‖graph`。新证明得到 `‖Tr_i u‖²≤B‖u‖graph²`，其中 `B=(2/L)‖V‖²+2L≥0`，再用 B≤(B+1)² 及两边非负给算子界 B+1>0。没有遗漏长度因子或将不同图范数直接混同。

这个连续性常数允许依赖固定盒子和方向。它只用于“零迹映射的核是闭集”，从不作为最终 h² 误差常数使用。最终统一常数来自既有 B.1，故此处不需要也没有偷偷假设盒子一致的图范数迹界。横向其他侧长退化时对应限制测度可为零，基础连续性声明仍有意义；最终局部逼近则明确要求所有边长正。

## 全局测试到物理面零迹，再到完整 H¹₀

对局部盒 B⊆S 和整个所选闭面 F⊆Sᶜ，复合算子为 `F_map = Tr_F ∘ restrict_B`，它是原全局 H¹ 图到真实横向 L² 面空间的连续线性映射。

对每个原 `φ : SpatialTest S`，第7项保证局部限制 jet 的值 a.e. 等于同一 φ.value；该函数全局光滑因而连续。调用真实连续代表面迹识别后，面迹类 a.e. 等于 φ 在实际 insertNth 面参数化上的值。限制测度的 a.e. 点确在横向开盒中，它们插入上下端点后属于整个闭面：横向严格区间条件弱化为闭区间，轴向由正长度及端点选择保证。

若该面点落入 φ 的闭支撑，则 φ.support 迫使它位于 S，与 F⊆Sᶜ 矛盾，因此实际函数值为零。用 Lp.ext 及零类的 a.e. 代表身份得到真正的零面类。这只在光滑测试上使用连续代表；对一般待逼近状态没有使用点值或连续性。

原 `dirichletJetSpace S` 的定义是所有这些真实测试 H¹ jet 的线性张成在完整原 H¹ 图拓扑中的闭包；`dirichletSubspace S` 是该空间的实际 value 像。第14项构造上述实际 CLM 的代数核，先用每个测试的零迹证明 span⊆ker，再以 `F_map.isClosed_ker` 和 `Submodule.topologicalClosure_minimal` 得整个 dirichletJetSpace⊆ker。所含的是原所有测试及整个原闭包，未用额外边界刻画公理，也没有只控制某个选定逼近序列。

这一零迹定理本身甚至不要求 S 开；最终应用中 S 开用于把 scalar H¹₀ 成员资格识别到原 H¹ 截断 jet，并保证 frontier S⊆Sᶜ。原 u 的值属于 dirichletSubspace，意味着存在一个原 H¹₀ jet 有该值；`mem_dirichletJetSpace_iff` 通过原开域的完整弱导数唯一性和值注入性，将它严格识别为当前 u 的一阶截断。不是将同值但未识别导数的另一状态送入迹算子。

## 全部全局 H²∩H¹₀ 状态的实际局部 B.1 应用

第16项实际量词次序为：

`∀ d, ∀ κ≥1, ∃ C>0, ∀ open S, ∀ a,b,h,J,u, ...`。

盒 B 为真实 openCoordinateBox a b，B⊆S，所有边长正、h>0，并保留原比较 `h/κ≤b_i−a_i≤κh`。J 是任意所选闭面集合，且每个选中整个闭面位于 frontier S。原状态 u 是 S 上全部0、1、2阶完整分布弱 jet，其原值属于 dirichletSubspace S；不要求 S 有界、连通、凸或光滑，不新增状态连续代表、局部零迹或预先存在的局部逼近。

S 开给 S 与 frontier S 不交，所以所选面在补集。第14项对原一阶截断提供每个选中面的真实零迹；第15项把它转换成“局部 H² 限制的一阶截断”的相同迹。这恰是 `OriginalForm.boundary_affine_lemma` 对同一局部状态要求的全部边界条件，没有把最终零迹留作用户前提。

调用 B.1 后得到同一局部域上的实际仿射 p 与完整 H¹ 残差 r。p 在所有选中的整个闭面逐点为零；r.value 在 B 上 a.e. 等于局部限制值减 p。通过限制 value 的精确身份和 subdomainLp_ae，最后把它还原成原全局代表 u 减 p，未改变残差或误差量。

局部 H² jet 的二阶字段按定义就是 `subdomainLp hBS (WeakSobolevJet.field 2 u)`。因此最终右端严格为原 Hessian 的实际局部 L² 限制范数，证明直接接受 B.1 原界，无需估计成较大的全域 Hessian 范数。左端为 `‖value r‖+h‖field₁r‖`，其中完整弱 jet 保证该梯度是原差的全部真实弱梯度。Hessian 使用原对称多指标 Euclidean 分量约定，没有自由设定的能量或额外低阶项。

代码在引入 S、a、b、h、J、u 之前就从 B.1 取到 C>0，并原样使用。局部限制的收缩常数1以及迹连续性证明中的固定盒常数均不乘入最终 C。因而 C 只依赖维数和 κ，保持实际 h² 及 h·gradient 尺度；没有小 h 条件，未除以状态或 Hessian 范数。空面集、单面、上下两面、角点及全部面均由任意 J 覆盖；最终环境维数 d+1≥1 包含一维区间和零维横截面。

## 原文定位与范围边界

原 B.2 以所有 `v∈H²(Ω)∩H¹₀(Ω)` 为输入，证明开始在每个局部块 B_K 选取 B.1 的 p_K。当前结果严格供应这个应用中的物理面零迹义务，得到原全局 v 的实际局部齐次 h² 仿射误差，不需要原 v 的节点值。

原 B.1/P025 已在 [T081独立验收](T081-local-acceptance.md) 对本次基线作为 PAPER 完成，含物理尺度和两非平行面的角点核零结论。本报告不重复提升它。当前仍没有实现原 FD Kuhn 网格的全部节点星、局部矩算子、`Q_hp_K=p_K` 的实际重构身份、局部稳定性及加权有限重叠全域求和，不能据此声称 B.2/P026 完成。固定覆盖表中已有13项 REVIEWED/PAPER，P025 绑定已验收基线，P026 仍为 PLANNED；本批保持 AUXILIARY 和13/26正确。

## 固定依赖、本机构建与公理

四模块的 Carleman 导入闭包共183模块，其中179旧模块与基线逐字相同，新增恰为本批四模块。这包括原完整 B.1 及其实际迹、核校正、Hessian 和物理尺度依赖，故 T081 的同基线验收适用。本次另直接读取 B.1 入口及 physicalBox actual 实现、原 Dirichlet 定义和值识别、完整图拓扑、原弱子域限制、真实盒迹及本批全部证明，检查它们被正确调用。没有用已有 PASS 代替新的组合语义审查。

原稿、治理协议、Lean/mathlib pin 和 CI 工作流未由本批改变。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean 为4.35.0，本机 mathlib 实际 HEAD 为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且工作树干净。root 显式导入四模块，CheckAxioms 增量只加入16项完整类型和公理输出，原全局递归检查未削弱。

固定 `/tmp/carleman-dirichlet-face-target.log` 实际含定向3365 jobs成功，`/tmp/carleman-dirichlet-face-full.log` 实际含 `Build completed successfully (3730 jobs).` 与 `Axiom audit passed for all 5777 Carleman declarations.`。固定 `/tmp/carleman-dirichlet-face-local-axioms.txt` 为 **1,665,777 bytes**，SHA256 **`2cf4be3976e3dbc77b0849a1db265c144365b62a77e79c36a059a5ce12992ebe`**。

16/16项实际完整类型逐一匹配，各恰有一条公理记录，只依赖 `propext`、`Classical.choice`、`Quot.sound`。全部1748条显式公理记录（1744个不同声明）也无白名单外公理；递归审计覆盖所有5777个 Carleman 声明及生成辅助声明，无 sorryAx 或无依据数学公理。四新模块无 sorry/admit/axiom/unsafe。

## 同 SHA 正式远端证据

已独立通过 GitHub connector 读取 [main CI 39179213298 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39179213298/attempts/1)：main/push，head SHA 精确匹配固定版本，run 为 completed/success。lean（117828189342）、state-check（117828189622）、dashboard / snapshot（117828903408）三项 jobs 均 completed/success。实际工具链准备、证明构建、checked source 记录、两份证据上传及同次快照步骤均 success。同 run 的 lean-ci-result artifact（12154808977）和 lean-declaration-evidence artifact（12155172823）均绑定固定 SHA、main 且未过期。

已实际读取 `/tmp/carleman-dirichlet-face-main-ci/result.json`：status PASS，`checked_sha=source_head_sha=59452751f05398e3446ed5305638a1e20dc89061`，targets 为 Carleman，`finished_at=2026-10-19T00:07:56.458497+00:00`，ci_url 精确对应该 run/attempt。实际 Lean 4.35.0 提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib 为上述固定 pin。

原始远端 `/tmp/carleman-dirichlet-face-main-axioms/axioms.txt` 与固定本机文件已独立逐字节比较，完全相同：**1,665,777 bytes**，SHA256 **`2cf4be3976e3dbc77b0849a1db265c144365b62a77e79c36a059a5ce12992ebe`**。远端16/16项完整类型和公理记录逐名匹配；全部1748条显式记录（1744个不同声明）仅含三项正常基础公理，末行为 **`Axiom audit passed for all 5777 Carleman declarations.`**。未混用其他提交、其他 run 或后续工作区产物。

## 验收决定

**C098：PASS，可升级为 REVIEWED，scope 保持 AUXILIARY。** 固定16项未发现限制的真实类与弱身份、图拓扑、测试支撑、闭核包含、原 H¹₀ 识别、局部 Hessian、常数量词或尺度方面需要修复的缺陷。完整同 SHA 三项 CI 与原始公理证据均已独立核实。

本次只写本报告，没有修改数学实现、台账、原稿或 root 导入，没有 commit/push。范围保持 AUXILIARY，B.2/P026 仍待，原文计数保持13/26。
