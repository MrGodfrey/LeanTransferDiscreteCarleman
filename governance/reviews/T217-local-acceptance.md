# T217 / C233 独立本机验收

- checked_sha: `79151186853d57b5e937851b51ace47c05a4e7ff`
- base_commit: `17b0a22b45b9d314f90414b72d3c3198ef129f0d`
- reviewed_at: `2026-10-20T05:07:09+00:00`
- reviewer: independent local Agent `/root/accept_spatial_lemma`
- result: **PASS — 11/11 声明（9 定理、2 定义），无阻断缺陷**
- axiom_check: **PASS**
- scope: **AUXILIARY；17/26 不变，不提升完整 Proposition A.1**
- evidence_source: **local**；按现行协议核对固定本地构建、公理及源文件关联，不查询或声称远端 CI 成功。

直接读取固定 Git 对象中的两模块全部定义与证明、十一项完整 raw 类型、分析及 MATH_SPEC，对照原稿 `paper/main.tex:2615–2652` 中光滑乘法保持 V 和 D(A) 的空间步骤。原稿 SHA256=`492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本批真正构造乘后弱射流并证明 H₀ᵐ 闭包保持；一般 W^{2m,∞} 算子系数、交换子量化界和完整加权形式估计不在已完成范围。

## 十一项声明

源码均位于固定 SHA 的 `Carleman/Spatial/`；raw 行号指 `/tmp/carleman-t217-high-order-product-local-axioms.txt`。

| 模块:行 | 完整声明 | raw 行 | 独立结论 |
| --- | --- | --- | --- |
| HigherWeakProduct:23 | `Carleman.WeakSobolevJet.leibnizField_perm` | 40204 | **PASS**：全部 List.Perm 构造归纳；cons 用真实弱导数唯一性，swap 用真实混合弱导数交换。 |
| HigherWeakProduct:42 | `Carleman.WeakSobolevJet.smoothProductJet` | 40217 | **PASS**：实际有限分量组装全阶 L² 射流，并逐条证明完整弱导数链。 |
| HigherWeakProduct:59 | `Carleman.WeakSobolevJet.smoothProductJet_value` | 40231 | **PASS**：零阶值恰为原 `(a []).map (value u)`。 |
| HigherWeakProduct:68 | `Carleman.WeakSobolevJet.continuous_wordField` | 40243 | **PASS**：允许长度内是真实场/分量 CLM；超出阶数的定义零分支连续。 |
| HigherWeakProduct:77 | `Carleman.WeakSobolevJet.continuous_leibnizField` | 40247 | **PASS**：有限 Leibniz 和的每项是实际有界乘子与原连续分量映射的复合。 |
| HigherWeakProduct:83 | `Carleman.WeakSobolevJet.smoothProductCLM` | 40252 | **PASS**：原值注入性给线性，有限场组装给实际图拓扑连续性。 |
| HigherDirichletProduct:20 | `Carleman.smoothProductCLM_test` | 40266 | **PASS**：对任意原测试，乘后射流精确等于真实乘积测试的全阶射流。 |
| HigherDirichletProduct:28 | `Carleman.smoothProductCLM_mem_higherDirichlet` | 40276 | **PASS**：测试保持与连续线性映射的闭包保持给真实 H₀ⁿ 成员资格。 |
| HigherDirichletProduct:38 | `Carleman.boundedSmooth_map_mem_sobolev` | 40286 | **PASS**：原有界光滑乘子的实际内部导数供应全部系数，内部构造乘后 Hⁿ 射流。 |
| HigherDirichletProduct:51 | `Carleman.boundedSmooth_map_mem_higherDirichlet` | 40293 | **PASS**：同一真实乘法保留原 H₀ⁿ 闭包及实际零阶 L² 类。 |
| HigherDirichletProduct:68 | `Carleman.boundedSmooth_map_mem_higherDirichlet_domain` | 40299 | **PASS**：同一 `w.map u` 同时属于 Hⁿ 与 H₀ᵐ；取 n=2m 得原域空间保持。 |

## 关键数学核对

**真实弱 Leibniz 场及对称性。** 已直接读取旧 `CoordinateWords`、`WeakLeibniz`、`WeakProduct`、`WeakMixedDerivative`。`derivativeSplits` 保留每次导数落在乘子或状态上的所有选择及其重数，故实际有限和包含正确 Leibniz 系数；没有把二项式重数丢弃。原弱乘积规则对全部 `SpatialTest S` 应用真实乘积测试，使用实际 Fréchet 导数与 a.e. L² 乘子身份，逐阶产生 `leibnizField_weak`。本批使用这一构造性定理，未调用需要预先存在乘后射流的旧 `wordField_mul` 来倒置论证。

`leibnizField_perm` 的 nil 分支平凡；cons 分支先用归纳等式识别被求导的场，再由同方向弱导数唯一性识别下一阶；swap 分支使用同一尾词场的两项一阶弱导数及两项混合二阶弱导数。旧 `mixed_commute` 在所有原测试上两次分部积分，通过测试的真实二阶导数交换与分布分离得到相等，不要求原状态有经典导数。cons 所需 `length<n`、swap 所需 `length+2≤n`、trans 的长度传递均在实际证明中供应，没有越过已给定的最高阶。系数 a 的真实微分链为显式辅助输入，不是任意指定的假导数。

**全弱射流与真实图拓扑。** `smoothProductJet` 对每个阶 k、每个 `Sym (Fin d) k`，以其排序坐标词的实际 Leibniz L² 场进行 `derivativeFieldAssembly`。排序只选代表；新增坐标的排序词与 cons 词由刚证明的置换不变性识别，随后 `leibnizField_weak` 逐字段满足原 jet 的全部弱关系。每个无序多指标组装一次；有序分裂的 Leibniz 重数没有被错误当成额外导数范数分量。空词给原乘积值，不是新命名的无关状态。

已读取 `SobolevTopology`、`SobolevRealization`、`SobolevHilbert`：jet 拓扑来自全部有限 L² 导数场的积范数，原完整弱身份为闭条件；与平方和 Sobolev Hilbert 范数有实际连续线性双向等价，未误称等距或借用零阶 L² 的拓扑。每个允许阶词场是原 `fieldCLM` 与真实分量 CLM 的复合；Leibniz 场为有限连续和。新 CLM 的连续性正是在该完整图拓扑中逐分量证明。其线性性通过原值映射注入性及真实标量乘法的线性性得到，未假设乘后梯度唯一之外的新目标估计。此处证明固定乘子的有界连续作用，不宣称其算子范数对所有权参数统一。

**原测试与 H₀ᵐ 闭包。** 已直接读取 T216 的实际 `allOrderJet`、`higherDirichletJetSpace` 及测试闭包等同证明。`smoothProductCLM_test` 比较两个已经内部构造、满足完整弱身份的射流；原值注入性把零阶乘法身份提升为所有阶相等。旧 `SpatialTest.mulOn` 的值确为真实函数乘积：在 S 内由域内光滑性求导，在 S 外利用原测试紧支包含 S，得到邻域上乘积恒零，故保持全空间光滑与原紧支。没有要求权在域外光滑延拓，也没有输入乘后边界迹。

`clm_mem_closed_span` 先由测试保持推出 span 保持，再用真实连续线性映射与拓扑闭包关系。这里的闭包是 Hᵐ 图拓扑中的原测试闭包；T216 已证明 span 的载体就是测试射流集合，因此不是另设较大边界空间。随后取同一 value 像得到真实 H₀ᵐ 的 L² 成员资格；没有把 L² 稠密像错误当作 L² 闭空间。

**实际导数供应与原文范围。** 最后三项从 `BoundedSmoothOn w.value S` 内部选用 `intrinsicWordMultiplier`，其值是原函数的实际 `wordDerivative`，可测性与有界性由域内光滑、各有限阶真实 Fréchet 导数界和受限测度供应。`intrinsicWordMultiplier_derivative` 在开域内部证明 cons 是实际方向导数，空词乘法与原 w 的作用精确相等。因此最终只输入原状态成员资格和原光滑乘子条件，不输入任意高阶系数族、乘后射流存在或其范数界。

`BoundedSmoothOn` 明确包含 S 内 C∞ 及所有有限阶实际导数有界；它不是一般 W^{2m,∞} 系数的替代定义。已读取 `SmoothOnClosure.boundedSmoothOn` 及 `BoundedSmoothOn.allowedWeight`：在原有界域的内禀闭包光滑权下，这一条件可由实际紧性与固定参数权导数供应，无域外延拓前提。当前最终定理是通用成员保持接口，不同时宣布原交换子 q 次幂估计或全部权族的统一算子范数。

最后的交空间结论使用同一个 L² 对象 `w.map u`，分别证明 Hⁿ 与 H₀ᵐ 成员，允许 n、m 任意且不要求它们预先相关；取 n=2m 即原文假设的域空间。它没有重新证明某个关联算子的域等式，也没有覆盖一般非光滑 W^{2m,∞} 算子系数的乘法。m/n=0、d=0、空域均没有被除法或不合法索引排除。开域、测度集中条件及局部有限条件在通用辅助接口中明示，原受限 Lebesgue 实例内部满足；没有增加正体积、全域有限体积、几何正则性或状态光滑性条件。

## 依赖验收与固定本地证据

签发前已全文读取 T216 冻结报告 [T216-local-acceptance.md](T216-local-acceptance.md)，单文件提交 `061e2229186295742d29c00397e0b7a1ed480e2e`，checked SHA 等于本批基线，reviewed_at=`2026-10-20T05:04:58+00:00`，25/25 PASS。该报告与本次直接读取的测试射流/闭包实际源码一致。新模块递归 Carleman 闭包 **87** 文件，其中 **85** 个旧文件与基线逐字节不变；另外比对旧 `DirichletWeakProduct` 与已接受 T067 `604328efce1cc28e4d6fe6cadcdaa039ee0e76a3` 不变。已读取本批用到的关键旧证明，不重复无关历史。

`/tmp/carleman-t217-local-evidence.json` 的 checked/source SHA 均为本报告 proof，source=local、status=PASS，finished_at=`2026-10-20T05:03:45.690033+00:00`。实际 `lake build Carleman`、`lake env lean tools/CheckAxioms.lean` 均记录 exit 0；定向 `target-build.log` **3229 jobs** 成功，全库 `build.log` **4241 jobs** 成功，`axioms.log` 为 0 bytes。此次审核核对执行记录及固定源关联，未声称另行重建旧闭包。

独立枚举 `/tmp/carleman-t217-local-source-manifest.txt` 的 **1005** 项 tracked Lean/三项构建配置，集合完整无重复，逐项 SHA256 与 proof Git blob 一致。清单 **109012 bytes**，SHA256=`63231f4bce3d280e96018310b9893af16bb87fac5a915d06db5d0a8034398ff4`。Lean v4.35.0/compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` 与 mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 均符合固定配置。

固定 raw **3097407 bytes**，SHA256=`eb96e122d444d248264fa65b14e0b6b121b3c65d9598a04117700b9caaa0f20e`。十一项完整类型和公理记录均逐项核对，只有 `propext`、`Classical.choice`、`Quot.sound`。全部 **3591** 条非空公理列表与 **9** 条无公理记录均无白名单外项；末行 **9173** 项全命名空间递归审计 PASS，无 sorryAx。固定 root 导入两模块，十一项 `#check`/`#print axioms` 齐全；实际审计以 `privateToUserName` 与 `collectAxioms` 检查含生成辅助声明的完整 Carleman 命名空间。

本报告于上述 reviewed_at 冻结，仅单文件提交，不修改数学、台账、原稿或覆盖统计，不 push。
