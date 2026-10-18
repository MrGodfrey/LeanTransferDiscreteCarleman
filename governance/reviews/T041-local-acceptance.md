# T041 / C057 独立本机验收

- `checked_sha`: `3d5aa9cec281974bef7da9d37ffa11a8f9f75670`
- `base_commit`: `4f669626b3228adea39a16fbf6c1d22313763331`
- `reviewed_at`: `2026-10-18T18:45:16+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：实际梯度配对、真实 H² jet 的负 Laplacian、全部 H¹₀ 测试的 Green 公式、H²∩H¹₀ 进入真实形式算子域，以及完整算子图的双向分布刻画。**没有反向 H² 正则性或域等式结论，不提升完整原文覆盖，仍为 12/26。**

本次从固定提交独立读取四模块全部证明、20 项完整展开类型、相关真实空间/算子依赖及原 `paper/main.tex` Section 3、Section 6 和 A1。阶段规格用于定位，未用执行者陈述或构建成功替代数学验收；当前工作区后续凸支撑逼近模块不在范围内。

## 全部 20 项声明

完整名称均加前缀 `Carleman.`；源码位置相对于固定提交的 `Carleman/Spatial/`。顺序与交付清单及 C057/T041 声明列表完全一致。以下逐项语义结论及同版本远端证据均已核实。

| # | 声明 | 位置 | 独立核对结论 |
|---|---|---|---|
| 1 | `derivativeField_inner` | `GradientPairing.lean:13` | PASS；真实 Euclidean 值 L² 内积等于全部多重指标分量的 L² 内积之和，a.e. 识别和可积性均供应。 |
| 2 | `firstDerivativeField_inner` | `GradientPairing.lean:29` | PASS；Sym.oneEquiv 将一阶多重指标精确改为全部 Fin d 坐标，每个出现一次。 |
| 3 | `weakGradientPairing` | `GradientPairing.lean:39` | PASS；实际一阶字段 L² 内积组成的连续双线性映射，没有零阶附加项。 |
| 4 | `weakGradientPairing_apply` | `GradientPairing.lean:42` | PASS；配对定义性等于两真实 field 1 的内积。 |
| 5 | `negativeLaplacian` | `WeakLaplacian.lean:14` | PASS；以实际二阶 jet 的纯二阶分量之和取负，构成真实连续线性映射。 |
| 6 | `negativeLaplacian_apply` | `WeakLaplacian.lean:17` | PASS；准确展开为 `-Σi Dii u`，没有混合项、重复计数或系数偏差。 |
| 7 | `negativeLaplacian_test` | `WeakLaplacian.lean:24` | PASS；完整 jet 的 k=1 弱身份给每个坐标积分分部，求和得到所有原 SpatialTest 的 Green 公式。 |
| 8 | `negativeLaplacian_dirichlet` | `WeakLaplacian.lean:34` | PASS；真实 H¹ 拓扑连续性与光滑测试闭包将同一身份传至全部 H¹₀ jet。 |
| 9 | `dirichletH2Energy` | `DirichletLaplacian.lean:13` | PASS；准确截断 H² jet 的一阶字段，再通过既有 Hilbert 实现构造真实 DirichletEnergy。 |
| 10 | `dirichletH2Energy_value` | `DirichletLaplacian.lean:17` | PASS；能量嵌入严格保留原 H² jet 的标量 L² value。 |
| 11 | `dirichletH2Energy_green` | `DirichletLaplacian.lean:22` | PASS；所有 DirichletEnergy 测试的实际梯度形式等于负 Laplacian 的 L² 配对。 |
| 12 | `dirichletH2DomainElement` | `DirichletLaplacian.lean:30` | PASS；完整变分身份内部供应原 model.domainElement，输出实际形式算子域元素。 |
| 13 | `dirichletH2DomainElement_value` | `DirichletLaplacian.lean:37` | PASS；域元素在 L² 中恰等于原 u，没有替换状态。 |
| 14 | `dirichletH2DomainElement_operator` | `DirichletLaplacian.lean:43` | PASS；原实际 operator 的值恰为已定义的真实 `-Σi Dii u`。 |
| 15 | `h2_dirichlet_le_domain` | `DirichletLaplacian.lean:50` | PASS；对所有标量类给真实子空间包含 H²∩H¹₀≤D(A)，没有反向或域等式。 |
| 16 | `IsWeakNegativeLaplacian` | `DirichletDistribution.lean:13` | PASS；对全部原 SpatialTest 要求实际梯度配对等于 f 的配对，准确表达分布 `-div(∇u)=f`。 |
| 17 | `isWeakNegativeLaplacian_iff_dirichlet` | `DirichletDistribution.lean:17` | PASS；完整光滑测试与全部 H¹₀ 测试的变分身份双向等价。 |
| 18 | `negativeLaplacian_isWeak` | `DirichletDistribution.lean:35` | PASS；任意真实 H² jet 的纯二阶和之负满足上述完整分布定义。 |
| 19 | `dirichletJetEnergy` | `DirichletDistribution.lean:39` | PASS；任意真实 Dirichlet jet 进入原能量空间，字段和值均保持。 |
| 20 | `dirichlet_operator_graph_iff` | `DirichletDistribution.lean:43` | PASS；对所有标量 L² 的 x、f，原完整算子图与真实 H¹₀ jet 的分布图双向等价，未加入 H² 或有限维限制。 |

## 全坐标配对与实际纯二阶导数

`DerivativeFiber d k` 是以 `Sym (Fin d) k` 为指标的真实 Euclidean 空间。`derivativeField_inner` 展开 L2.inner_def，在一个共同的 a.e. 集上使用全部有限分量的 derivativeComponent_ae，将 Euclidean 内积逐分量展开。每项是两个真实标量 L² 类的内积密度，`L2.integrable_inner` 供应有限求和与积分交换的可积性。没有把不同代表间的 a.e. 等式当作逐点等式使用。

一阶的 Sym.oneEquiv 是 Fin d 与单元素多重指标的一一对应，故求和严格是每个坐标一次。没有维数因子、重复方向、漏掉坐标，亦未把二阶混合指标的计数方式误用到一阶梯度。`weakGradientPairing` 则用原 fieldCLM 1 与真实 L² innerSL 构成连续双线性配对，准确等于 `∫S Σi Di u Di v`，没有加入 `∫S uv` 或任意给定形式。

negativeLaplacian 的定义是连续线性映射 `-Σi derivativeComponentCLM (i::i::nil) ∘ fieldCLM 2`。输入必须是真正 WeakSobolevJet d 2，因而其零阶、一阶和二阶字段已由所有坐标、所有低阶多重指标、全部原 SpatialTest 的弱导数身份联系；这不是仅以 H² 命名的任意数据。i::i::nil 是纯二阶 DiDi，多重指标即使使用无序 Sym 也不会产生排列系数。负号与原正 Dirichlet 算子 `-Δ` 一致。

准确的一阶 truncate 直接保留原零阶和一阶 L² 字段。对每个 i，u.property 在 k=1、α=i::nil、方向 i、任意 φ 上给

`⟨Di u, Di φ⟩ = -⟨Dii u, φ⟩`。

其中 `SpatialTest.sobolevJet_derivative` 已将测试 jet 的该分量严格识别为真实 Fréchet 坐标导数的 L² 类。将坐标身份有限求和，再用负值与内积的线性关系，正好得到 `⟨∇u,∇φ⟩=⟨-Δu,φ⟩`。证明直接使用原完整弱导数定义，没有额外假设 Green 公式、空间强导数的点态正规性或边界积分消失。

## 全部 H¹₀ 测试与真正的闭包拓扑

已直接核对原 SpatialTest：它包含所有全 Euclidean 空间的 C∞ 实函数，具有紧支撑且 tsupport⊆S。S 开时，这是通过全局延拓表达的完整 C_c∞(S)，未缩小为有限元、谱截断、固定坐标函数或任意指定测试子族。φ.toLp 和 φ.derivativeLp 都是实际函数及实际 fderiv 的等价类，相关可积性已证明。

dirichletJetSpace 是这些实际测试 jet 的线性 span 在 WeakSobolevJet 中的拓扑闭包。已复核 SobolevTopology 与 SobolevHilbert：前者的拓扑是所有 L² 导数字段的有限乘积图拓扑，后者通过双向连续线性等价实现平方和 Hilbert 范数；m=1 时包含值和全部一阶导数，绝不是仅标量 L² 闭包。

`exists_test_of_mem_test_span` 由真实零测试、相加、任意实数倍和 span 归纳给出每个 span 元素本身就是一个合法光滑测试 jet。其 jet 运算通过完整弱导数唯一性和值单射证明，并非只核对零阶后自由指定梯度。因此 Green 公式已对整个 span 成立。

固定 u 后，`v ↦ weakGradientPairing (truncate u) v` 和 `v ↦ inner (-Δu) (value v)` 都是该 H¹ 图拓扑中的真实连续函数；等值集合闭合。closure_minimal 将光滑测试身份传给所有 dirichletJetSpace 中的 v。此步骤不要求 u∈H¹₀：任意 H² 的 u 对 H¹₀ 的测试 v 都有该公式，正是正确的一次弱积分分部；不需要 ∂S 光滑或经典法向导数。

同一闭包论证用于一般 H¹ jet u 和任意 L² f，给 IsWeakNegativeLaplacian 的正向延拓；反向将已证属于 dirichletJetSpace 的每个实际测试代入即可。结果是双向等价，未把单向密度推论误作无条件等价，也没有把测试条件当作任意能量测试的目标身份输入。

## H²∩H¹₀ 的实际算子域与作用

`dirichletH2Energy` 保留 truncate u 的实际字段，经 SobolevHilbert.ofJet 放入真实 DirichletEnergy。hu 是原标量 value 属于 dirichletSubspace 的条件。开放域上完整弱导数唯一性给 value 单射，`mem_dirichletJetSpace_iff` 因而能从能量元素的标量成员恢复同一个 jet 的 H¹₀ 成员，没有在同一个 L² 函数上偷偷更换梯度。

已直接读取 `boundedDirichletOriginalForm`：其 V 是实际 dirichletSubspace，form 是实际全梯度 L² 配对，空间闭合、L² 稠密和 Poincaré 强制性由既有证明供应。形式中没有质量项，亦不是外部给定一个满足待证结论的任意算子。

其 `CoerciveForm.domainV` 精确定义为所有存在 L² f、对每个原能量状态 w 满足 `form(v,w)=⟨f,embed(w)⟩` 的 v；domain 是这一子空间在完整标量 H 中的像。operator 由该变分身份选取 f，再由能量嵌入稠密性证明 f 唯一；`domainElement` 和 `operator_domainElement` 正确构造域成员及识别其作用，不预设域等于 H²∩H¹₀。

本次 Green 公式对每个 DirichletEnergy 测试 w 都成立，故可将实际 `negativeLaplacian u` 作为上述 f 内部构造域元素。value 等式严格保持原 u 的标量类；operator 等式通过既有唯一性识别为同一 `-ΣDii u`。最后由 sobolevSubspace 的真实 jet 见证覆盖所有标量 H²∩H¹₀ 成员，得到子空间包含。结论没有要求 u 的额外边界光滑性或某个离散空间成员资格。

## 完整算子图的双向刻画

最终定理对任意 x、f∈L²(volume.restrict S) 量化。左侧存在的是原整个 model.domain 的元素 z，要求其标量值为 x、原 operator z=f。右侧存在真实 H¹ jet u，要求 value u=x、u 属于上述真实 H¹₀ 闭包，并满足全部 SpatialTest 的分布 `-div(∇u)=f`。

前向先用已证 `operator_isAssociated` 将域元素转成原能量状态 v 及对全部能量测试的变分身份，再取同一个 v 的真实 toJet。其闭包成员由 value 单射恢复；将任意原测试通过 dirichletJetEnergy 放进能量空间，所得配对就是真实分布身份。反向从任意右侧 H¹₀ jet 构造原能量元素，利用全测试与全 H¹₀ 变分身份的已证等价，对每个能量状态清偿变分条件，最后由原 associated 等价恢复实际算子域及作用。

这里没有 H² 前提、有限维前提、谱投影、有限测试族或更小的候选域。右侧虽以存在 jet 表述，但开放域上的真实弱导数唯一性保证它表示同一个 x 的弱梯度；不是在 x 上任意附加一个梯度。hS、hd、hb 来自实际有界 Dirichlet 形式的公开输入，量词在所有 x、f 之前，不存在依赖状态的域选择或额外估计假设。

## 原文映射、参数与范围

原 A1（`paper/main.tex:333` 起）同时要求真实闭合稠密形式空间、关联算子与 H²ᵐ 图正则性。Section 3 从同一个形式及其完整关联域构造辅助问题；Section 6 的 P1 和 FD 实例则明确取 V=H¹₀、`a(u,v)=(∇u,∇v)`、A=-Δ_D。本次证明使已构造形式算子的整个图具有正确的分布负 Laplacian 含义，并在 H²∩H¹₀ 上识别其实际纯二阶表达，符合这些接口的空间算子部分。

原附录 `prop:analytic-realizations`（`paper/main.tex:2659` 起）另外用凸域椭圆正则性得到 D(A)=H²∩H¹₀ 及原图估计。本次只有 H²∩H¹₀≤D(A)，不能由完整分布图反推出 H² 正则性，尤其不能声称一般有界开集的域等式。固定规格和 MATH_SPEC 已明确这一点，并澄清 T040 的完整 Lean OriginalForm 只对应原 A1 的空间与形式部分。

辅助配对、negativeLaplacian 和光滑测试公式允许任意 d、任意 S；闭包延拓需要 S 开。关联域及最终完整图要求 S 开、0<d、S 有界，正好覆盖原正维凸多面体/盒子情形，且不增加边界光滑、凸性、连通性或非空条件。d=0 的配对与纯二阶和自然为空；最终关联构造明确用 hd 排除其可能失去梯度强制性的情形。空域也未被隐式排除。限制体积测度的局部有限等实例来自真实 volume，不是假设某个任意测度与 Lebesgue 等价。

本批没有时间、网格、q 或权族参数，也没有数值误差或统一图界的存在断言；只有实际连续线性映射和精确恒等式。它不能清偿原 A1 的反向 H² 正则性、原 A2/A3 的完整具体实现、连续热 CE、节点函数的 H¹₀ 成员、H² 连续代表/点值、具体网格和原定量误差。C057 必须保持 AUXILIARY，不能提升 P011/P012/P014/P015 或完整解析实现；原文计数保持 12/26。`extra_hypotheses=[]` 仅对该公开范围的辅助目标理解。

## 固定依赖、构建与公理

已读取 [T040 基线独立验收](T040-local-acceptance.md) 及 [T039 闭包空间验收](T039-local-acceptance.md)，并直接复核本次实际调用的测试 jet/运算、H¹ 闭包、成员等价、弱导数唯一性、Sobolev Hilbert 互换、Dirichlet 形式、完整关联算子构造与 domainElement；未仅凭先前 PASS 标签接受依赖。

四新模块的 Carleman 导入闭包共 57 模块，其中 53 个旧模块相对 base 逐字节未改；新增恰为本次四模块，固定 Carleman.lean 均显式导入。原稿、治理协议、Lean/mathlib pin 和工作流未变；MATH_SPEC 的差异为本阶段说明及对原 A1 未清偿 H² 部分的措辞澄清。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本机 mathlib 实际 HEAD 为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且工作树干净。

固定 CheckAxioms 对全部 20 项输出实际 `#check @...` 及递归公理列表，末尾遍历所有经 privateToUserName 归属 Carleman 的公开/私有声明并 collectAxioms，仅允许 `propext`、`Classical.choice`、`Quot.sound`。已逐项阅读实际展开类型，与源码、C057/T041 清单及交付名单一致，未出现隐藏的目标 Green 公式、域等式、H² 正则性或有限测试前提。

固定 `/tmp/carleman-laplacian-local-axioms.txt` 实际为 1,244,536 bytes，SHA256 `7cf16d8968456259fc68291dcb9f545d5b61503489b2cbc92f867da4a780edec`；20/20 项的公理集合均恰为上述三项标准基础公理。末行实际为 `Axiom audit passed for all 4465 Carleman declarations.`。本机 `/tmp/carleman-laplacian-full.log` 实际包含 `Build completed successfully (3562 jobs).` 及同一全局审计通过记录，没有 sorryAx 或未批准数学公理。

已独立通过 GitHub connector 核实 [main CI 39155188364 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39155188364/attempts/1)：固定 head SHA、main/push、completed/success。lean（117756847631）、state-check（117756847840）、dashboard / snapshot（117757551675）三个 jobs 均成功。Lean job 的固定工具链、root proof target、checked source 记录及两份证据上传步骤全部 success。同次 lean-ci-result artifact（12146493407）和 lean-declaration-evidence artifact（12146319157）的 workflow_run 均绑定该 run 与固定 SHA。

已实际读取 `/tmp/carleman-laplacian-main-ci/result.json`：status PASS，`checked_sha=source_head_sha=3d5aa9cec281974bef7da9d37ffa11a8f9f75670`，target 为 Carleman，`finished_at=2026-10-18T18:42:01.256638+00:00`；CI URL 对应上述 attempt 1。Lean 4.35.0（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）与 mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 均与固定 pin 一致。

远端原始 `/tmp/carleman-laplacian-main-axioms/axioms.txt` 为 1,244,536 bytes，SHA256 `7cf16d8968456259fc68291dcb9f545d5b61503489b2cbc92f867da4a780edec`，已实际逐字节比较，与固定本机副本完全相同。另逐名核对其中 20/20 项完整类型存在，公理集合均恰为上述三项标准基础公理，末行实际确认全部 4465 声明递归审计 PASS。没有使用其他提交或后续草稿的产物替代本次证据。

## 验收决定

**C057：PASS，可升级为 REVIEWED，scope 保留 AUXILIARY。** 20 项未发现需修复的数学、类型、坐标、符号、a.e. 代表、完整域或量词缺陷；固定版本的语义、完整类型、递归公理及同 SHA main CI 证据均已核实。只接受本报告所列的真实负 Laplacian、全 H¹₀ Green、H²∩H¹₀ 进入域以及完整分布算子图；反向 H² 正则性和域等式仍未完成，不提升任何完整原文结果，计数保持 12/26。

本次仅写本报告，没有修改源码、台账、原稿、root 导入或覆盖表，没有 commit/push。
