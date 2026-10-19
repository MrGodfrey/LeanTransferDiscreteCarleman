# T130 / C146 独立本机验收

- `checked_sha`: `5c1c62ee09ab89d7e28c0b484c02494958856b33`
- `base_commit`: `bee8a93d0856f84c9280d10a19f50da7da2a362f`
- `reviewed_at`: `2026-10-19T06:59:10+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：原 H¹₀ 状态的真实全空间零延拓在完整 H¹ 图拓扑下的连续性，以及零延拓后限制到较大开域仍属于该域原 H¹₀ 测试闭包。未证明光滑内域 H² 正则性、统一二阶先验界或凸域穷竭，P023 不提升，原文保持 **14/26**。

本 Agent 从固定 Git 对象读取两模块全部证明、七项完整展开类型、T130 分析、MATH_SPEC、C146/T130 清单和关键依赖，对照原稿及已经实际读取的 Grisvard 相关页面。治理协议自前次验收不变，已作版本比较。规格、旧验收标签和 CI 均未代替数学核查；工作树后续代码及变化中的 `.ci/axioms.txt` 排除在本次依据之外。

## 全部七项声明

名称省略 `Carleman.`；源位置以 `Carleman/Spatial/` 为根。顺序与固定 C146/T130 及交付 JSON 完全一致。类型行号指本次独立下载并逐字节比对的原始 axioms.txt。

| # | 声明 | 固定源位置 / 完整类型行 | 独立结论 |
|---|---|---|---|
| 1 | `SpatialTest.zeroExtendDirichlet_value_ae` | `DirichletExtensionContinuity.lean:13` / 27399 | PASS；原测试的全空间零延拓值在 volume 下 a.e. 等于同一原全空间光滑函数，域外零值来自真实拓扑支持。 |
| 2 | `WeakSobolevJet.zeroExtendDirichlet_tendsto` | `DirichletExtensionContinuity.lean:25` / 27405 | PASS；原完整 H¹ jet 强收敛经逐字段零延拓保持，使用真实限制算子的 Hilbert 伴随连续性。 |
| 3 | `WeakSobolevJet.extendDirichlet` | `DirichletSubdomainExtension.lean:14` / 27413 | PASS；实际定义先作全空间 H¹ 零延拓，再限制到目标 S，输出真正弱 H¹ jet。 |
| 4 | `WeakSobolevJet.extendDirichlet_value` | `DirichletSubdomainExtension.lean:19` / 27420 | PASS；值严格等于原标量 L² 类零延拓后的真实限制，不更换代表或测度。 |
| 5 | `WeakSobolevJet.extendDirichlet_field_norm_le` | `DirichletSubdomainExtension.lean:25` / 27425 | PASS；k∈Fin 2 的每个完整字段 L² 范数不增，常数为1，包括零阶字段和整个一阶纤维。 |
| 6 | `WeakSobolevJet.extendDirichlet_test` | `DirichletSubdomainExtension.lean:31` / 27431 | PASS；T⊆S 时严格等于同一个全局测试函数视作 S 上测试所得的整个弱 jet。 |
| 7 | `WeakSobolevJet.extendDirichlet_mem` | `DirichletSubdomainExtension.lean:36` / 27437 | PASS；由 T 中真实测试 span 的完整 H¹ 强逼近和 S 中原测试闭包的闭性，得到 H¹₀(S) 成员。 |

## 原论文用途与边界

原 `paper/main.tex:2659–2664` 的 `prop:analytic-realizations` 引用凸域 Dirichlet H² 正则性来识别 D(A) 及供应椭圆正则估计。已在本轮连续审查中实际视觉核对 [Grisvard 1985 本地原书](</Users/wangyu/Documents/math/article/Grisvard1985-Elliptic Problems in Nonsmooth Domains.pdf>) 印刷147–149页，即 PDF159–161页：其证明取光滑凸内域解，将这些 H¹₀ 状态作全空间 H¹ 零延拓，取得共同有界/弱极限后，再识别原域上的解和二阶导数。本报告沿用已读取的这三页，不把执行者的书籍概述当作证据。

本批完成上述路线中的真实 H¹₀ 延拓工具。它适用于任意包含的开域 T⊆S，并未依赖凸性、光滑边界、正则迹、原状态光滑性或 H² 正则性。具体光滑内域解及其原测试闭包成员仍须由后续证明供应；本批不凭这一延拓工具宣称完整正则定理或 P023 已完成。

## 真实测试值与完整全空间弱 jet

已直接复核 `DirichletZeroExtension`、`DirichletTestPairing`、`ZeroExtensionLp` 及相关测试对象。原 `dirichletJetSpace T` 是全部紧支光滑测试 jet 的线性 span 在完整弱 H¹ 图拓扑中的闭包。它不是由点态边界零值定义的空间，也不是原值在标量 L² 拓扑中的闭包。

`zeroExtendLp` 实际为原 L² 代表乘 indicator T 的 MemLp.toLp，具有全空间 a.e. indicator 身份、域内 a.e. 原值身份和真实 L² 范数等式。原 `zeroExtendDirichlet` 将零阶和一阶全部字段分别作此延拓；其全空间弱身份来自原 H¹₀ 闭包与任意全空间紧支光滑测试的配对闭性。该依赖先对真正光滑测试证明全空间积分分部公式，再由连续的值和完整梯度配对传到原图闭包，未误用仅域内测试来直接断言全空间弱导数。

第1项先将全空间延拓值改写为原测试 toLp 的真实 L² 零延拓。对 T 内点，由 `ae_restrict_iff'` 把原域 a.e. 身份变成全空间上“属于 T 则相等”的 a.e. 身份；对 T 外点，φ.support:tsupport φ⊆T 说明该点不在真实拓扑支持，从而同一全局 φ.value 确实为零。两部分与 indicator 身份合并，得到 volume 下的全空间 a.e. 相等。没有从只在 T 内成立的 a.e. 身份直接推出域外相等。

这里的原测试具有实际全空间 C∞、紧支及支持包含条件。测试值、真实 Fréchet 导数和其 L² 类均对应同一函数；没有添加边界 trace 字段或用任意候选导数代替全梯度。

## 完整图拓扑的连续性与范数

已读取 `SobolevTopology`：WeakSobolevJet 是有限个真实 L² 字段的乘积空间中的闭子空间，所用拓扑是完整图拓扑；`fieldCLM k` 对每个 k 连续。第2项使用 subtype 和有限 Pi 拓扑的收敛判据，分别证明 k=0、1 的完整字段收敛，不只证明原值的标量 L² 收敛。

对每个字段，已读取 `ObservedRegionLp.restrictRegion_adjoint`：真实限制 CLM 的 Hilbert 伴随严格等于 `zeroExtendLp`。该等式由 L² 内积、实际 a.e. 限制身份和零延拓积分身份证明；用于此处的 DerivativeFiber 是实际有限维实 Hilbert 空间，所需完备性已由实例供应。故每个字段的零延拓是连续线性算子，原字段强收敛经它传递，再组合成全空间 H¹ jet 收敛。公开声明直接给出所有序列的该收敛性质；这些原图空间为度量空间，因此这是所需连续性，不附加逼近序列的更强条件。

第3项 `extendDirichlet S hT u hu` 的定义严格是 `restrictDomain S (zeroExtendDirichlet hT u hu)`。第4项由两个真实 value 身份得到完全相同的标量 L² 操作。第5项先用限制 L² 范数不增，再用全空间零延拓字段范数等式，获得常数1。k:Fin 2 包含整个零阶和一阶字段，而非只选一个梯度坐标；不存在依赖位置、域、维数或网格的范数等价常数。

定义和值/范数结论本身不要求 T⊆S 或 S 开；即使 S 只截取延拓的一部分，仍是实际限制后的 jet 且范数不增。真正宣称 H¹₀(S) 成员的第6、7项明确要求 S 开和 T⊆S，没有遗漏这一必要包含关系。所有维数、空域和零状态均在实际类型内；未额外要求域非空、有界或正体积。

## 同一测试 jet 与原 H¹₀ 闭包成员

当 T⊆S 时，第6项右侧使用的测试结构保留原 φ.value、smooth 和 compact，仅将支持证明改为 φ.support.trans hTS。因此它是同一个全局函数，不是另构造一个近似代表。`restrictedJet_eq_test` 先利用第1项的全空间 a.e. 身份识别目标域 value，再用开域上的完整弱 jet 值单射识别整个 jet。该单射来自全部光滑紧支测试的真实弱导数唯一性，未假定两个 jet 的梯度预先相等。

第7项从原 `u ∈ dirichletJetSpace T` 解出一列测试 span 中的 U_n，在原完整 H¹ 图拓扑中强收敛到 u。`mem_closure_iff_seq_limit` 在实际度量拓扑上合法；不是用弱收敛或仅值收敛代替图收敛。已复核 `exists_test_of_mem_test_span`：测试在零、加法、实数倍下保持实际 C∞ 紧支及其完整 jet，故每个 U_n 等于一个真实 φ_n 的 Sobolev jet。

原 span 中每项属于 T 的 H¹₀ 闭包，因此第2项可用于整个序列与极限。再由实际 `restrictDomain_tendsto` 得到 S 中完整 H¹ 强收敛。第6项将每个延拓项严格识别为同一 φ_n 在 S 的测试 jet，故每项属于 S 的原测试闭包；该闭子空间的闭性给出极限的成员身份。不同成员证明参数只属于 Prop，未引入额外状态选择。此步骤确实证明原闭包成员，并非从边界零值或未给出的迹定理跳到 H¹₀。

全程仅对阶数1的原 Dirichlet jet 作零延拓。任意 H² 状态的跨边界二阶导数可能有边界项，本批没有声称其零延拓属于全空间 H²，也不需要这种错误前提。

## 固定依赖、构建及递归公理

两新模块的 Carleman 导入闭包共71模块，其中69旧模块与已验收 base `bee8a93d0856f84c9280d10a19f50da7da2a362f` 逐字节不变。另独立比较 `DirichletZeroExtension` 的69模块闭包，与 [T057 / C073](T057-local-acceptance.md) 固定证明 SHA `fbcd888532fe88caff4907495fad399fe6feeb55` 完全不变。已直接读取本次关键旧证明及其真实对象，不仅依赖旧 PASS 标签。固定 root 显式导入两个新模块；源码无 sorry、admit、额外 axiom 或 native_decide。

治理协议、原稿和工具链 pins 与 base 不变；原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean 固定4.35.0；mathlib pin 及本机实际干净 HEAD 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。

实际读取 `/tmp/carleman-dirichlet-extension-target.log` 的3213 jobs成功记录、`-full.log` 的3912 jobs成功记录及6904声明递归审计PASS。本次固定 `-local-axioms.txt` 为 **2,106,590 bytes**，SHA256 **`e44529ffe7a62861c137c62e6e69658853595c0c26e15650d773a5995c1788d9`**。全部七项实际展开类型存在，依赖仅为 `propext`、`Classical.choice`、`Quot.sound`。

全文2392条非空及8条无公理打印记录未发现其他公理。固定 CheckAxioms 的递归主体与 base 不变，对全部经 privateToUserName 识别的 Carleman 声明调用 collectAxioms；末行6904项审计涵盖生成和私有声明，不只是七项显式接口。

## 同 SHA CI、证据版本隔离与独立下载

本 Agent 自行查询 [main CI 39212728130 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39212728130/attempts/1)。run 为 main/push，head SHA 精确匹配，最终 completed/success，`updated_at=2026-10-19T06:58:29Z`。三 job 全部 completed/success：state-check **117929521362**、lean **117929521618**、dashboard / snapshot **117930449368**。

本次临时前缀复用了 T057。验收开始时约定的 main-ci/result.json 实际指向旧 SHA `fbcd888532fe88caff4907495fad399fe6feeb55`，旧 axioms 为1,385,779 bytes。本 Agent 未把它们作为 T130 证据，先将两个旧下载目录完整保留为 `/tmp/carleman-dirichlet-extension-T057-main-ci`、`/tmp/carleman-dirichlet-extension-T057-main-axioms`，再自行下载本次 run 到约定目录。旧验收报告未修改。

本次同 run artifact：`lean-ci-result` **12168083598**，压缩产物492 bytes，digest `sha256:5d36fa84f7013676458a1e8572d0859c7fb59e64f2adc3a0a4bd84b08c707020`；`lean-declaration-evidence` **12168870070**，压缩产物194000 bytes，digest `sha256:332c6cfc5ad5683f8ec6c2fc805df607314403542f44308779f528d58d9054ab`。两份 workflow_run 元数据均绑定上述 run、main 和完整 proof SHA。两次独立 `gh run download 39212728130` 均 exit 0。

实际 `/tmp/carleman-dirichlet-extension-main-ci/result.json` 为 **PASS**，`checked_sha=source_head_sha=5c1c62ee09ab89d7e28c0b484c02494958856b33`，targets 为 Carleman，`finished_at=2026-10-19T06:57:21.761275+00:00`，ci_url 为上述 run/attempt。Lean 编译器提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib 为上述 pin。解压 result 为537 bytes，SHA256 `5183d17141d09b400ce4ea4e1a94c54941836d0e5bad742192af63b3ae4038a8`。

本次实际 `/tmp/carleman-dirichlet-extension-main-axioms/axioms.txt` 与固定本机副本独立逐字节相同：**2,106,590 bytes**，SHA256 **`e44529ffe7a62861c137c62e6e69658853595c0c26e15650d773a5995c1788d9`**，末行实际为 **6904项全声明递归审计PASS**。七项完整类型和基础公理均在此同版本原始证据中；旧 T057 产物及后续工作树未混入。

## 验收决定

**C146：PASS，可升级为 REVIEWED，scope 保持 AUXILIARY。** 七项声明未发现需修复的数学缺陷。真实测试值、全空间弱身份、完整 H¹ 图连续性、字段常数1、同一测试 jet 和原测试闭包成员均已独立核实；同 SHA 三项 CI 与自行下载的原始公理证据一致。

P023 不提升，原文保持 **14/26**。本次仅新增本报告，未修改实现、台账、root 或原稿，未 commit/push；仅在临时目录保留旧证据并下载本次原始产物。签发 UTC 如上固定；最终核对并通知主 Agent 后冻结本报告内容与时间戳。
