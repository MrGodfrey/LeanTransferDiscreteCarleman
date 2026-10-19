# T106 / C122 独立本机验收

- `checked_sha`: `337d9c1b8c5fadce4e638a2c96311e230ee94bb1`
- `base_sha`: `2f2e71d4359a206ac9035d73b61889bfa3cb7bfb`
- `reviewed_at`: `2026-10-19T03:42:53+00:00`（UTC；同版本最终 CI 和原始产物核验完成时间）
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**。23/23 项显式声明通过；C122 可记为独立验收通过。原文覆盖保持 **14/26**，不提升完整 FD / P012。
- 独立验收者：`/root/accept_section3`。本报告定稿后不再变更上述签发时间。

本次直接从固定 Git 对象读取三个新模块全部源码、实际完整展开类型、关键依赖、规格 `governance/analysis/T106-fd-physical-spaces.md`，对照原论文而非只阅读执行者报告。自行查询同 SHA main CI、自行下载同 run 的两份原始产物并比较字节。只新增本报告，未改实现、台账或提交；工作树 T107 重构和质量伴随模块未纳入验收。

## 原论文映射

固定 `paper/main.tex:1634–1667` 给出全部内部节点状态、质量 `m_h=∏ᵣδᵣ`、物理配对 `m_h Σᵢ fᵢgᵢ`，以及 ω 内节点组成的控制空间、零延拓 B 和限制 B*。其加权范数平方为 `m_h Σᵢ(σ(xᵢ)fᵢ)²`，控制范数则仅对 ω 内节点求和。固定 `paper/main.tex:466–469` 的 N5 要求全部状态的真实观察界，Appendix B Step 3（2878–2889）以帽函数支撑和局部质量估计证明它。

本批把这些原配对与此前节点能量提升为真实有限维 Hilbert 空间及其算子，保留完全相同的数值数据和精确范数。原来的内部索引由 `Fin (Nᵣ-1)` 对应实际坐标 `aᵣ+1`，故原 `Nᵣ≥2` 时恰为 `1,…,Nᵣ-1` 的全部节点；控制索引是实际点落在 ω 中的子类型，没有减少状态或替换控制区域。

## 23 项声明逐项核查

以下省略共同命名空间 `Carleman.`，路径相对于固定提交的 `Carleman/`。

| # | 声明及固定源码位置 | 独立核查结果 |
|---|---|---|
| 1 | `PhysicalFiniteSpace` — `Spatial/PhysicalFiniteSpace.lean:12` | PASS；以独立命名类型封装全部 `ι → ℝ`，质量参数 `mass>0`。不是函数的子空间或某类特殊状态。 |
| 2 | `PhysicalFiniteSpace.valuesEquiv` — `:21` | PASS；与全部节点函数的真实线性等价，正反方向均为同一节点值；不宣称与函数上确界范数等距。 |
| 3 | `PhysicalFiniteSpace.core` — `:25` | PASS；直接定义内积 `mass Σ fᵢgᵢ`，证明对称、加法、数乘及正性；正定性由 mass 非零和非负平方和逐项为零得到 `f=0`。 |
| 4 | `PhysicalFiniteSpace.inner_eq` — `:60` | PASS；实际内积严格等于上述物理配对，任意独立 f、g。 |
| 5 | `PhysicalFiniteSpace.norm_sq` — `:63` | PASS；该实际范数平方严格等于 `mass Σ fᵢ²`，由真实内积自身身份得到，没有范数等价常数。 |
| 6 | `PhysicalFiniteSpace.norm_eq` — `:68` | PASS；实际范数等于物理平方和的非负平方根；用范数非负合法去平方。 |
| 7 | `PhysicalFiniteSpace.multiplier` — `:72` | PASS；任意有限节点函数 b 的真实逐节点乘法线性映射，经有限维连续性转为连续线性映射。 |
| 8 | `PhysicalFiniteSpace.multiplier_apply` — `:78` | PASS；实际算子逐值为 `bᵢfᵢ`，没有引入投影或修改节点数据。 |
| 9 | `PhysicalFiniteSpace.multiplier_norm_sq` — `:81` | PASS；实际乘子作用后范数平方精确为 `mass Σ(bᵢfᵢ)²`。 |
| 10 | `CartesianPhysicalState` — `Spatial/CartesianPhysicalSpaces.lean:16` | PASS；取完整内部节点索引及质量 `∏δᵣ`，质量正性由全部正步长的有限乘积内部给出。 |
| 11 | `CartesianPhysicalControl` — `:19` | PASS；取 ω 内实际内部节点子类型及同一质量，控制数据为该索引上全部函数。 |
| 12 | `cartesianPhysicalState_inner` — `:23` | PASS；状态 Hilbert 内积与原 `cartesianPhysicalInner` 精确相同。 |
| 13 | `cartesianPhysicalControl_inner` — `:27` | PASS；控制 Hilbert 内积与原 `cartesianControlPhysicalInner` 精确相同。 |
| 14 | `cartesianPhysicalControlExtension` — `:33` | PASS；通过节点线性等价将原零延拓提升为控制 Hilbert 空间到状态 Hilbert 空间的连续线性映射。 |
| 15 | `cartesianPhysicalControlRestriction` — `:41` | PASS；相同方式得到真实全状态至 ω 内节点的连续线性限制。 |
| 16 | `cartesianPhysicalControlExtension_values` — `:49` | PASS；上述连续算子的节点值与原零延拓逐值一致。 |
| 17 | `cartesianPhysicalControlRestriction_values` — `:53` | PASS；上述连续算子的节点值与原限制逐值一致。 |
| 18 | `cartesianPhysicalControl_adjoint` — `:57` | PASS；真正的 `ContinuousLinearMap.adjoint` 等于上述限制。对任意控制向量 v 和状态 f 用实际 Hilbert 配对和内积非退化性证明，不只是形式双线性伴随。 |
| 19 | `cartesianPhysicalStateWeight` — `:68` | PASS；状态空间的真实连续节点乘子，权值取实际物理节点上的 `σ(xᵢ)`。 |
| 20 | `cartesianPhysicalControlWeight` — `:73` | PASS；控制空间上的相同节点权乘法，索引取子类型的原节点。 |
| 21 | `cartesianPhysicalStateWeight_norm_sq` — `:79` | PASS；实际状态加权范数平方恰为此前 `cartesianWeightedNodeEnergy`。 |
| 22 | `cartesianPhysicalControlWeight_norm_sq` — `:84` | PASS；实际控制加权范数平方恰为此前 `cartesianControlWeightedSq`。 |
| 23 | `allowed_weight_cartesian_hilbert_observation` — `Spatial/CartesianHilbertObservation.lean:14` | PASS；全部原状态的真实重构观察范数受同一零延拓 B 的真实 Hilbert 伴随之控制加权范数控制；常数和网格阈值的量词顺序、两符号及全部允许权统一性保持。 |

固定原始 `axioms.txt` 中，上述完整类型分别从第 24623、24625、24628、24631、24634、24637、24640、24646、24650、24654、24656、24659、24662、24666、24673、24680、24684、24688、24693、24701、24709、24713、24718 行开始，均有相应递归公理打印记录。

## 真实 Hilbert 结构与范数

`PhysicalFiniteSpace` 只从函数类型复用 `AddCommGroup`、`Module` 和节点值；其 `NormedAddCommGroup` 在第 47 行由刚构造的 `InnerProductSpace.Core` 生成，随后第 51 行构造匹配的 `InnerProductSpace`。独立核对锁定 mathlib 的 `Core.toNormedAddCommGroup`，其范数定义正是 `sqrt(re ⟪f,f⟫)`。因此这里实际使用物理质量范数，没有复用函数空间的 sup 范数。

第 54 行通过 `valuesEquiv` 的单射性得到有限维性，第 58 行由有限维实范数空间的完备性得到 `CompleteSpace`。有限维与完备资格均内部供应，真正的 Hilbert 伴随不依赖新增假设。上述实例虽未另计入 23 项显式命名清单，已直接阅读其源码并包含在全环境递归审计中。

正定性没有要求索引非空：当索引为空，函数空间只有零向量，`funext` 证明仍成立。维数零的 Cartesian 质量是空乘积 1；控制节点为空或某方向无内部节点亦与空平方和一致。原文 `d≥1`、`Nᵣ≥2`、`δᵣ>0` 全部包含，未加非空控制、正控制测度或节点数量下界。

连续线性映射的构造使用有限维自动连续性，只用于形成合法 Hilbert 算子。最终估计没有使用任意有限维范数等价或算子范数上界；所有质量和权乘子等式均精确，故没有潜藏随网格或节点数增长的常数。

## 实际控制、伴随与观察界

直接检查 `CartesianNodalControl`：控制索引为 `{a // x_a ∈ ω}`，限制读取 `f a.val`，零延拓在该子类型外严格为零。原配对证明仅删除这些真实零项并用子类型有限和重索引，两个空间均带同一 `∏δᵣ` 质量。因此 `cartesianPhysicalControl_adjoint` 调用 mathlib 真实 `adjoint_inner_right`，对每个独立 v、f 得到 `⟪v,B†f⟫_U=⟪Bv,f⟫_X=⟪v,restriction f⟫_U`，由内积非退化性推出真实算子相等。不存在混用不同内积或暗中添加质量矩阵逆的问题。

状态权和控制权都乘 `σ(xᵢ)`，其平方范数因而是 `σ(xᵢ)²fᵢ²`；没有将平方权测试算子与加权范数乘子混淆。定义允许任意 σ 是更一般的精确恒等式；最终允许权本身严格正。

独立阅读 `AllowedCartesianObservation`、`CartesianObservationLocalization`、`AllowedCartesianKuhnStability`、`Observation` 的实际证明：

1. 紧包含 `closure ω₀ ⊆ ω` 内部给出正缓冲半径 r 及 `h₀=r/(d+1)`。实际非零 Kuhn 帽函数把节点与观察点放在同一真实单元，距离 ≤d h，从而 ω 外节点在 ω₀ 上的帽函数为零。该逐点恒等覆盖任意完整状态。
2. 真实重构的 a.e. 身份将该恒等变为区域指示乘子后的 L² 类恒等；`σ.observation` 正是实际加权重构在 ω₀ 上的 L² 范数，其平方积分身份已核对。
3. 已有实际允许权质量界控制筛选节点后的重构范数。原轮廓的紧凸域 Lipschitz 界产生统一 `W=exp(Ld)`，此前可取平方能量常数 `W⁴(d+2)`；这里沿用其平方根，不新增网格相关常数。
4. 本批仅以已证 `B†=restriction` 和精确控制权范数平方身份改写该结论。`sqrt(‖u‖²)=‖u‖` 使用范数非负，平方根方向及幂次正确。

最终命题先固定开凸有界环境域 S、原光滑轮廓和观察区域，再选 `h₀,C>0`，之后才量化所有平移、正步长、有限网格、嵌入 `Ω_g⊆S`、h、时间权 w、指数 τ、时刻 t、符号 η 和完整物理状态 f。条件只有 `0<h≤h₀`、`δᵣ≤h`、`h q(t)≤1`、`|η|=1` 及原几何/轮廓条件。原矩形实例取 `S=Ω_g=Ω`；原 `h q_max≤δ_num≤1` 蕴含所需时刻条件。此观察步骤不需要步长下界，未收紧原可比条件。η 包含两符号；τ 全实数覆盖原范围；常数先于整个 TimeWeight，故周期 T 一致性保留。未使用周期性或时间导数只是此固定时刻结论的加强。

## 依赖与公理审计

三个新模块的递归 `Carleman.*` 源码导入闭包共 **312** 个文件，其中 **309** 个既有文件与基线逐字不变。新三模块均在固定根目标 `Carleman.lean` 中导入。新增源码没有 `sorry`、`admit`、`axiom` 或 `native_decide`。原内积/节点能量、实际重构和观察证明先于本批，新的 Hilbert 实例与伴随再用于最终观察改写，无调用后续 T107 结果或循环假设。

`AGENTS.md`、`governance/PROJECT_OPERATIONS.md`、`state/README.md`、原论文、工具链与 mathlib 锁定文件均与基线一致。全环境递归公理检查器的实现亦未改；其遍历包括自动生成实例及投影，不只检查显式清单。

实际产物中 23 项都有完整类型及公理记录。全文件可见 2155 个带公理的打印记录（2151 个不同名称）及 8 个无公理记录，所有依赖只包含 `propext`、`Classical.choice`、`Quot.sound`。打印记录数量不等于全环境总声明数；最终递归审计明确通过 **6406** 个 Carleman 声明，无新增非基础公理。

## 同 SHA CI 与原始产物

验收者自行读取 [main CI run 39195706077 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39195706077/attempts/1)，其事件为 main 的 push，`head_sha=337d9c1b8c5fadce4e638a2c96311e230ee94bb1`，最终状态 **completed/success**，API `updated_at=2026-10-19T03:42:15Z`。

| Job | ID | 最终状态 |
|---|---:|---|
| `state-check` | 117877899745 | completed / success |
| `lean` | 117877900011 | completed / success |
| `dashboard / snapshot` | 117878560075 | completed / success |

两份原始 artifact 由验收者通过 `gh run download` 独立下载：

- **12160784770**，`lean-ci-result` → `/tmp/carleman-fd-physical-spaces-main-ci/result.json`。
- **12161397674**，`lean-declaration-evidence` → `/tmp/carleman-fd-physical-spaces-main-axioms/axioms.txt`。

实际 `result.json` 为 `status=PASS`，`checked_sha` 与 `source_head_sha` 均为上述完整固定 SHA，目标为 `Carleman`，`finished_at=2026-10-19T03:41:00.254959+00:00`。Lean 为 **4.35.0**，Linux 构建提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib 为 **56a005855ea17e0b0958f73ec801ae140b0a1679**，与固定配置及本机阅读的 mathlib 源码版本一致。

远端 `axioms.txt` 与固定 `/tmp/carleman-fd-physical-spaces-local-axioms.txt` 已独立逐字节比较，完全相同：**1,908,614 bytes**，SHA256 **`fad17c6d867e1d9e2f8820bde6e48524f85c3bcdae5c68575a24f84287a05c13`**。固定 `/tmp/carleman-fd-physical-spaces-full.log` 实际记录全库 **3821 jobs** 成功及 **6406** 项递归审计通过。本次使用固定产物，不使用后续工作区 `.ci/axioms.txt`。

## 最终范围判定

**23/23 PASS；无需要修复的数学、类型、统一量词、公理或版本绑定缺陷。** 本批完成原全部物理状态/控制 Hilbert 空间、精确质量和加权范数、真实零延拓/限制及 Hilbert 伴随，并以同一伴随表述真实全允许权观察界。

本批不宣称已经完成重构与质量算子的 Hilbert 伴随统一接口，也不把后续刚度、近似、测试等数据的全部组合视为已完成。C122 保持 **AUXILIARY**；完整 FD / P012 不升级，原文覆盖保持 **14/26**。
