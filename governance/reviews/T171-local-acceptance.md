# T171 / C187 独立本机验收：原终端滤波条件与 Cartesian 物理滤波观测

- checked_sha / source_sha: `f6e35f26cc23e5ca84eb8e869a12864be70e7b27`
- mathematical_base: `3a752bc986ef1a893825b6597211ccb519d8a292`
- reviewed_at: `2026-10-19T13:44:33+00:00`
- reviewer: 独立本机数学验收 Agent `/root/accept_spatial_foundations`
- result / axiom_check: **PASS / PASS**；全部 **3/3** 显式声明通过。
- scope: **AUXILIARY**；C187 可在本批范围登记 REVIEWED，原文覆盖保持 **17/26**。完整盒 Cartesian 滤波观测不自动完成一般几何的原定理或滤波控制。

## 固定源码与原文

本报告直接读取固定 Git 对象中的两个新模块、三个完整展开类型、实际调用的关键依赖，以及 T171 分析、MATH_SPEC、固定台账与根审计配置。AGENTS、PROJECT_OPERATIONS、state/README、MILESTONES、PAPER_COVERAGE 与本 Agent 已读 T168 版本逐字节不变，继续适用。后续 T172 等工作树源码、动态根导入及动态 `.ci/axioms.txt` 不作为证据。

原稿核对 `paper/main.tex` 的 filtering 小节（约 2135–2195 行）及 Appendix C 的反向范数证明（2962 行起）：原 C0=max{1,C(T,M)}、真实 Rayleigh 商上确界、两个滤波条件、仅终态属于 F、指数 K_F 及最终 2C0 观察常数均逐项核对。固定原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

签发前已完整读取独立 [T170 报告](T170-local-acceptance.md)，报告提交 `da95f786af0ae582fcc4fa9ba22d0bd4b1f84b4c`，checked SHA 与本批 mathematical_base 完全一致，reviewed_at=`2026-10-19T13:36:55+00:00`，3/3 PASS。固定 T171 台账中的 C186 当时仍是 BUILT/PENDING；本报告依明确版本的后续独立验收补齐门槛，没有把该旧状态误读为已验收，也没有修改总台账。

## 全部声明与逐项结论

顺序与固定 manifest、C187 和 T171 清单一致。源码位置相对于 `Carleman/Control/`；raw 行为本批固定完整声明输出的起始行。

| 序号 | 声明 | 固定源码 | raw 行 | 判定 |
| --- | --- | --- | --- | --- |
| 1 | `Carleman.Physical.filter_condition_budget` | `FilteredObservation.lean:10` | 33115 | 原两个条件精确推出 4C0 exp(-2dS)K²≤1。PASS。 |
| 2 | `Carleman.Physical.filtered_observation_of_relaxed` | `FilteredObservation.lean:28` | 33121 | 真实反向估计代入明确的松弛观测前提，吸收终态余项并得原 2C0 观察界。PASS。 |
| 3 | `Carleman.Physical.box_cartesian_filtered_observability` | `BoxCartesianFilteredObservation.lean:15` | 33149 | 原完整 Cartesian 物理对象内部供应松弛观测，保留原滤波条件及参数顺序。PASS。 |

### 1. 原两个条件与精确预算

第一个声明量化任意实 T、M、Λ、θ、d、S、C0，只要求 C0≥1 和两条原不等式。实际 `filterConstant T M Λ = exp(TΛ+MT+M²T²/2)`。由两条件相加得到

`log(4C0) - 2dS + 2(TΛ+MT+M²T²/2) ≤ 0`。

C0≥1 内部保证 4C0>0，故 `exp(log(4C0))=4C0`，并用 `exp(a+a)=exp(a)²` 得到声明中的精确预算；没有将 K 的平方误写成 K，也没有遗漏对数项的 1/2。此纯代数引理不需要另加正性或 θ∈(0,1)，比原适用参数范围更宽，并完整覆盖原假设。

### 2. 真实反向估计、终态限制与余项吸收

通用声明以实有限维 Hilbert 状态 X 和任意完整实 Hilbert 控制空间 U 为对象；没有要求 U 有限维。A 是实际连续线性算子，保留对称、非负条件；各 V_i 是实际对称算子，‖V_i‖≤M。它明确保留 `hobs`：对所有原物理伴随解，初态平方由实际 B* 观察和 `exp(-2dS)` 终态平方控制。这一抽象辅助声明本身不声称证明 hobs。

重新读取 FilterReverse、ReverseIteration、PositiveResolvent、RayleighStep 的真实证明及 PhysicalEquations。`filterRayleigh A F` 对 F=⊥ 显式取 0，否则是非零 F 元素的真实商 `⟨Ax,x⟩/‖x‖²` 的上确界。‖A‖ 只用于证明该集合有上界，不进入最终 K 或任何统一常数。非零终态的商由所属 F 给上界，零终态单独处理，因此 F={0} 及零维状态空间都没有除零缺口。

反向证明在完整状态空间上迭代实际方程；一步 Rayleigh 增长至多 dt M²。其范数步采用输入状态的 Rayleigh 商，累积后得到 `TΛ_F+MT+M²T²/2`，没有节点数、‖A‖ 或额外 T 因子。正 resolvent 下界直接由非负二次型证明，有限维仅用于可逆性，不供应隐含统一范数等价。

唯一的 F 限制是 `p (Fin.last steps) ∈ F`。未要求任何中间 p_i∈F，也未要求 A、V_i 或步算子保持 F。原 `dt*M≤1/2` 保留，M=0 允许。

通用证明把正 K 的范数反向界平方，以非负 C0 exp(-2dS) 相乘，再把预算乘以 ‖p0‖²，严格得到终态余项≤‖p0‖²/4。与 hobs 和非负观察项合并，得到原 `2*C0*dt*Σ‖B* p_i‖²`；没有通过改变终态、投影轨道或更换物理方程吸收。

### 3. 同一 Cartesian 对象、参数次序与完整实例

最终声明固定正维坐标盒（维数 d+1）、非空开 W⊆盒、开 ω 且 closure W⊆ω，以及 ratio≥1；随后选择 qc、κ、h0、Δ0、Cb、d0。六个参数先于 T、M。再对每个 T>0、M≥0，从 T170 取得 C(T,M)>0，并选择 **C0=max(1,C(T,M))**；C0 先于全部 o、δ、N、h、时间网格 g、节点势 b、θ、F 和轨道 p。

这里 C0 允许依赖 T、M，正是原稿 `9.26-eq15` 的顺序；不能把本结论误记成 C0 对 T、M 也统一。δ 每轴为正、原盒域等式、h/ratio≤δ_j≤h 及 h≤h0 均保留。没有先固定某张网格再选择 C0。

原尺度 `Smax=κ min(h^(-4/5),dt^(-2/5))` 与 `qb=Cb(qc+T⁻¹+M^(2/3))` 使用同一依赖中的定义。原两侧 `16qb≤Smax≤qb*T/(4dt)`、dt≤Δ0、dt≤T/12 和 dt M≤1/2 完整保留。两个滤波条件仍以实际 Cartesian Laplacian 的 Λ_F 和同一个 d0、Smax 表述。

源码在给定 T、M 后把原观测 C 提升为 C0；乘子的整个右侧由平方、正指数和 dt>0 保证非负。随后实际调用 T170 `box_cartesian_physical_observability`，再调用通用吸收声明；最终类型没有 hobs、CE、载荷稳定性、A 的对称性/非负性或任意替代观察假设。

重新读取物理空间和控制定义：X_h 是全部内部节点值配实际质量内积 `(∏δ_j)Σ f_a g_a`，U_h 是 ω 内节点的同质量 Hilbert 空间。B 是实际零延拓，其 Hilbert 伴随精确等于节点限制；不是任意线性观察。`B*B=id` 给 ‖Bv‖=‖v‖，计数 L² 等距 E 又给 `‖E B B* x‖=‖B*x‖`，所以依赖中的观察项确实恢复到原 U_h 范数。节点索引为空也未增加 Nonempty 前提。

A 由原 (2d+1) 点差分公式定义；实际边能量配对给对称与非负。V_i 是实际节点乘子 b_i，假设只为每个节点 |b_i(a)|≤M；物理质量内积的对称性和相同 M 的算子范数界在内部供应。虽用有限维自动连续性构造 CLM，其未知连续性常数没有进入估计；所用 M 界有独立真实范数证明。

`AdjointEquation dt L p` 展开为 `dt⁻¹(p_i−p_(i+1)) + L_i.adjoint p_i = 0`。i.castSucc 对应论文 p^(n−1)，Fin.last 对应 p^N，求和覆盖全部时间步，前面保留 dt。最终量化所有完整物理轨道，只在终态要求属于任意 F，没有周期性、低频轨道或光滑性限制。θ 量化任意实数且保留两条件，因此包含原 0<θ<1 范围。

## 依赖版本与公理

递归解析两个模块实际 `Carleman.*` 导入，共 **762** 个模块；除两个新增模块外的 **760** 个旧模块全部与 mathematical_base 逐字节一致。另对关键入口与其已验收版本比较整个导入闭包，均无变化：

| 依赖入口 | 固定接受版本 | 闭包模块数 |
| --- | --- | --- |
| FilterReverse / C041、T025 | `12d18c9c6548cc70165ad9e4c01314f4438dc5f1` | 11 |
| BoxCartesianObservation / C186、T170 | `3a752bc986ef1a893825b6597211ccb519d8a292` | 756 |
| BoxCartesianLoadCarleman / C185、T169 | `7d1cc86d3c0a01b524f099ba90baaf59784f159d` | 752 |
| PhysicalFiniteWeights / C184、T168 | `30a03e32af45ef82baacbbfe6917cd7ceff234f3` | 44 |

T170 的明确版本独立报告已在本次正式签发前读取；该报告同时记录已接受 T169 报告提交 `cf033f11dc66ebab3c8a083ed3db516cb1d78183`。上述依赖比较和关键实际证明阅读是本次独立执行，未仅用执行者说明替代数学核验。

固定根导入包含两个模块，CheckAxioms 对三个名字分别 `#check @...` 和 `#print axioms ...`。三个新声明都只依赖 `propext, Classical.choice, Quot.sound`。独立解析 raw 中 **3071** 条显式公理记录（3067 个不同名字，其中 9 条无公理记录），没有白名单外依赖；新源码无 sorry/admit/axiom/native_decide。末尾真实 `collectAxioms` 审计遍历全部 Carleman 声明并还原私有名字，输出 **8099 项递归审计 PASS**。

实际读取定向 `/tmp/carleman-t171-box-filter-target2.log` 的 **3992 jobs** 成功、固定 `-build.log` 的 **4099 jobs** 成功；`-axioms.log` 为 0 bytes，仅是空 stderr，未用它代替审计结论。没有重建未来工作树来冒充本批验证。

Lean pin 为 `leanprover/lean4:v4.35.0`，实际 CI 编译器 commit 为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib 固定及本机干净 HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。已读取固定 CI 工作流，其 Lean checkout 精确使用 github.sha，结果和声明工件由同次任务上传。

## 独立 CI 与原始工件

本 Agent 自行查询实际 GitHub API，并分别以 `gh run download` 下载同次 `lean-ci-result` 和 `lean-declaration-evidence`，两个下载均 exit 0；未使用 root 下载副本代替独立取证。

- run: [39261882332 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39261882332/attempts/1)，event=push、branch=main、head_sha 精确等于 checked_sha；最终 completed/success，API updated_at=`2026-10-19T13:42:01Z`。
- 三项 jobs：lean **118091374402**、state-check **118091374403**、dashboard / snapshot **118092989262**，均 completed/success。曾观察到 dashboard 仍运行，之后重新查询确认最终成功才签发。
- `lean-ci-result` artifact **12190138560**，ZIP 492 bytes；API digest `sha256:02f82aba988630590cf0d5d8ae392699cbc95580e886db3b686413edf9c7e876`。
- `lean-declaration-evidence` artifact **12190338449**，ZIP 235517 bytes；API digest `sha256:bbeeb074b270cc02da681f8a78cc7918a56360099a7044fb8b0584c99398d4b2`。
- 两工件 workflow_run 均绑定本报告的 main、run 和精确 SHA；ZIP digest 与解包后的 raw digest 分开记录。

独立 result 路径 `/tmp/carleman-t171-cartesian-filtered-observation-main-ci/result.json`，537 bytes，SHA256 `f062a9c58dea00e678b2fbbf8576f00d6c5e86b8da382087a7cefd3ceaa864d1`。实际内容 status=PASS、checked_sha=source_head_sha=`f6e35f26cc23e5ca84eb8e869a12864be70e7b27`、targets=[Carleman]、finished_at=`2026-10-19T13:40:43.619993+00:00`；ci_url、Lean 和 mathlib 字段均与上述证据一致。

独立 raw 路径 `/tmp/carleman-t171-cartesian-filtered-observation-main-axioms/axioms.txt` 与固定 `/tmp/carleman-t171-cartesian-filtered-observation-local-axioms.txt` **逐字节完全相同**：**2540654 bytes**，SHA256 **`cacb14043c6cb78528a83b3938b32d2327273ed23f495219622b6fa834b78a8e`**。完整类型、公理集合和最终 8099 项递归成功记录均由该固定 raw 实际读取。

## 最终判定

**3/3 PASS，未发现阻断缺陷。** 原两个滤波条件、真实反向范数界、仅终态所属 F、原物理 B* 和完整 Cartesian 盒实例全部衔接；C0(T,M) 对网格、势、θ、F、轨道统一。通用 helper 的 hobs 明示，完整盒实例已内部清偿。C187 可登记 AUXILIARY/REVIEWED，保持原文 **17/26**；本批没有证明滤波控制、一般几何或 P1 的完整对应结论。本报告仅单文件提交，不 push，不修改实现、原稿或台账；通知后 reviewed_at 与正文冻结。
