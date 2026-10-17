# T013：原域参数插值的可复用检查点

原目标仍是 `paper/main.tex:666–672` 的 `eq:parametergraph`，不是仅在 H₀ⁿ、光滑边界、紧支撑状态或有限频率子空间上的版本。令 n=2m、ν=volume.restrict Ω，u 为现有 `WeakSobolevJet d n ν Ω`，所需分析核心为

\[
\exists C>0\ \forall r\ge1\ \forall u,\quad
\sum_{j=0}^n r^{n-j}\|D^ju\|_{L^2(\Omega)}
\le C(\|u\|_{H^n(\Omega)}+r^n\|u\|_{L^2(\Omega)}).
\]

随后原 A1 的 Hⁿ 图界才把第一项换成 ‖Au‖。C 只能依赖固定 Ω、d、n，不能依赖 r、T、q、L、网格或状态。

## 已具体检查的两条路线

### 同时有 L² 与 Hⁿ 界的弱扩张

缺失的几何/分析定理必须给出同一个线性算子
`E : WeakSobolevJet d n (volume.restrict Ω) Ω →ₗ[ℝ] WeakSobolevJet d n volume univ`，满足：

1. 所有 j≤n 的实际弱导数字段限制回 Ω 后等于原字段；至少 value 限制恒等加上弱导数唯一性也可。
2. `‖value (E u)‖L²(ℝᵈ) ≤ C₀ ‖value u‖L²(Ω)`。
3. `‖E u‖Hⁿ(ℝᵈ) ≤ Cₙ ‖u‖Hⁿ(Ω)`。

只有 Hⁿ 有界性不够：将它用于 rⁿ·‖E u‖L² 会重新产生错误的 rⁿ·‖Au‖。不能用逐个 u 选取无定量界的延拓。

还缺全空间真实弱 jet 的参数插值，而不是标量 Young 不等式。Fourier 路线须先证明本项目分布测试定义的字段与 Fourier 乘子 `(iξ)^α` 一致、L² Plancherel 及各阶有限 Euclidean 字段比较；再使用频率分割 `|ξ|≤r`/`|ξ|>r`。不能把 Bessel-potential 空间同名类型直接视为这里的弱 jet。

本轮在固定 mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 的 Analysis/Geometry 中检索 Lipschitz-domain / Sobolev-extension / cone-condition，并检查：

- `Analysis/FunctionalSpaces/SobolevInequality.lean` 的 `eLpNorm_le_eLpNorm_fderiv*`：输入是全空间经典 C¹、紧支撑函数及一阶 fderiv；没有上述原域全阶弱扩张或弱 jet 等价入口。
- `Analysis/FunctionalSpaces/BesselPotentialSpace.lean` 与 `Analysis/Distribution/Sobolev.lean`：定义和结论不能直接替代本项目的原域 L² 多重指标字段。
- 已存在的标量 Lipschitz 延拓只控制一阶 Lipschitz 常数，不能作为 n=2m 的 Hⁿ 扩张。

未找到可直接接入的原 Lipschitz 几何与上述同步扩张 API。检索结果不是对库中所有可能等价定理不存在的数学断言。

### 原域单侧平移、差商与锥形平均

不使用域外延拓的替代路线仍需具体完成：

1. 从原有界 Lipschitz 图表导出有限内锥覆盖，固定高度、孔径和覆盖常数。
2. 对 Ω 内可用的方向，证明真实弱字段的平移 FTC/差商，及平移后平滑逼近在全部 Hⁿ 字段中收敛。
3. 用有消失矩的单侧核构造尺度 h 的平均，得到
   `‖D^j u‖₂ ≤ C(h^(n−j)‖u‖Hⁿ + h^(−j)‖u‖₂)`，0<h≤h₀。
4. 取 h=min(h₀,1/r)，保留同一个几何常数，再处理有限覆盖拼接。

目前第1步的原几何表示和第2步的弱平移定理都未建立；本轮没有把形式上的差商符号或有限标量插值当作这些分析步骤的证明。直接高阶反射一般 Lipschitz 图表需要其所无的高阶链式正规性；零延拓会加边界迹条件；A1 粗估计会产生错误 r 幂，均未采用。

## 本轮实际绕开的两个依赖

1. **权 profile 的 C∞(闭包) 表示**：已证明坐标词导数连续延拓与完整 Fréchet 张量连续延拓等价；证明域外值改变不影响条件、内侧延拓在闭包唯一、邻域表示蕴含此条件。紧性给实际域内导数界，并接通全空间阶弱乘积、R/N 共轭和弱时间轨迹。未宣称证明 Whitney 邻域延拓，也不再需要它。原稿只使用 C∞(闭包) 记号且未定义：两种常见入口（内侧连续、邻域限制）均可用于本轮证明，未将任意闭集上的 `ContDiffOn` 与它们等同。
2. **算子域误差的加权能量步骤**：原 A3 与 A1 测试恒等式直接推出
   `c Nσ(u)² ≤ ‖σ(A+(Lq)^(2m))u‖L² ‖σu‖L²`。
   `allowed_spacetime_operator_energy_uniform` 实际证明其时空版本，L₀ 在 T、q、权、指数和状态之前选定；所有权后 L² 有限性从无权图正规性推出。这可对真正 D(A) 值的时间误差使用，不需单独的 Hⁿ→Hᵐ 乘积插值。它没有证明对全部 H²ᵐ 状态的原 `eq:weighted-interpolation`，也没有证明误差的两个右端加权估计。

## 继续的精确边界

- 原 `eq:parametergraph`、连续及 Euler 的完整统一允许权 R 图界仍未清偿。
- T012 的 12δt L² / (84/c)δt form-energy 仍是无权结论。新 N 对象和 A3 不等式没有把它们变成允许权族 B4 误差。
- 需完成原加权对偶导数界和加权仿射缺陷界，再用实际对偶恒等式取得时间加权 L²；随后新 A3 能量不等式可替换误差证明中的单独空间能量插值。
- 原 N1–N5 空间误差、全权族阈值合并与 `TransferBridges.solutions` 实质误差仍待。B2/B5、规范 B3、B4 finite/order/shift 沿用既有证明。
- 本轮没有新增论文假设或弱化最终结论；没有新增原文完成项，仍为 1/26。
