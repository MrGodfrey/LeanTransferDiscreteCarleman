# T231 — 实际解析边界坐标及其导数互逆

基线 `721b761224ad1b6425466bc956417ddce7f41908`。原 Corollary A.2 一般凸多面体正则性路线中，T230 指数和内域的边界坐标。AUXILIARY、18/26，内域 PDE 正则与统一二阶界仍待。

对实际全空间解析 g 和 Dg(c)≠0，实值线性泛函的非零性给满射，有限维值域给 kernel 的实际连续补投影。使用 mathlib 真实隐函数定理生成 e₀:E⇄ℝ×ker Dg(c)，其第一坐标严格等于 g，第二坐标为补投影(x−c)，c 映到 (g(c),0)。正向是实际解析函数；隐函数定理给逆在该点解析。利用解析阶 ω 的局部持续性选真实开邻域 W，再限制逆映射的源并取逆，得到真正局部可逆图 e，逆在整个 e.target 解析。没有把 C∞ 点处的逐阶邻域误当作一个统一 C∞ 邻域；这里实际证明较强的解析性并使用 ω≠∞。

图限制不改变正向/逆向的实际函数。原全空间第一坐标身份仍成立；目标中所有 y 都有 g(e⁻¹y)=y₁。halfspaceExpSum_analytic 从真实仿射函数、exp 和有限和直接证明原 gₙ 的解析性，没有假设内域已有解析图册。

level_chart_image_sublevel 证明原源内的严格子水平集精确映到目标内半空间，两个方向均使用真正局部互逆资格。level_chart_frontier_iff 用 OpenPartialHomeomorph.IsImage.frontier 证明源中的全部原边界点恰对应 g=a；因此既不只是集合单向包含，也不是仅基点处的切平面身份。应用 T230 的实际边界值=1/2 与非零导数得到 halfspaceSmoothInner_analytic_chart，其源含指定任意边界点，正反两向解析，原整个局部边界严格平坦化，原内域精确映到半空间。

analytic_chart_derivative_inverse 对任何正反两向在开图内解析的真实 partial homeomorphism，从两方向局部互逆身份和真实 Frechet 链式法则证明每个源点的导数双向可逆，且其 CLM inverse 严格等于逆图在像点的真实导数。没有假设 Jacobian 可逆或选择与原图不相关的线性算子。

本批 6 定理不额外要求原多面体边界光滑；图属于实际构造的光滑凸内域。弱 Sobolev 状态在这些非线性坐标下的变换、边界椭圆 H² 正则性以及凸域统一 Miranda–Talenti 界是后续明确义务，P023 不提升。原稿未改。
