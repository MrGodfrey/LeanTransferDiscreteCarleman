# T205 — 原控制极限的真实初终值

基线 `7afc739b6c8f95e208beeaefed4b955f0eebbdb5`。原文 `paper/main.tex:2395–2415`，特别是第 2415 行利用不限端点的测试识别 y(0)=y0、y(T)=0。2 模块 6 声明；AUXILIARY、17/26。整个 P021 仍需与实际控制弱积聚定理组合及覆盖一般空间分支。

标量 `scalar_affine_green` 从真实弱 H¹ 身份推出绝对连续性，再用实际 a.e. 导数和绝对连续积分分部给 ∫(f+(t-c)df)=(T-c)f(T)+cf(0)。`scalar_endpoints` 用 c=0、真实弱 FTC、T>0，将 a+∫df=0 与 ∫f+∫t df=0 转为 f(0)=a、f(T)=0。涉及每个积分的可积性均由实际 L² 资格及连续时间乘子供应。

`continuous_pairing_weak` 把原真实质量弱导数作用到 innerSL w，并用原 q=EY 的 a.e. 身份、E*E 伴随配对，得到 f(t)=〈q(t),Ew〉 的真实标量弱导数 df(t)=〈D(t),w〉。其中 D 是同一 Y/U/b 的 dirichletTimeLoad。`continuous_pairing_test` 将原 all-energy-tests 导出的质量测试等式通过实际 tensor/toLp 代表改写为 q 的积分等式；η 在两个端点均不受限制。

`continuous_H_endpoints` 对任意原能量方向 w 使用 η=1 和 η=t，分别提供上述两项标量积分身份。真实 q 的 H 连续性使其标量配对在整个闭区间连续；标量端点定理因此得到 〈q(0),Ew〉=〈y0,Ew〉、〈q(T),Ew〉=0。最后使用原 Dirichlet 值域在 H 的真实稠密性和内积连续性，扩展至每个 H 方向并分离向量，给 q(0)=y0、q(T)=0。

`continuous_H_trace` 直接组合 T204 的真实连续代表，返回同一原 Y 的 q：闭区间 H 连续、q=EY 几乎处处、q(0)=y0、q(T)=0。没有使用任意 Lp 代表的端点值，没有把零测端点假设变成终值，没有替换状态、控制、势或初始数据。原 open/finite-measure 域与 T>0 前提保持；内部一步 TimeGrid 不施加周期端点条件。

原文第 2415 行的连续性与初终值身份至此在实际完整 Dirichlet 弱控制恒等式下得到证明；实际盒 FD 控制族及任意弱积聚的最终整合留到下一阶段。原稿不改，原控制成本的 T 统一性保持，未添加新的控制预算。
