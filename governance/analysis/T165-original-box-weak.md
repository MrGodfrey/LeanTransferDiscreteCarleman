# T165 / C181：任意原闭区间权和原弱轨道的完整盒 CE

五模块十四声明。IntervalTimeWeight 把任意原闭区间连续且≥1的 q 组成真实 ContinuousMap，并用原 clampPath 延拓到全实轴有界连续函数；构造的 TimeWeight 在整个 Icc 精确等于 q。由 derivWithin_congr 在同一集合上逐次应用，保留值、一阶及二阶区间导数，包括两个端点。没有要求原 q 在区间外有界、正、连续或光滑；延拓只用于固定权的连续性证明。

IntervalHeatEnergies 直接对任意 q 定义真实 exp(qρ) 空间乘子的 timeSq 能量。以两层真实 Lp 代表规则证明原 multiplier(τ=0) 与 expMultiplier 的 seminorm 相同，再用原时间满测区间上的 EqOn 精确换回 q。所有能量对所选有界代表不变。BoxIntervalWeakHeat 把原 C² 区间数据的三端点条件、下界和两个导数预算逐项交给已证 T164 估计，再以精确能量身份恢复原 q；没有保留 TimeWeight 或存在延拓前提。

WeakTrajectoryHeatEnergies 对任意原 PeriodicWeakTrajectory 构造出的实际周期图，证明其梯度 Bochner 字段 a.e. 等于原 domainValue 的真实 dirichletDomainJet 一阶弱字段。证明只使用能量嵌入及真实 jet 值唯一性；由实际 Lp 类内部供应该梯度的 MemLp。原值、时间导数和算子通过原转换的真实代表身份恢复；观察使用真实 cutoff。因而左右两项和在两种表示下完全相等，没有改变梯度/残差或扩大常数。

BoxOriginalWeakHeat 最终直接量化原闭区间 C² q 和全部 PeriodicWeakTrajectory。负高斯相位、λ、β、qc、C 均先于 g/q/ε/u 选择；保留所有原时间权条件、双符号、指数(3,1;3)、同一C和全部弱状态。TimeGrid 可以取 steps=1、dt=T 实现任意 T>0，接口不限制时间长度。原域资格只有 a.e.，domainValue 在例外时间的选择不影响积分；未引入每时刻 D(A)、额外代表、给定逼近、连续 CE 或光滑 PDE 前提。

区域仍为正坐标盒而非 P024 的所有 analytic-realizations 域；后续把实际梯度接入通用 Sobolev transfer geometry 并完成具体差分端到端实例，同时继续一般凸多面体。AUXILIARY，P024 不提升、覆盖17/26，原稿不改。

定向3596 jobs、根目标4081 jobs通过；7984项递归公理审计通过。固定 raw 2472185 bytes，SHA256 15cd685b2d61987101fa4319b4c0cea22f5b7e7b0ca4b0d97e0f0b96b05efda3。同 SHA 正式 CI 与独立验收另行登记。
