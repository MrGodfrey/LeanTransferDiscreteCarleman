# T156 / C172：原闭区间 C² 时间权的周期延拓与盒估计

本批消除此前要求时间权全实线 C² 周期的范围限制，接入原 `paper/main.tex:292–299` 的闭区间 C² 与零至二阶端点匹配。三模块五声明；状态仍全时空 C∞ 周期零边界、区域仍坐标盒，因此仍 AUXILIARY，不提升 P024 或17/26覆盖。

`exists_continuous_periodic_extension` 用实际 AddCircle 周期商及 Ico 基本域延拓连续且端点相等的函数，证明全实线连续、周期及在整个 Icc 上相等（右端点由端点匹配补上）。`periodic_primitive_of_interval` 用实际积分构造原函数；区间 FTC 和原函数端点匹配证明一个周期上的导数积分为零，周期积分恒等式再给全实线原函数的周期性。实际 HasDerivAt 由 FTC 给出。

`exists_periodic_C2_extension` 输入 ContDiffOn ℝ 2 q (Icc 0 T) 以及 q、真实 derivWithin q、真实二次 derivWithin 的端点匹配。先将连续二阶导数延拓成 R；积分得到 P，精确恢复区间 q′，且 P 周期、deriv P=R；再次积分得到 Q，恢复 q，且 Q 周期、deriv Q=P。因此 Q 为全局 C²，值和一二阶实际全导数都与原区间值/内导数一致，包括两个端点。没有假设另给光滑代表、周期延拓或导数字段。

`boxTimeIntegral_congr_on` 处理真实柱测度下区间相等的函数；`box_interval_C2_gaussian_heat_both_signs` 内部构造上述 Q，供应原 qclass 的全部导数界，调用已得全局 C² 权估计，并将全部四项实际积分严格换回原 q。观察项仅按空间示性集合分支。c/λ/β/qc/C 均沿用既定值，先于 T/q/ε/u，延拓不改变任何常数、权指数、残差或观察区域。

此阶段完整恢复原时间权的有限正则性及端点条件，但未扩展全部弱轨道或一般凸多面体。原稿不改。目标3308 jobs、根目标4039 jobs、7621声明递归公理审计通过；固定 SHA 另需独立 Agent 与同 SHA 三项实际 CI及raw比较。
