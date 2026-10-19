# T162 / C178：带实际经典微分字段的完整弱周期图逼近

本批将 T161 的光滑代表逼近加强为显式经典字段身份。五模块十三声明；任意原正盒弱周期轨道都有同一列实际全时空光滑、严格周期、全时间全边界零值函数 F_n，以及原周期图 P_n→p。除每个闭时间区间时刻的真实 Lp 迹外，对几乎每个时间，其两个实际 Bochner 字段在原空间测度下分别 a.e. 等于 F_n 的经典时间导数和负空间 Laplacian。

SmoothDifferentialLinearity 用真实 Fréchet 微分的加法和常数乘法证明 directionalLap 的线性规则，并识别真实 cos/sin 乘空间函数的时间微分及空间 Laplacian。HarmonicGraphFields 从原 harmonicTrajectory 的 MemLp.toLp 代表身份读取同一轨道的导数字段，借原真实 domainRepresentative 和算子线性性识别算子字段。没有假设某个抽象残差等于经典残差。

ClassicalDirichletTimeCore 在原完整周期图内定义更强的真实子空间。一个共同 F 同时具有光滑、周期、边界、迹和两个微分字段身份。零、加法、实乘封闭性使用外层时间 Lp 与内层空间 Lp 各自的 a.e. 代表规则及真实经典导数线性性，保留两个 a.e. 层次，没有将 Bochner 类代表当作逐点函数。

ClassicalHarmonicTimeCore 显式构造原两个 SpatialTest 系数的 cos/sin 组合。系数的值和算子投影分别是原函数类和真实负 Laplacian 类，内部计算得到该同一 F 的真实时间导数及负 Laplacian，逐项核对所有负号。全部字段身份与原实际周期轨道兼容，而非为 F 任意指定一对导数组。

BoxClassicalTimeDensity 重新应用已验收/构建的完整谐波密度转移接口，并同时使用 T160 的 graphH 和 graphA 身份。因而较强的经典子空间也在完整弱周期图中稠密。最后选取同一个序列，并用真实 spaceTime_timeD 和 spaceTime_directionalLap 将中间方向微分明确换成 deriv(fun s=>F_n(s,x)) t 和 -spatialLaplacian(fun y=>F_n(t,y)) x。

此处覆盖任意原弱周期轨道；原轨道不需要全时刻算子域归属、光滑时间代表或给定逼近序列。逼近使用的 T、频率相关常数不进入原 CE 常量。尚需将空间梯度、加权 Bochner 范数和实际柱积分对应，并传递已有光滑 CE 至全部弱轨道；一般凸多面体仍待。保持 AUXILIARY、P024 不提升、覆盖17/26，原稿不改。

定向3502 jobs、根目标4067 jobs通过；7799项递归公理审计通过。固定 raw 2433363 bytes，SHA256 df4daf04c607a2ea591d71656fa19d93465458b8ac1c32564d232e51c850336e；同SHA真实三项CI和独立验收另行登记。
