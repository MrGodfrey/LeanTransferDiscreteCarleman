# T014 全空间插值完成与原域扩张检查点

原稿 `paper/main.tex:666–673` 从 bounded Lipschitz Ω 的扩张/插值及A1单向椭圆界得到parametergraph。T013留下的全空间Fourier/Bessel识别障碍，本阶段已由直接弱卷积路线绕过；不再作为这条路线的必要依赖。

## 已完成的完整链

1. `WeakConvolution`：反射核是真正SpatialTest，实际导数负号；弱测试恒等式证明u*Dκ=v*κ，实际卷积求导识别D(u*κ)=v*κ。
2. `ConvolutionL2`：sqrtκ加权Cauchy–Schwarz，卷积积分及平移保持测度，实际推出MemLp和常数1收缩；没有Young不等式占位。
3. `MollifiedInterpolation`：三条L²卷积及乘积可积；真实全空间IBP给中间导数平方界，原状态不需紧支撑。
4. `FullSpaceInterpolation`：构造归一bump序列，半径趋零且比例固定2；固定库的Lebesgue微分定理和Fatou把估计传回原弱链。
5. `FullSpaceJetInterpolation`：原Sym多重指标的同方向邻阶链、有限分量最大值log-convex、`DiscreteMaximum`，最后恢复原Euclidean全部导数字段。C在r/u之前；n=0、d=0及r=0均包含。

## 仍需原域几何证明，不能改作原定理假设

对每个固定n，需要同一个真实弱扩张 E_n:Hⁿ(Ω)→Hⁿ(ℝᵈ)，保持每阶弱字段在Ω上的限制，并有固定B₀、B_n：

- ‖value(E_n u)‖L²(ℝᵈ) ≤ B₀‖value u‖L²(Ω)；
- ‖E_n u‖Hⁿ(ℝᵈ) ≤ B_n‖u‖Hⁿ(Ω)。

全空间参数估计将给原域同形式界，再用原A1 ‖u‖H^(2m)≤Creg‖Au‖。两个有界性必须来自同一扩张；仅Hⁿ有界会使r^n乘在高阶范数上，仍不足。全空间导数字段限制是必要对象匹配，不可只给一个标量范数比较。

固定mathlib已有的标量Lipschitz扩张不是高阶弱Sobolev扩张；全空间紧支撑GNS不直接覆盖原域；零延拓强加额外边界条件；一般Lipschitz图表的高阶普通反射没有需要的高阶链式正规性。这些路线此前已核对，未作为已证结果使用。

后续可以构造保留两种界的高阶Lipschitz扩张，或建立原域有限锥覆盖、弱平移FTC和Taylor平均的局部插值。原稿与最终结论保留，不要求用户接受新边界或状态限制。

## 冻结能量独立成果及剩余右端

任意μ下界A3估计和真实barμ单元下界已完成；`FrozenEulerPair`由原A1构造，实际误差残差及N能量乘积界已完成。该路线避开能量步骤单独的空间插值，但仍需加权连续/Euler时间导数载荷界及加权误差L²。不能从T012无权12dt结论直接填写这些允许权估计；不进行μ−barμ扰动，不引入L^(2m)损失。
