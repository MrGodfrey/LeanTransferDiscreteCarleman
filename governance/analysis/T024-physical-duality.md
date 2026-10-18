# T024 — 原 Lemma 7.1：物理时间适定性、能量与精确对偶

目标是 `paper/main.tex` 的 `lem:physicalduality`（1753 行起）。最终入口 `Carleman.Physical.physical_duality_lemma` 给出一份合取：任意初值与控制的前向唯一解、任意末值的伴随唯一解、任意 j≤ell 的原反向稳定界、统一控制 L2 能量界、原精确对偶恒等式。

## 原数据与真实方程

N 个控制步为 Fin N，N+1 个物理状态节点为 Fin(N+1)。第 i 个步是原 n=i+1；i.castSucc 对应 n−1，i.succ 对应 n。没有循环回绕或周期状态约束。

`ForwardEquation` 是 dt⁻¹(y^(n)−y^(n−1))+(A+V^n)y^n=B u^n；`AdjointEquation` 使用实际 Hilbert 伴随 `(A+V^n).adjoint`，正是 dt⁻¹(p^(n−1)−p^n)+(A+V^n)*p^(n−1)=0。中间 `Forward/Adjoint` 是乘 dt 后的代数形式，由已证明 iff 无损连接。原 A 与 V 自伴保证原伴随等于自身，但最终方程仍明确使用实际 adjoint。

Section7 给出的 X 有限维、A 自伴非负、V^n 自伴且范数≤M、B 范数≤1 是最终输入；M≥0。U 可为原 L² 控制 Hilbert 空间，无有限维条件。有限元/差分的具体算子构造仍属于其各自未验收的实现结果，本阶段不宣称已完成那些实例。此处证明对所有满足 Section7 算子性质的空间/算子成立。

## 适定性和能量

单步 `step dt L=Id+dt L` 的二次型下界由非负刚度与真实势的范数界推出 −M‖x‖²。Cauchy–Schwarz 得 `(1−dt M)‖x‖≤‖step x‖`；dt M≤1/2 保证单射，有限维使其满射。`Fin.induction` 与 `Fin.reverseInduction` 在原完整状态空间递推构造解并逐步证明唯一性。

利用 exp(2r)≥1+2r 与 0≤r≤1/2，直接证明 `(1−r)exp(2r)≥1`，得到真实逆步范数≤exp(2dt M)。对伴随轨迹证明 exp(2dt M n)‖p^n‖ 随 n 单调，恰得

`‖p^j‖≤exp(2M(t_ell−t_j))‖p^ell‖`。

前向证明先建立真实有限前缀控制范数的离散递推，再用 Cauchy–Schwarz 得 `dt Σ‖u^n‖≤sqrt(T) sqrt(dt Σ‖u^n‖²)`。最终可取

`C(T,M)=exp(2MT)(1+sqrt(T))>0`。

C 在 X/U、A/V/B、N、dt、初值与控制之前选定；通过 g.period=T，未保留 N、维数或 ‖A‖ 的常数依赖。对所有节点 n 的同一界等价于原有限节点最大值界。

## 精确对偶

对每一步，从两个实际方程和 L 自伴得到

`(y^n,p^n)−(y^(n−1),p^(n−1))=dt (Bu^n,p^(n−1))`。

有限和严格望远镜消去，真实 B 的 Hilbert 伴随给出原 `dt Σ(u^n,B* p^(n−1))`。未替换为 p^n、未加入余项，内积均为原 X、U 内积。

## 状态

六个新模块由 root 导入，完整声明加入实际类型与全环境递归公理审计。正式 PAPER 完成必须等待固定提交真实 main CI 与独立 Agent 验收。本说明仅为映射，不代替验收。
