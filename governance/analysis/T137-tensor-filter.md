# T137：完整原 Proposition 7.8 的实际 Cartesian 粗网格界

原文 `prop:filter-fd` 的对象是零边界粗节点全部数据的张量分片线性插值像；物理质量为原对角质量，刚度为原2d+1点差分，常数严格12∑Hr⁻²。本阶段没有用任意保留子空间或预设能量界替代它们。

`linearRefinementBasis` 是T136真实一维插值作用于单个粗节点Kronecker数据。`tensorLinearProlongation` 对全部粗内节点的值乘这些一维基函数之积求和，正是原张量插值。节点恢复通过乘积Kronecker性质；每个边界面为零；对任意坐标r，分离该方向基函数并用实际插值与有限线性组合交换，得到坐标截面等于该截面粗节点值的一维插值。全部其他方向节点可任意选取，未仅检查可分离数据。

`CartesianAxisSum` 用真正 piSplitAt 等价和有限Fubini分解全部细节点矩形和。截面两端为零，T136给每条线的12/Hr²界；逐其他方向求和，再逐r求和，得到全部张量插值数据的能量界。每个方向使用它自己的H_r=m_rh_r，没有各向同性假设。

`CartesianBoxValues` 把闭盒内真实零边界节点函数与旧cartesianLatticeData逐点识别：边界用原零值，内部明确构造同一原内节点索引。前向整数格点等于自然坐标update的精确身份保证最后一条边也不遗漏。`cartesianCoarseProlongation` 是到旧 CartesianPhysicalState 的真实线性映射，全部粗内节点函数均为输入；该空间内积仍是∏h_r倍节点平方和。

`cartesianCoarseProlongation_mass` 用零下边界把整个矩形和精确变成原内节点质量，`cartesianCoarseProlongation_energy` 使用已验收原差分算子配对边恒等式和上述真实节点身份。由此不经过质量等价常数就直接得到原细算子的能量界。实际F是映射range，原filterRayleigh的supremum上界由C151的能量引理应用于每个实际range元素得到；原细算子无须保持F。

`fd_coarse_filter_rayleigh` 先以N=mK陈述全部嵌套网格，`fd_dividing_filter_rayleigh`另外直接接受原每轴整除条件m_r∣N_r，内部取K=N/m并输出原细空间上的映射、逐节点张量公式和同一Rayleigh界。正m和正h正是实际粗细步长；K=0或1、粗空间为零、维数0均允许为更强退化情形，原正盒不受限制。

六模块27声明：定向3522 jobs、全库3941 jobs；7042个声明递归公理审计PASS。固定 `/tmp/carleman-t137-tensor-local-axioms.txt` 2165149bytes，SHA256 `cbb193ef1348054e358a3ed155a500878483f0f187abee4577b3f62accbca0a1`。申请完整P020/PAPER独立验收，通过前完成数15/26。无新增数学公理，无H²正则或连续CE作为输入。T136是本阶段新一维依赖，需先独立验收；旧差分物理对象与C151取supremum引理在固定版本继续核对。
