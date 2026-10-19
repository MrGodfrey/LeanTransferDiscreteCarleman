# T127：有界分布导数的真实 L² 表示及极限

本阶段为原附录的凸域 Dirichlet H² 正则性建立极限工具。已核对 Grisvard《Elliptic Problems in Nonsmooth Domains》1985版第147–149页 Theorem 3.2.1.2：其凸域内逼近证明在第149页将二阶导数字段分别作 L² 有界极限，再在最终包含任意紧支测试函数的子域上恢复弱导数。这里只建立相关基础，不把光滑内域解、Miranda–Talenti界或内域穷竭当作已经完成。

`BoundedTestRepresentation` 对任意实 Hilbert 空间 H、线性单射 J:V→H 和实际线性泛函 L，若 |Lx|≤C‖Jx‖，则通过实际 range J 上的连续泛函、Hahn–Banach等范数延拓和Riesz表示构造 v∈H，满足‖v‖≤C及全部 x 上的内积身份。V无需完备或稠密，C允许0，输出范数常数不增加。

`WeakDerivativeBoundedTest` 在任意开域S的原Lebesgue L²空间上，将全部真实紧支光滑测试jet的线性span作为V；原value映射单射，且span的每个元素确为一个真实测试函数。泛函是原u对测试方向导数的负内积。实际测试范数界因此构造一个真实L²弱导数v，其范数≤同一C；证明全部原测试的分部积分身份。反向由Cauchy–Schwarz给出精确等价，不预设u有任何Sobolev正则性。

`WeakDerivativeBoundedLimit` 只要求每个测试函数上的导数配对收敛、每个测试最终成立的分部积分身份，以及候选导数字段最终有统一L²界。用实数闭不等式传极限后调用前述表示，得到极限u的真实弱导数且保持C。V_n无需收敛，不预设存在弱收敛子列。恒定域上u_n强L²收敛、各u_n已有弱导数及其统一界是已证明的直接推论。更一般的逐测试最终身份允许后续内域穷竭，未声称H²零延拓成立。

三模块5显式声明，定向3169 jobs、全库3892 jobs通过，6787声明递归公理审计PASS。固定 `/tmp/carleman-bounded-limit-local-axioms.txt` 为2085893 bytes，SHA256 `94b2ec60a7ea2cb40147fcb603c70b448a8df5b2973b20ff74e6effe2d87b025`。

AUXILIARY、14/26；P023不提升。实际Dirichlet解的Hessian统一先验界、光滑内域正则性及穷竭构造仍需证明。原稿未改，无新增数学公理。
