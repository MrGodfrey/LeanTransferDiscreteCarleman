# T169 / C185：原 Cartesian 控制范数与真实物理载荷 Carleman 估计

三模块十三声明。CartesianPhysicalControlIsometry 从真实控制 Hilbert 伴随等于限制证明 B*B=id，再以实际内积证明原节点零延拓保范数。原状态/控制权乘子严格与零延拓交换，因此加权物理范数也精确相同；包括空观察节点集合。

CartesianCountWeights 以 T168 的真实质量等距满射构造原状态的计数 L² 实现。观测映射是 EBB*，其中 B 是实际原控制零延拓；其范数准确为原控制空间的 ‖B*z‖，而非依赖节点数的比较。真实节点相位值构造计数 SpatialProfile，任意允许指数 τ 下的状态及控制权范数均精确一致。

BoxCartesianLoadCarleman 取原高斯相位的实际节点值，使用全局逐点界构造固定 bound=2 的计数相位，并证明≤−1；没有用连续 a.e. 界推断节点值。原 T167 全状态双向 CE 内部供应周期负向载荷估计：q³ 状态项由完整 nodeEnergy 控制，真实逆等距 Γ=E⁻¹ 恢复载荷，原 B* 观察项由上述等式转换。结论为实际 PhysicalLoadCarleman，对所有周期节点状态和所有计数 L² 载荷成立。PhysicalQClass 的原导数与端点条件通过已证 toInterval 接入 T167。

所有 c/λ/β/qc/κ/h0/Δ0/C 在空间网格和时间数据之前选择，保留原 h^(-4/5)、dt^(-2/5) 尺度。最终无外加 CE、比较范数常数、测试估计、正则性或频率滤波假设。本批是盒 Cartesian 实例的物理载荷接口，尚未宣称观测/控制或一般几何完成；AUXILIARY，原文17/26。

控制等距定向3514 jobs，载荷组合定向3982 jobs，根目标4094 jobs通过。Axiom audit passed for all 8093 Carleman declarations. 固定raw 2510276 bytes，SHA256 2163ab6209f04e62d9563574a6ef1df423c1705878b0ffeb049544cbb7307eb4。同SHA正式CI与独立验收另行登记。
