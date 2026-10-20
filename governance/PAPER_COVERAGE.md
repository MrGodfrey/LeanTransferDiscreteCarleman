# 论文结果覆盖表

此表按原 TeX 的具名 theorem/lemma/proposition/corollary 登记，共 26 项。机器来源是 `state/paper_coverage.json`，本表由 `tools/update_dashboard.py` 同步生成。页码是原 PDF 页码，TeX 行号仅辅助定位，label 为稳定定位。

初始 19 项工作目标只映射其中 15 项结果，其余 11 项保留待分解。一个结果可以对应多个 Lean 声明；同一正文结果在附录证明不重复计数。Section 8 实验复现不在形式化计数内。

| ID | 原文结果 | 标签 | PDF 页 / TeX 行 | 阶段 | 初始目标 | Lean 声明 |
| --- | --- | --- | --- | --- | --- | --- |
| P001 | Theorem 2.1 | `thm:main` | 10 / 525 | M5 | C010 | Carleman.Section5.NumericalData, Carleman.Section5.TransferUniform, Carleman.OriginalForm.transfer_uniform |
| P002 | Corollary 2.2 | `cor:general-scales` | 11 / 599 | M5 | C011 | Carleman.CarlemanExponents.alphaX, Carleman.CarlemanExponents.alphaT, Carleman.Section5.ScaleUniform, Carleman.OriginalForm.scale_uniform |
| P003 | Corollary 2.3 | `cor:scales` | 11 / 617 | M5 | C012 | Carleman.CarlemanExponents.heat, Carleman.CarlemanExponents.heat_scale_exponents, Carleman.OriginalForm.heat_scale_uniform |
| P004 | Lemma 3.1 | `lem:graph` | 11 / 647 | M3 | C005, C036, C037 | Carleman.OriginalForm.section3_original_operator, Carleman.OriginalForm.ofBilinear_scalarForm, Carleman.PeriodicWeakTrajectory.graph_equation_iff, Carleman.Section3.Conclusions.primitive_on_interval, Carleman.Section3.Conclusions.form_bound, Carleman.Section3.Conclusions.form_coercive |
| P005 | Lemma 3.2 | `lem:cell` | 13 / 789 | M3 | C020 | Carleman.cell_estimates_uniform, Carleman.CellEstimates.weight_quotient_essSup, Carleman.CellEstimates.global_cell_bounds |
| P006 | Lemma 3.3 | `lem:eulerMR` | 14 / 863 | M3 | C006, C036, C037 | Carleman.OriginalForm.section3_original_operator, Carleman.OriginalForm.ofBilinear_scalarForm, Carleman.PeriodicWeakTrajectory.graph_equation_iff, Carleman.Section3.Conclusions.euler, Carleman.Section3.EulerEstimate |
| P007 | Lemma 3.4 | `lem:frozen` | 15 / 964 | M3 | C036, C037 | Carleman.OriginalForm.section3_original_operator, Carleman.OriginalForm.ofBilinear_scalarForm, Carleman.PeriodicWeakTrajectory.graph_equation_iff, Carleman.Section3.Conclusions.frozen, Carleman.Section3.ContinuousEstimate |
| P008 | Theorem 3.5 | `thm:timeerror` | 16 / 1023 | M3 | C007, C036, C037 | Carleman.OriginalForm.section3_original_operator, Carleman.OriginalForm.ofBilinear_scalarForm, Carleman.PeriodicWeakTrajectory.graph_equation_iff, Carleman.Section3.Conclusions.temporal, Carleman.Section3.TemporalEstimate, Carleman.Section3.temporal_arbitrary_uniform |
| P009 | Lemma 4.1 | `lem:spatialEuler` | 17 / 1148 | M4 | C008 | Carleman.Section4.EnergyEstimate, Carleman.Section4.L2Estimate, Carleman.Section4.SpatialUniform, Carleman.OriginalForm.spatial_uniform |
| P010 | Theorem 4.2 | `thm:combined` | 19 / 1287 | M4 | C009 | Carleman.Section4.reconstructedError_value_ae, Carleman.Section4.CombinedEstimate, Carleman.Section4.CombinedUniform, Carleman.OriginalForm.combined_uniform |
| P011 | Proposition 6.1 | `prop:p1` | 21 / 1499 | M6a | C277 | Carleman.finite_halfspace_convex, Carleman.finite_halfspace_p1_realization |
| P012 | Proposition 6.2 | `prop:fd` | 23 / 1672 | M6a | C015, C158 | Carleman.cartesian_numericalData_of_box, Carleman.cartesian_full_weight_interface |
| P013 | Lemma 7.1 | `lem:physicalduality` | 24 / 1753 | M6b | C040 | Carleman.Physical.ForwardEquation, Carleman.Physical.AdjointEquation, Carleman.Physical.physical_duality_lemma |
| P014 | Theorem 7.2 | `prop:physicalO` | 25 / 1827 | M6b | C016 | 待建立 |
| P015 | Theorem 7.3 | `prop:physicalC` | 27 / 2032 | M6b | C017 | 待建立 |
| P016 | Lemma 7.4 | `lem:filter-reverse` | 29 / 2164 | M6b | C041 | Carleman.Physical.filterRayleigh, Carleman.Physical.filterConstant, Carleman.Physical.filter_reverse |
| P017 | Theorem 7.5 | `thm:filtered-observability` | 29 / 2177 | M6b | C018 | 待建立 |
| P018 | Corollary 7.6 | `cor:filtered-control` | 29 / 2201 | M6b | 待分解 | 待建立 |
| P019 | Proposition 7.7 | `prop:filter-p1` | 30 / 2224 | M6b | C151 | Carleman.SimplicialPartition.maxDiameter_pos, Carleman.SimplicialPartition.inverseWeight_const_bound, Carleman.conforming_uniform_inverse, Carleman.Physical.filterRayleigh_le_of_energy_bound, Carleman.Physical.nestedConformingFilter, Carleman.Physical.dirichlet_galerkin_energy, Carleman.Physical.nested_p1_filter_rayleigh, Carleman.Physical.p1_coarse_filter_rayleigh |
| P020 | Proposition 7.8 | `prop:filter-fd` | 30 / 2241 | M6b | C153 | Carleman.linearRefinementBasis, Carleman.tensorLinearProlongation, Carleman.linearRefinementBasis_node, Carleman.uniformLinearProlongation_sum, Carleman.uniformLinearProlongation_const_mul, Carleman.tensorLinearProlongation_zero_face, Carleman.tensorLinearProlongation_node, Carleman.tensorLinearProlongation_slice, Carleman.cartesianAxisFill, Carleman.cartesianAxisFill_self, Carleman.cartesianAxisFill_update, Carleman.cartesian_sum_axis, Carleman.tensorLinearProlongation_line_inverse, Carleman.tensorLinearProlongation_direction_inverse, Carleman.tensorLinearProlongation_inverse, Carleman.cartesianLatticeData_of_box_values, Carleman.cartesian_sum_box_values, Carleman.cartesianLatticeSuccessor_nat, Carleman.cartesianCoarseProlongation, Carleman.cartesianCoarseProlongation_values, Carleman.cartesianCoarseProlongation_mass, Carleman.cartesianCoarseProlongation_axis, Carleman.cartesianCoarseProlongation_energy, Carleman.Physical.cartesianCoarseFilter, Carleman.Physical.cartesian_coarse_energy_bound, Carleman.Physical.fd_coarse_filter_rayleigh, Carleman.Physical.fd_dividing_filter_rayleigh |
| P021 | Corollary 7.9 | `prop:control-convergence` | 31 / 2344 | M6c | C019 | 待建立 |
| P022 | Proposition A.1 | `prop:spatial-operators` | 36 / 2615 | M6a | C245 | Carleman.OriginalForm.formSqrtDomain_eq, Carleman.OriginalForm.SquareRootData, Carleman.OriginalForm.exists_squareRootData, Carleman.higherCoefficient_spatial_operators |
| P023 | Corollary A.2 | `prop:analytic-realizations` | 37 / 2659 | M6a | C276 | Carleman.DirichletSpatialAnalyticData, Carleman.dirichlet_spatial_analytic_of_regularity, Carleman.finite_halfspace_analytic_realization, Carleman.box_full_spatial_analytic_realization |
| P024 | Proposition A.3 | `prop:continuousCE` | 37 / 2672 | M6a | C013 | 待建立 |
| P025 | Lemma B.1 | `lem:fd-boundary-affine` | 38 / 2803 | M6a | C097 | Carleman.OriginalForm.boundary_affine_lemma, Carleman.physicalBox_h2_corner_bound, Carleman.physicalBox_two_faces_affine_zero |
| P026 | Lemma B.2 | `lem:fd-weighted-approximation` | 39 / 2841 | M6a | C113 | Carleman.allowed_weight_cartesianKuhn_h2_error, Carleman.allowed_weight_cartesianKuhn_approximation |
