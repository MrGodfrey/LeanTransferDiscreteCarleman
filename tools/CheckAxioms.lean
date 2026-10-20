module

import Carleman
import Lean.Util.CollectAxioms

/-! Print the main interfaces and reject unapproved axioms in every project declaration. -/

#check @Carleman.sum_sub_perm
#print axioms Carleman.sum_sub_perm
#check @Carleman.TimeGrid
#check @Carleman.TimeGrid.period
#check @Carleman.TimeGrid.dt_eq_period_div_steps
#check @Carleman.TimeGrid.next_eq_add_one
#check @Carleman.TimeGrid.prev_eq_sub_one
#check @Carleman.TimeGrid.dPlus_apply
#check @Carleman.TimeGrid.dMinus_apply
#check @Carleman.TimeGrid.pairing
#check @Carleman.TimeGrid.pairing_self_eq_zero
#check @Carleman.TimeGrid.pairing_dPlus
#check @Carleman.TimeGrid.pairing_dMinus
#print axioms Carleman.TimeGrid.pairing_dPlus
#print axioms Carleman.TimeGrid.pairing_dMinus

#check @Carleman.TimeGrid.map
#check @Carleman.TimeGrid.dPlus_map
#check @Carleman.TimeGrid.dMinus_map
#check @Carleman.Reconstruction
#check @Carleman.Reconstruction.Q
#check @Carleman.Reconstruction.G
#check @Carleman.Reconstruction.pairing_RH_dPlus
#check @Carleman.Reconstruction.pairing_RH_dMinus
#check @Carleman.Reconstruction.shifted_dPlus_unique
#check @Carleman.Reconstruction.shifted_dMinus_unique
#check @Carleman.LoadInterface
#check @Carleman.LoadInterface.J_transferLoad
#check @Carleman.LoadInterface.auxiliary_dPlus_eq_state
#check @Carleman.LoadInterface.auxiliary_dMinus_eq_state
#print axioms Carleman.LoadInterface.auxiliary_dPlus_eq_state
#print axioms Carleman.LoadInterface.auxiliary_dMinus_eq_state

#print Carleman.Reconstruction
#print Carleman.LoadInterface
#check @Carleman.Reconstruction.J_unique
#check @Carleman.TimeGrid.extensionPlus_on_cell
#check @Carleman.TimeGrid.extensionMinus_on_cell
#check @Carleman.TimeGrid.extensionPlus_period
#check @Carleman.TimeGrid.extensionMinus_period
#check @Carleman.LoadInterface.existsUnique_auxiliary_dPlus
#check @Carleman.LoadInterface.existsUnique_auxiliary_dMinus
#check @Carleman.LoadInterface.residualPlus_eventuallyEq
#check @Carleman.LoadInterface.residualMinus_eventuallyEq
#print axioms Carleman.LoadInterface.existsUnique_auxiliary_dPlus
#print axioms Carleman.LoadInterface.existsUnique_auxiliary_dMinus
#print axioms Carleman.LoadInterface.residualPlus_eventuallyEq
#print axioms Carleman.LoadInterface.residualMinus_eventuallyEq

#check @Carleman.Reconstruction.ofLinearMap
#check @Carleman.Reconstruction.existsUnique_mass_adjoint
#print axioms Carleman.Reconstruction.ofLinearMap
#print axioms Carleman.Reconstruction.existsUnique_mass_adjoint

-- Real uses of the shared commutation theorem at all four paper maps.
section ReconstructionUses
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  {V : Submodule ℝ H} (r : Carleman.Reconstruction V X) (g : Carleman.TimeGrid)
example (z : g.Sequence X) : g.dPlus (g.map r.R z) = g.map r.R (g.dPlus z) :=
  g.dPlus_map r.R z
example (z : g.Sequence X) : g.dMinus (g.map r.R z) = g.map r.R (g.dMinus z) :=
  g.dMinus_map r.R z
example (v : g.Sequence H) : g.dPlus (g.map r.J v) = g.map r.J (g.dPlus v) :=
  g.dPlus_map r.J v
example (v : g.Sequence H) : g.dMinus (g.map r.J v) = g.map r.J (g.dMinus v) :=
  g.dMinus_map r.J v
example (v : g.Sequence H) : g.dPlus (g.map r.Q v) = g.map r.Q (g.dPlus v) :=
  g.dPlus_map r.Q v
example (v : g.Sequence H) : g.dMinus (g.map r.Q v) = g.map r.Q (g.dMinus v) :=
  g.dMinus_map r.Q v
example (z : g.Sequence X) : g.dPlus (g.map r.G z) = g.map r.G (g.dPlus z) :=
  g.dPlus_map r.G z
example (z : g.Sequence X) : g.dMinus (g.map r.G z) = g.map r.G (g.dMinus z) :=
  g.dMinus_map r.G z
end ReconstructionUses

-- Regression for the manuscript's unrestricted load maps: F has no typeclasses,
-- and Γ/lift are arbitrary functions satisfying only the original compatibility.
section OrdinaryLoadMaps
variable {H X F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  {V : Submodule ℝ H} (r : Carleman.Reconstruction V X) (g : Carleman.TimeGrid)
  (Γ : F → X) (lift : F → H) (h : ∀ f, r.J (lift f) = Γ f)
example (μ : g.Sequence ℝ) (f : g.Sequence F) (z : g.Sequence X) :
    g.map r.J ((Carleman.LoadInterface.mk Γ lift h).transferLoad g μ f z) =
      (fun i => Γ (f i)) + fun i => μ i • r.G (z i) :=
  (Carleman.LoadInterface.mk Γ lift h).J_transferLoad g μ f z
example (I : X → F) (hI : ∀ z, Γ (I z) = z) (v : g.Sequence X) :
    (fun i => Γ (I (v i))) = v :=
  (Carleman.LoadInterface.mk Γ lift h).rightInverse_load g I hI v
end OrdinaryLoadMaps

-- T003: actual norm objects, genuine weak trajectory, and the uniform conditional conclusion.
#print Carleman.PeriodicWeakTrajectory
#print Carleman.TransferGeometry
#print Carleman.ComparisonBridge
#print Carleman.ErrorBridge
#print Carleman.TransferBridges
#check @Carleman.TimeGrid.weightedNorm_sq
#check @Carleman.TimeGrid.powerSq_eq_weightedSq
#check @Carleman.PeriodicWeakTrajectory.domainValue_L2
#check @Carleman.PeriodicWeakTrajectory.domainValue_weakDerivative
#check @Carleman.PeriodicWeakTrajectory.residual_ae
#check @Carleman.LoadInterface.transferLoad_powerSq_le
#check @Carleman.ComparisonBridge.comparison
#check @Carleman.ErrorBridge.total_bound
#check @Carleman.conditional_transfer_uniform
#print axioms Carleman.conditional_transfer_uniform
#print axioms Carleman.PeriodicWeakTrajectory.residual_ae

-- T004: exact cell integrals, actual L² objects, full Lemma 3.2 and B3 constructors.
#print Carleman.TimeWeightRegularity
#print Carleman.CellEstimates
#print Carleman.BoundedMultiplier
#print Carleman.SpatialProfile
#check @Carleman.TimeGrid.cellTime_succ_sub
#check @Carleman.TimeGrid.cellTime_lt_succ
#check @Carleman.TimeGrid.extensionPlus_on_open_cell
#check @Carleman.TimeGrid.extensionMinus_on_open_cell
#check @Carleman.TimeGrid.intervalIntegrable_extensionPlus_cell
#check @Carleman.TimeGrid.intervalIntegrable_extensionMinus_cell
#check @Carleman.TimeGrid.integral_extensionPlus_cell
#check @Carleman.TimeGrid.integral_extensionMinus_cell
#check @Carleman.TimeGrid.integrable_extensionPlus
#check @Carleman.TimeGrid.integrable_extensionMinus
#check @Carleman.TimeGrid.integral_extensionPlus
#check @Carleman.TimeGrid.integral_extensionMinus
#check @Carleman.Orientation.measurable_cell_index
#check @Carleman.Orientation.aestronglyMeasurable_cell_select
#check @Carleman.Orientation.integral_extension
#check @Carleman.Orientation.integrable_extension
#check @Carleman.Orientation.integral_frozen_weightedSq
#check @Carleman.Orientation.integrable_frozen_density
#check @Carleman.Orientation.timeSq_frozen_eq_powerSq
#check @Carleman.TimeGrid.node_value_of_periodic_endpoints
#check @Carleman.TimeGrid.cellTime_mem
#check @Carleman.TimeGrid.next_node_value
#check @Carleman.Orientation.extension_eq_cellNumber
#check @Carleman.Orientation.cellNumber_nonneg
#check @Carleman.Orientation.cellNumber_le_steps
#check @Carleman.Orientation.anchor_mem
#check @Carleman.Orientation.anchor_distance
#check @Carleman.Orientation.anchor_value_eq_extension
#check @Carleman.Orientation.extension_periodic
#check @Carleman.cellThreshold_pos
#check @Carleman.cellThreshold_bounds
#check @Carleman.TimeWeightRegularity.mesh_bounds
#check @Carleman.TimeWeightRegularity.relative_q_extension
#check @Carleman.TimeWeightRegularity.relative_weight_extension
#check @Carleman.TimeWeightRegularity.shift_extension
#check @Carleman.TimeWeightRegularity.weight_time_quotient
#check @Carleman.TimeWeightRegularity.weight_time_quotient_essSup
#check @Carleman.TimeWeightRegularity.shift_node_increment
#check @Carleman.TimeWeightRegularity.weight_node_quotient
#check @Carleman.cell_estimates_uniform
#check @Carleman.CellEstimates.weight_quotient_essSup
#check @Carleman.CellEstimates.global_cell_bounds
#check @Carleman.TimeWeightRegularity.continuousOn
#check @Carleman.TimeWeightRegularity.aestronglyMeasurable
#check @Carleman.TimeWeightRegularity.reciprocal_lipschitz
#check @Carleman.TimeWeightRegularity.difference_le
#check @Carleman.TimeWeightRegularity.small_node
#check @Carleman.TimeWeightRegularity.comparable
#check @Carleman.TimeWeightRegularity.relative_q
#check @Carleman.TimeWeightRegularity.allowedWeight_pos
#check @Carleman.TimeWeightRegularity.allowedWeight_eq_exp
#check @Carleman.TimeWeightRegularity.cell_distance
#check @Carleman.TimeWeightRegularity.logWeight_derivative_bound
#check @Carleman.TimeWeightRegularity.logWeight_difference
#check @Carleman.TimeWeightRegularity.relative_weight
#check @Carleman.TimeWeightRegularity.weight_le
#check @Carleman.TimeWeightRegularity.power_difference
#check @Carleman.TimeWeightRegularity.shift_difference
#check @Carleman.SpatialProfile.multiplier_value
#check @Carleman.SpatialProfile.multiplier_neg_value
#check @Carleman.SpatialProfile.seminorm_definite
#check @Carleman.SpatialProfile.seminorm_cell_le
#check @Carleman.SpatialProfile.multiplier_map_add_exponent
#check @Carleman.SpatialProfile.seminorm_add_exponent
#check @Carleman.SpatialProfile.density_eq_shifted_seminorm_sq
#check @Carleman.SpatialProfile.seminorm_global_le
#check @Carleman.SpatialProfile.aestronglyMeasurable_seminorm_sq
#check @Carleman.SpatialProfile.aestronglyMeasurable_extended_sq
#check @Carleman.SpatialProfile.extended_sq_comparable
#check @Carleman.SpatialProfile.extended_sq_integral_comparison
#check @Carleman.SpatialProfile.powerSq_timeSq_comparison
#check @Carleman.SpatialProfile.powerSq_timeSq_comparison_comp
#check @Carleman.SpatialProfile.lifted_timeSq_le
#check @Carleman.SpatialProfile.node_powerSq_le_reconstruction
#check @Carleman.SpatialProfile.powerSq_timeSq_uniform
#check @Carleman.SpatialProfile.powerSq_timeSq_uniform_bounded_exponents
#check @Carleman.BoundedMultiplier.observation_le
#check @Carleman.BoundedMultiplier.observation_sq_integral
#check @Carleman.SpatialProfile.observation_time_comparison
#check @Carleman.BoundedMultiplier.memLp_smul
#check @Carleman.BoundedMultiplier.map_ae
#check @Carleman.BoundedMultiplier.map_add
#check @Carleman.BoundedMultiplier.map_smul
#check @Carleman.BoundedMultiplier.seminorm_apply
#check @Carleman.BoundedMultiplier.seminorm_le
#check @Carleman.BoundedMultiplier.seminorm_le_of_weight_le
#check @Carleman.BoundedMultiplier.seminorm_eq_zero_iff
#check @Carleman.BoundedMultiplier.seminorm_sq_integral
#check @Carleman.BoundedMultiplier.integrable_density
#check @Carleman.TransferGeometry.node_derivative_of_L2
#check @Carleman.TransferGeometry.node_state_of_L2
#check @Carleman.TransferGeometry.lifted_load_of_L2
#check @Carleman.TransferGeometry.observed_reconstruction_of_L2
#check @Carleman.frozenShift_extension_sq_le
#check @Carleman.frozenShift_timeSq_le
#check @Carleman.TimeWeightRegularity.ofContDiffOn
#print axioms Carleman.cell_estimates_uniform
#print axioms Carleman.CellEstimates.global_cell_bounds
#print axioms Carleman.SpatialProfile.powerSq_timeSq_uniform_bounded_exponents
#print axioms Carleman.TransferGeometry.lifted_load_of_L2
#print axioms Carleman.frozenShift_timeSq_le

-- T005: every new public declaration, bound to the build SHA.
#check @Carleman.DifferentialExpression
#check @Carleman.DifferentialExpression.boundSq
#check @Carleman.DifferentialExpression.boundSq_nonneg
#check @Carleman.DifferentialExpression.orders
#check @Carleman.DifferentialExpression.apply
#check @Carleman.DifferentialExpression.apply_ae
#check @Carleman.DifferentialExpression.linearMap
#check @Carleman.DifferentialExpression.weighted_sq_le
#check @Carleman.DifferentialExpression.weighted_density_le
#check @Carleman.CarlemanExponents.order_exponent_le
#check @Carleman.DifferentialExpression.onFields
#check @Carleman.DifferentialExpression.onFields_apply
#check @Carleman.DifferentialExpression.timeSq_le_graph
#check @Carleman.DifferentialExpression.aestronglyMeasurable_apply
#check @Carleman.OperatorMultiplier
#check @Carleman.OperatorMultiplier.memLp_apply
#check @Carleman.OperatorMultiplier.map
#check @Carleman.OperatorMultiplier.map_ae
#check @Carleman.OperatorMultiplier.map_add
#check @Carleman.OperatorMultiplier.map_smul
#check @Carleman.OperatorMultiplier.linearMap
#check @Carleman.OperatorMultiplier.norm_map_le
#check @Carleman.OperatorMultiplier.continuousLinearMap
#check @Carleman.OperatorMultiplier.map_weight
#check @Carleman.OperatorMultiplier.weighted_seminorm_le
#check @Carleman.OperatorMultiplier.ofCoefficients
#check @Carleman.OperatorMultiplier.ofCoefficients_apply
#check @Carleman.OperatorMultiplier.ofCoefficients_map_ae
#check @Carleman.OperatorMultiplier.const
#check @Carleman.OperatorMultiplier.const_map_ae
#check @Carleman.VectorCoefficient
#check @Carleman.OperatorMultiplier.ofVectorCoefficients
#check @Carleman.OperatorMultiplier.ofVectorCoefficients_apply
#check @Carleman.OperatorMultiplier.ofVectorCoefficients_map_ae
#check @Carleman.SpatialCoordinates
#check @Carleman.DerivativeFiber
#check @Carleman.JetFields
#check @Carleman.derivativeComponent
#check @Carleman.derivativeComponent_ae
#check @Carleman.weakJetSubmodule
#check @Carleman.WeakSobolevJet
#check @Carleman.WeakSobolevJet.field
#check @Carleman.WeakSobolevJet.field_weak_derivative
#check @Carleman.WeakSobolevJet.field_weighted_sq
#check @Carleman.WeakSobolevJet.expression
#check @Carleman.WeakSobolevJet.expression_weighted_density_le
#check @Carleman.WeakSobolevJet.vectorExpression
#check @Carleman.WeakSobolevJet.vectorExpression_apply_ae
#check @Carleman.derivativeComponent_ext
#check @Carleman.derivativeFiber_zero_norm_sq
#check @Carleman.WeakSobolevJet.value
#check @Carleman.WeakSobolevJet.eq_zero_of_value_eq_zero
#check @Carleman.WeakSobolevJet.value_injective
#check @Carleman.sobolevSubspace
#check @Carleman.sobolevJetEquiv
#check @Carleman.sobolevDerivative
#check @Carleman.sobolevDerivative_weak
#check @Carleman.sobolevDerivative_zero_value
#check @Carleman.sobolevDerivative_zero_seminorm
#check @Carleman.SpatialTest
#check @Carleman.SpatialTest.memLp
#check @Carleman.SpatialTest.memLp_derivative
#check @Carleman.SpatialTest.toLp
#check @Carleman.SpatialTest.derivativeLp
#check @Carleman.SpatialTest.toLp_ae
#check @Carleman.SpatialTest.derivativeLp_ae
#check @Carleman.IsWeakSpatialDerivative
#check @Carleman.IsWeakSpatialDerivative.iff_integral
#check @Carleman.IsWeakSpatialDerivative.zero
#check @Carleman.IsWeakSpatialDerivative.add
#check @Carleman.IsWeakSpatialDerivative.smul
#check @Carleman.spatial_eq_zero_of_tests
#check @Carleman.IsWeakSpatialDerivative.unique
#check @Carleman.IsWeakSpatialDerivative.of_zero
#check @Carleman.TransferGeometry.order_of_L2_expression
#check @Carleman.TransferGeometry.order_of_L2_expressions_uniform
#check @Carleman.CarlemanExponents.comparisonExponent
#check @Carleman.CarlemanExponents.comparisonExponent_bounds
#check @Carleman.conformingDerivative
#check @Carleman.conformingExpression
#check @Carleman.conformingDerivative_zero_seminorm
#check @Carleman.conformingDerivative_weak
#check @Carleman.conformingExpression_ae
#check @Carleman.sobolevGeometry
#check @Carleman.differentialFamilyBound
#check @Carleman.differentialFamilyBound_ge_one
#check @Carleman.sobolevGeometry_order
#check @Carleman.sobolevGeometry_node_derivative
#check @Carleman.sobolevGeometry_node_state
#check @Carleman.sobolevGeometry_lifted_load
#check @Carleman.sobolevGeometry_observation
#check @Carleman.sobolevGeometry_comparisons
#check @Carleman.norm_iteratedFDeriv_exp
#check @Carleman.norm_iteratedFDerivWithin_exp_profile
#check @Carleman.norm_iteratedFDerivWithin_allowedWeight
#check @Carleman.exists_profile_derivative_bound
#check @Carleman.allowedWeight_spatial_derivatives_uniform
#check @Carleman.SpatialProfile.ofContinuousOn
#check @Carleman.SpatialProfile.ofContinuousOn_value
#check @Carleman.SpatialProfile.ofContinuousOn_multiplier
#check @Carleman.TimeWeightRegularity.hasDerivWithinAt_logWeight
#check @Carleman.TimeWeightRegularity.hasDerivWithinAt_allowedWeight
#check @Carleman.TimeWeightRegularity.derivWithin_logWeight_bound
#check @Carleman.TimeWeightRegularity.allowedWeight_inv
#check @Carleman.SpatialProfile.logDerivative
#check @Carleman.SpatialProfile.logDerivative_value
#check @Carleman.SpatialProfile.logDerivative_seminorm_le
#check @Carleman.SpatialProfile.logDerivative_shift_le
#check @Carleman.TimeWeightRegularity.shifted_power_derivative_ratio
#check @Carleman.TimeWeightRegularity.shift_derivative_ratio
#print Carleman.OperatorMultiplier
#print Carleman.VectorCoefficient
#print Carleman.DifferentialExpression
#print Carleman.SpatialTest
#print Carleman.IsWeakSpatialDerivative
#print axioms Carleman.allowedWeight_spatial_derivatives_uniform
#print axioms Carleman.TimeWeightRegularity.shift_derivative_ratio
#print axioms Carleman.WeakSobolevJet.value_injective
#print axioms Carleman.sobolevGeometry_order
#print axioms Carleman.sobolevGeometry_comparisons

-- T006: concrete Bochner/Sobolev and remaining bridge constructors.
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#check @Carleman.Orientation.aestronglyMeasurable_extension
#check @Carleman.Orientation.memLp_extension
#check @Carleman.Orientation.memLp_smul_extension
#check @Carleman.PeriodicWeakTrajectory.sobolevError
#check @Carleman.PeriodicWeakTrajectory.sobolevError_value_ae
#check @Carleman.PeriodicWeakTrajectory.sobolevError_L2
#check @Carleman.PeriodicWeakTrajectory.sobolevError_field_finite
#check @Carleman.PeriodicWeakTrajectory.sobolevError_expression_finite
#check @Carleman.domainSobolevJet
#check @Carleman.domainSobolevJet_value
#check @Carleman.injective_of_elliptic_bound
#check @Carleman.memLp_domainSobolevJet_of_operator
#check @Carleman.PeriodicWeakTrajectory.domainSobolev_L2
#check @Carleman.PeriodicWeakTrajectory.weighted_domain_field_finite
#check @Carleman.BoundedMultiplier.continuousLinearMap
#check @Carleman.BoundedMultiplier.continuousLinearMap_apply
#check @Carleman.SpatialProfile.expMultiplier
#check @Carleman.SpatialProfile.expCLM
#check @Carleman.SpatialProfile.expCLM_ae
#check @Carleman.SpatialProfile.exp_profile_difference
#check @Carleman.SpatialProfile.expCLM_sub_norm_le
#check @Carleman.SpatialProfile.continuous_expCLM
#check @Carleman.SpatialProfile.multiplier_map_eq_expCLM
#check @Carleman.SpatialProfile.aestronglyMeasurable_map
#check @Carleman.SpatialProfile.memLp_map
#check @Carleman.derivativeComponentCLM
#check @Carleman.derivativeComponentCLM_apply
#check @Carleman.weakJetSubmodule_isClosed
#check @Carleman.weakSobolevJet_completeSpace
#check @Carleman.WeakSobolevJet.fieldCLM
#check @Carleman.WeakSobolevJet.fieldCLM_apply
#check @Carleman.WeakSobolevJet.valueCLM
#check @Carleman.WeakSobolevJet.valueCLM_apply
#check @Carleman.WeakSobolevJet.norm_field_le
#check @Carleman.WeakSobolevJet.norm_le_sum_fields
#check @Carleman.WeakSobolevJet.sum_fields_le
#check @Carleman.WeakSobolevJet.aestronglyMeasurable_field
#check @Carleman.WeakSobolevJet.memLp_field
#check @Carleman.WeakSobolevJet.truncate
#check @Carleman.WeakSobolevJet.truncate_value
#check @Carleman.WeakSobolevJet.norm_truncate_le
#check @Carleman.sobolevSubspace_mono
#check @Carleman.domainSobolevJet_norm_mono
#check @Carleman.elliptic_bound_lower_order
#check @Carleman.BoundedMultiplier.inner_map_left
#check @Carleman.SpatialTest.mulOn
#check @Carleman.SpatialTest.mulOn_toLp
#check @Carleman.SpatialTest.mulOn_derivativeLp
#check @Carleman.IsWeakSpatialDerivative.mul
#check @Carleman.SpatialProfile.timeSquareIntegrable_of_memLp
#check @Carleman.SpatialProfile.timeSq_eq_norm_toLp_sq
#check @Carleman.SpatialProfile.timeNorm_eq_norm_toLp
#check @Carleman.DifferentialExpression.memLp_apply
#check @Carleman.DifferentialExpression.timeSquareIntegrable_apply
#check @Carleman.WeakSobolevJet.timeSquareIntegrable_field
#check @Carleman.sobolevGeometry_comparisonBridge
#check @Carleman.sobolevGeometry_errorBridge
#check @Carleman.sobolevGeometry_value_finite
#check @Carleman.sobolevGeometry_observation_finite
#check @Carleman.sobolevGeometry_derivative_finite
#check @Carleman.sobolevGeometry_gradient_finite
#check @Carleman.conforming_value_L2
#check @Carleman.sobolevGeometry_trajectory_graph_L2
#check @Carleman.sobolevGeometry_reconstruction_graph_L2
#check @Carleman.sobolevGeometry_error_graph_L2
#check @Carleman.coordinateTensorEval
#check @Carleman.coordinateDerivative
#check @Carleman.coordinateDerivative_zero
#check @Carleman.coordinateDerivative_cons
#check @Carleman.abs_coordinateDerivative_le
#check @Carleman.coordinateVector
#check @Carleman.coordinateVector_represents
#check @Carleman.coordinateCollection
#check @Carleman.norm_coordinateCollection_le
#check @Carleman.iteratedFDerivWithin_eq_of_mem_nhds
#check @Carleman.allowedWeight_coordinate_derivatives_uniform
#check @Carleman.SpatialProfile.directionalMultiplier
#check @Carleman.SpatialProfile.weightDirectionalMultiplier
#check @Carleman.SpatialProfile.multiplier_smooth
#check @Carleman.SpatialProfile.weightDirectionalMultiplier_value
#check @Carleman.SpatialProfile.weightDirectionalMultiplier_map
#check @Carleman.SpatialProfile.weak_derivative_weighted
#check @Carleman.TimeGrid.ae_mem_period
#check @Carleman.TimeWeightRegularity.derivative_ae
#check @Carleman.TimeWeightRegularity.aestronglyMeasurable_derivative
#check @Carleman.TimeWeightRegularity.memLp_shift
#check @Carleman.SpatialProfile.valueMultiplier
#check @Carleman.SpatialProfile.logDerivativeAction
#check @Carleman.SpatialProfile.logDerivativeAction_eq
#check @Carleman.SpatialProfile.aestronglyMeasurable_logDerivativeAction
#check @Carleman.SpatialProfile.memLp_logDerivativeAction
#check @Carleman.SpatialProfile.logDerivative_spacetime_le
#print axioms Carleman.sobolevGeometry_comparisonBridge
#print axioms Carleman.sobolevGeometry_errorBridge
#print axioms Carleman.SpatialProfile.logDerivative_spacetime_le
#print axioms Carleman.allowedWeight_coordinate_derivatives_uniform
#print axioms Carleman.memLp_domainSobolevJet_of_operator
#print axioms Carleman.IsWeakSpatialDerivative.mul

-- T007: every explicit declaration, including actual objects and existence results.
#check @Carleman.CoerciveForm
#check @Carleman.CoerciveForm.form_nonneg
#check @Carleman.CoerciveForm.eq_of_tests
#check @Carleman.CoerciveForm.domainV
#check @Carleman.CoerciveForm.domain
#check @Carleman.CoerciveForm.energyRaw
#check @Carleman.CoerciveForm.energyRaw_mem
#check @Carleman.CoerciveForm.embed_energyRaw
#check @Carleman.CoerciveForm.energy
#check @Carleman.CoerciveForm.embed_energy
#check @Carleman.CoerciveForm.operatorRaw
#check @Carleman.CoerciveForm.operatorRaw_test
#check @Carleman.CoerciveForm.operator
#check @Carleman.CoerciveForm.operator_test
#check @Carleman.CoerciveForm.domainElement
#check @Carleman.CoerciveForm.energy_domainElement
#check @Carleman.CoerciveForm.operator_domainElement
#check @Carleman.CoerciveForm.operator_symmetric
#check @Carleman.CoerciveForm.operator_nonneg
#check @Carleman.CoerciveForm.IsAssociated
#check @Carleman.CoerciveForm.operator_isAssociated
#check @Carleman.CoerciveForm.IsAssociated.domain_eq
#check @Carleman.CoerciveForm.IsAssociated.operator_eq
#check @Carleman.CoerciveForm.IsAssociated.existsUnique_periodicEuler
#check @Carleman.CoerciveForm.IsAssociated.euler_unweighted_graph
#check @Carleman.CoerciveForm.resolventH
#check @Carleman.CoerciveForm.resolventH_eq
#check @Carleman.CoerciveForm.operatorGraph
#check @Carleman.CoerciveForm.operatorGraph_mem
#check @Carleman.CoerciveForm.operatorGraph_eq
#check @Carleman.CoerciveForm.operatorGraph_isClosed
#check @Carleman.CoerciveForm.operatorGraph_completeSpace
#check @Carleman.CoerciveForm.domain_dense
#check @Carleman.variationalSolve
#check @Carleman.variationalSolve_spec
#check @Carleman.variationalSolve_unique
#check @Carleman.CoerciveForm.shiftedForm
#check @Carleman.CoerciveForm.shiftedForm_apply
#check @Carleman.CoerciveForm.shiftedForm_coercive
#check @Carleman.CoerciveForm.loadFunctional
#check @Carleman.CoerciveForm.loadFunctional_apply
#check @Carleman.CoerciveForm.resolventEnergy
#check @Carleman.CoerciveForm.resolventEnergy_test
#check @Carleman.CoerciveForm.resolvent
#check @Carleman.CoerciveForm.resolvent_equation
#check @Carleman.CoerciveForm.resolvent_unique
#check @Carleman.CoerciveForm.existsUnique_shifted
#check @Carleman.sum_bilinear_increment
#check @Carleman.sum_weighted_increment
#check @Carleman.TimeGrid.l2Sq
#check @Carleman.TimeGrid.l2Norm
#check @Carleman.TimeGrid.l2Sq_eq
#check @Carleman.TimeGrid.l2Sq_nonneg
#check @Carleman.TimeGrid.l2Norm_sq
#check @Carleman.TimeGrid.l2Norm_nonneg
#check @Carleman.CoerciveForm.eulerResidual
#check @Carleman.CoerciveForm.euler_energy_identity
#check @Carleman.CoerciveForm.euler_graph_sq
#check @Carleman.CoerciveForm.euler_graph_norm
#check @Carleman.TimeGrid.l2Norm_le_of_bound
#check @Carleman.TimeWeightRegularity.shift_node_decrement
#check @Carleman.TimeWeightRegularity.shift_oriented_increment
#check @Carleman.TimeWeightRegularity.shift_increment_absorb
#check @Carleman.eulerShiftThreshold
#check @Carleman.eulerShiftThreshold_large
#check @Carleman.CoerciveForm.euler_unweighted_graph
#check @Carleman.CoerciveForm.periodicEuler_wellposed
#check @Carleman.CoerciveForm.eulerSolution
#check @Carleman.CoerciveForm.eulerSolution_coe
#check @Carleman.CoerciveForm.eulerSolution_equation
#check @Carleman.CoerciveForm.eulerSolution_unique
#check @Carleman.CoerciveForm.existsUnique_periodicEuler
#check @Carleman.Orientation.neighbor
#check @Carleman.Orientation.difference_neighbor
#check @Carleman.Orientation.pairing_difference_self_nonneg
#check @Carleman.CoerciveForm.EulerSpace
#check @Carleman.CoerciveForm.eulerForm
#check @Carleman.CoerciveForm.eulerForm_apply
#check @Carleman.CoerciveForm.eulerForm_coercive
#check @Carleman.CoerciveForm.eulerLoad
#check @Carleman.CoerciveForm.eulerLoad_apply
#check @Carleman.CoerciveForm.eulerEnergy
#check @Carleman.CoerciveForm.eulerEnergy_test
#check @Carleman.conformingEuler_existsUnique
#check @Carleman.euler_sobolev_fields_bound
#check @Carleman.conformingHilbert
#check @Carleman.conformingEmbed
#check @Carleman.conformingHilbert_isClosed
#check @Carleman.conformingHilbert_completeSpace
#check @Carleman.conformingEmbed_range
#check @Carleman.conformingEmbed_dense
#check @Carleman.conformingEmbed_injective
#check @Carleman.conformingCoerciveForm
#check @Carleman.HilbertJetFields
#check @Carleman.hilbertJetSubmodule
#check @Carleman.SobolevHilbert
#check @Carleman.hilbertJetSubmodule_isClosed
#check @Carleman.sobolevHilbert_completeSpace
#check @Carleman.SobolevHilbert.toJet
#check @Carleman.SobolevHilbert.ofJet
#check @Carleman.SobolevHilbert.jetEquiv
#check @Carleman.SobolevHilbert.norm_sq
#check @Carleman.SobolevHilbert.value
#check @Carleman.SobolevHilbert.value_injective
#print axioms Carleman.CoerciveForm.periodicEuler_wellposed
#print axioms Carleman.CoerciveForm.euler_energy_identity
#print axioms Carleman.CoerciveForm.euler_unweighted_graph
#print axioms Carleman.CoerciveForm.operatorGraph_isClosed
#print axioms Carleman.CoerciveForm.domain_dense
#print axioms Carleman.conformingEuler_existsUnique
#print axioms Carleman.euler_sobolev_fields_bound

-- T008: all explicit declarations; the recursive audit below checks their dependencies.
#check @Carleman.TimeGrid.timeIntegral_eq_intervalIntegral
#check @Carleman.TimeGrid.memLp_of_continuousOn
#check @Carleman.HasWeakTimeDerivative.of_hasDerivAt
#check @Carleman.Orientation.extensionLp
#check @Carleman.Orientation.extensionLp_ae
#check @Carleman.Orientation.extensionLp_norm_sq
#check @Carleman.Orientation.extensionLp_norm
#check @Carleman.CoerciveForm.eulerExtension_graph
#check @Carleman.CoerciveForm.eulerExtension_graph_bound
#check @Carleman.TimeGrid.constantMultiplier
#check @Carleman.TimeGrid.harmonicLp
#check @Carleman.TimeGrid.harmonicLp_ae
#check @Carleman.CoerciveForm.frequencyGraph
#check @Carleman.CoerciveForm.frequencyGraph_equation
#check @Carleman.CoerciveForm.finiteFrequencyGraph
#check @Carleman.CoerciveForm.finiteFrequencyGraph_equation
#check @Carleman.CoerciveForm.exists_finite_harmonic
#check @Carleman.CoerciveForm.IsAssociated.exists_finite_harmonic
#check @Carleman.CoerciveForm.timeGraphDefect
#check @Carleman.CoerciveForm.timeOperatorGraph
#check @Carleman.CoerciveForm.timeOperatorGraph_mem
#check @Carleman.CoerciveForm.timeOperatorGraph_isClosed
#check @Carleman.CoerciveForm.timeOperatorGraph_ae
#check @Carleman.CoerciveForm.timeOperatorGraph_representative
#check @Carleman.CoerciveForm.timeOperatorGraph_completeSpace
#check @Carleman.CoerciveForm.frequency_energy_identity
#check @Carleman.CoerciveForm.frequency_graph_sq
#check @Carleman.CoerciveForm.frequency_kernel
#check @Carleman.CoerciveForm.frequency_solution_graph
#check @Carleman.CoerciveForm.frequency_unique
#check @Carleman.CoerciveForm.existsUnique_frequency
#check @Carleman.CoerciveForm.FrequencySpace
#check @Carleman.CoerciveForm.frequencyProjection
#check @Carleman.CoerciveForm.frequencyForm
#check @Carleman.CoerciveForm.frequencyForm_apply
#check @Carleman.CoerciveForm.frequencyForm_coercive
#check @Carleman.CoerciveForm.frequencyLoad
#check @Carleman.CoerciveForm.frequencyLoad_apply
#check @Carleman.CoerciveForm.frequencyEnergy
#check @Carleman.CoerciveForm.frequencyEnergy_test_zero
#check @Carleman.CoerciveForm.frequencyEnergy_test_one
#check @Carleman.CoerciveForm.frequencyCos
#check @Carleman.CoerciveForm.frequencySin
#check @Carleman.CoerciveForm.frequencyCos_equation
#check @Carleman.CoerciveForm.frequencySin_equation
#check @Carleman.TimeGrid.angularFrequency
#check @Carleman.TimeGrid.angularFrequency_period
#check @Carleman.harmonicValue
#check @Carleman.harmonicDerivative
#check @Carleman.harmonic_hasDerivAt
#check @Carleman.harmonic_continuous
#check @Carleman.harmonicDerivative_continuous
#check @Carleman.harmonic_periodic_trace
#check @Carleman.CoerciveForm.harmonicDomain
#check @Carleman.CoerciveForm.harmonicDomain_value
#check @Carleman.CoerciveForm.harmonicDomain_operator
#check @Carleman.CoerciveForm.harmonicDomain_representative
#check @Carleman.CoerciveForm.harmonicTrajectory
#check @Carleman.CoerciveForm.frequencyTrajectory
#check @Carleman.CoerciveForm.frequencyTrajectory_equation
#check @Carleman.scalarTensor
#check @Carleman.scalarTensor_ae
#check @Carleman.inner_scalarTensor
#check @Carleman.integrable_scalar_smul
#check @Carleman.inner_scalarTensor_integral
#check @Carleman.Orientation.frozenMultiplier
#check @Carleman.CoerciveForm.evolutionFields
#check @Carleman.CoerciveForm.evolution
#check @Carleman.CoerciveForm.evolution_ae
#check @Carleman.CoerciveForm.evolution_eq_iff
#check @Carleman.CoerciveForm.periodicGraph_mem_of_tendsto
#check @Carleman.CoerciveForm.evolution_of_tendsto
#check @Carleman.PeriodicWeakTrajectory.tracePath
#check @Carleman.PeriodicWeakTrajectory.tracePath_on
#check @Carleman.PeriodicWeakTrajectory.tracePath_ae
#check @Carleman.PeriodicWeakTrajectory.tracePathL2_ae
#check @Carleman.PeriodicWeakTrajectory.toPeriodicGraph
#check @Carleman.PeriodicWeakTrajectory.toPeriodicGraph_value_on
#check @Carleman.PeriodicWeakTrajectory.toPeriodicGraph_derivative_ae
#check @Carleman.PeriodicWeakTrajectory.toPeriodicGraph_operator_ae
#check @Carleman.CoerciveForm.PeriodicGraph.trace_injective
#check @Carleman.CoerciveForm.PeriodicGraph.toTrajectory_toPeriodicGraph
#check @Carleman.TimeGrid.PeriodicFields
#check @Carleman.TimeGrid.fieldsValue
#check @Carleman.TimeGrid.fieldsDerivative
#check @Carleman.TimeGrid.fieldsOperator
#check @Carleman.TimeGrid.fieldsTraceDefect
#check @Carleman.CoerciveForm.periodicGraphSubmodule
#check @Carleman.CoerciveForm.PeriodicGraph
#check @Carleman.CoerciveForm.periodicGraph_mem
#check @Carleman.CoerciveForm.periodicGraph_isClosed
#check @Carleman.CoerciveForm.periodicGraph_completeSpace
#check @Carleman.CoerciveForm.PeriodicGraph.toTrajectory
#check @Carleman.CoerciveForm.PeriodicGraph.toTrajectory_operator_ae
#check @Carleman.TimeGrid.TracePath
#check @Carleman.TimeGrid.timeMeasure_finite
#check @Carleman.TimeGrid.clampPath
#check @Carleman.TimeGrid.clampPath_apply
#check @Carleman.TimeGrid.clampPath_on
#check @Carleman.TimeGrid.clampPathCLM
#check @Carleman.TimeGrid.pathL2
#check @Carleman.TimeGrid.pathL2_ae
#check @Carleman.TimeGrid.pathL2_memLp
#check @Carleman.HasWeakTimeDerivative.congr_derivative
#check @Carleman.IsWeakTimeClass
#check @Carleman.IsWeakTimeClass.zero
#check @Carleman.IsWeakTimeClass.add
#check @Carleman.IsWeakTimeClass.smul
#check @Carleman.IsWeakTimeClass.iff_weakDerivative
#check @Carleman.IsWeakTimeClass.eq_zero_of_tests
#check @Carleman.IsWeakTimeClass.unique
#check @Carleman.weakTimeSubmodule
#check @Carleman.weakTimeSubmodule_isClosed
#check @Carleman.weakTimeSubmodule_completeSpace

-- T009: every explicit declaration; recursive audit follows.
#check @Carleman.closedRange_on_core_closure
#check @Carleman.CoerciveForm.exists_constant_periodic_in_core_closure
#check @Carleman.CoerciveForm.evolution_constant_surjective
#check @Carleman.CoerciveForm.existsUnique_constant_periodic
#check @Carleman.CoerciveForm.regularTimeCore_dense
#check @Carleman.CoerciveForm.periodic_graph_cross_zero
#check @Carleman.CoerciveForm.periodic_graph_sq
#check @Carleman.CoerciveForm.exists_constant_weak_periodic
#check @Carleman.BoundedMultiplier.map_sub_norm_le
#check @Carleman.TimeWeightRegularity.shift_frozen_relative
#check @Carleman.CoerciveForm.periodic_graph_perturbation
#check @Carleman.CoerciveForm.frozen_periodic_graph_sq
#check @Carleman.CoerciveForm.frozen_periodic_wellposed
#check @Carleman.CoerciveForm.frozen_periodic_uniform
#check @Carleman.TimeGrid.fourier_coe_trig
#check @Carleman.TimeGrid.scalar_eq_zero_of_harmonics
#check @Carleman.TimeGrid.harmonicSpan
#check @Carleman.TimeGrid.harmonicSpan_dense
#check @Carleman.CoerciveForm.constantEvolutionEquiv
#check @Carleman.CoerciveForm.constantSolve
#check @Carleman.CoerciveForm.constantSolve_equation
#check @Carleman.CoerciveForm.constantStateSolve
#check @Carleman.CoerciveForm.constantStateSolve_eq
#check @Carleman.CoerciveForm.constantStateSolve_bound
#check @Carleman.CoerciveForm.graphH
#check @Carleman.CoerciveForm.graphA
#check @Carleman.CoerciveForm.graphDomain
#check @Carleman.CoerciveForm.graphDomain_operator
#check @Carleman.CoerciveForm.graphH_injective
#check @Carleman.CoerciveForm.graph_symmetric
#check @Carleman.CoerciveForm.graphOfDomain
#check @Carleman.CoerciveForm.IsRegularTimeCore
#check @Carleman.CoerciveForm.regularTimeCore
#check @Carleman.CoerciveForm.frequencyGraph_mem_core
#check @Carleman.CoerciveForm.regularTimeCore_fields
#check @Carleman.TimeWeightRegularity.shiftMultiplier
#check @Carleman.TimeWeightRegularity.shiftMultiplier_nonneg
#check @Carleman.TimeWeightRegularity.shiftMultiplier_endpoint
#check @Carleman.TimeWeightRegularity.shiftMultiplier_derivative
#check @Carleman.TimeWeightRegularity.shiftMultiplier_absolutelyContinuous
#check @Carleman.CoerciveForm.shifted_periodic_graph_sq
#check @Carleman.CoerciveForm.shifted_periodic_wellposed
#check @Carleman.CoerciveForm.time_state_bound
#check @Carleman.CoerciveForm.periodic_trace_bound
#check @Carleman.CoerciveForm.regularTimeCore_norm_bound
#check @Carleman.CoerciveForm.exists_operator_positive_constant
#check @Carleman.CoerciveForm.time_graph_positive
#check @Carleman.CoerciveForm.periodic_time_inner_zero
#check @Carleman.CoerciveForm.regularTimeCore_cross_zero
#check @Carleman.CoerciveForm.evolution_constant
#check @Carleman.CoerciveForm.regularTimeCore_graph_sq
#check @Carleman.compact_subset_period_bounds
#check @Carleman.exists_time_test_primitive
#check @Carleman.exists_time_test_integral_one
#check @Carleman.TimeGrid.timeMeasure_real_univ
#check @Carleman.TimeGrid.timeUnit
#check @Carleman.TimeGrid.timeUnit_ae
#check @Carleman.TimeGrid.timeUnit_norm
#check @Carleman.TimeGrid.integral_norm_le_l2
#check @Carleman.HasWeakTimeDerivative.norm_sub_le_integral_norm
#check @Carleman.HasWeakTimeDerivative.trace_bound
#check @Carleman.BoundedMultiplier.positiveComplement
#check @Carleman.CoerciveForm.evolution_positiveComplement
#check @Carleman.CoerciveForm.evolution_surjective
#check @Carleman.CoerciveForm.existsUnique_variable_periodic
#check @Carleman.CoerciveForm.exists_variable_weak_periodic
#check @Carleman.CoerciveForm.exists_frozen_weak_periodic
#check @Carleman.CoerciveForm.IsAssociated.exists_variable_weak_periodic
#check @Carleman.CoerciveForm.IsAssociated.weak_periodic_unique
#check @Carleman.PeriodicWeakTrajectory.coefficient_energy
#check @Carleman.CoerciveForm.periodic_coefficient_inner
#check @Carleman.CoerciveForm.periodic_coefficient_sq
#check @Carleman.CoerciveForm.periodic_coefficient_nonneg
#check @Carleman.CoerciveForm.variable_periodic_graph_sq
#check @Carleman.integrable_inner_of_memLp
#check @Carleman.CoerciveForm.operator_energy_zero
#check @Carleman.CoerciveForm.weak_periodic_kernel
#check @Carleman.CoerciveForm.evolution_injective
#check @Carleman.CoerciveForm.weak_periodic_unique
#check @Carleman.TimeGrid.timeIntegral_of_test_support
#check @Carleman.HasWeakTimeDerivative.ae_const_of_zero
#check @Carleman.HasWeakTimeDerivative.const_of_zero
#check @Carleman.absolutelyContinuous_of_dist_le
#check @Carleman.HasWeakTimeDerivative.absolutelyContinuous
#check @Carleman.HasWeakTimeDerivative.ae_hasDerivAt
#check @Carleman.HasWeakTimeDerivative.energy_identity
#check @Carleman.PeriodicWeakTrajectory.time_energy_zero
#check @Carleman.HasWeakTimeDerivative.integral_eq
#check @Carleman.HasWeakTimeDerivative.integral_eq_sub
#check @Carleman.TimeGrid.intervalIntegrable_of_memLp
#check @Carleman.TimeGrid.primitive_continuousOn
#check @Carleman.HasWeakTimeDerivative.scalar_primitive
#check @Carleman.HasWeakTimeDerivative.primitive
#check @Carleman.LoadInterface.exists_frozen_transfer_trajectory

-- T010: every explicit declaration of this spatial stage.
#check @Carleman.WeakSobolevJet.lower_parameterNorm_le
#check @Carleman.conjugatedCommutator
#check @Carleman.conjugatedCommutator_eq
#check @Carleman.conjugatedCommutator_parameter_le
#check @Carleman.derivativeComponent_multiplier
#check @Carleman.derivativeField_norm_sq
#check @Carleman.derivativeField_scaled_bound
#check @Carleman.WeakSobolevJet.wordField_vector
#check @Carleman.WeakSobolevJet.weighted_leibnizField_bound
#check @Carleman.wordIndex
#check @Carleman.wordIndex_cons
#check @Carleman.WeakSobolevJet.wordField
#check @Carleman.WeakSobolevJet.wordField_nil
#check @Carleman.WeakSobolevJet.wordField_weak
#check @Carleman.WeakSobolevJet.wordField_norm_le
#check @Carleman.IsWeakSpatialDerivative.list_sum
#check @Carleman.derivativeSplits
#check @Carleman.derivativeSplits_lengths
#check @Carleman.derivativeSplits_length
#check @Carleman.norm_list_sum_le
#check @Carleman.WeakSobolevJet.parameterNorm
#check @Carleman.WeakSobolevJet.parameterNorm_nonneg
#check @Carleman.WeakSobolevJet.parameterNorm_component
#check @Carleman.WeakSobolevJet.wordField_weighted_le
#check @Carleman.WeakSobolevJet.leibniz_term_bound
#check @Carleman.WeakSobolevJet.leibnizField_bound
#check @Carleman.BoundedMultiplier.one
#check @Carleman.BoundedMultiplier.mul
#check @Carleman.BoundedMultiplier.one_map
#check @Carleman.BoundedMultiplier.one_seminorm
#check @Carleman.BoundedMultiplier.mul_map
#check @Carleman.BoundedMultiplier.map_inverse
#check @Carleman.WeakSobolevJet.leibnizConstant
#check @Carleman.WeakSobolevJet.leibnizConstant_pos
#check @Carleman.WeakSobolevJet.parameterNorm_mono
#check @Carleman.WeakSobolevJet.parameterNorm_leibniz_bound
#check @Carleman.WeakSobolevJet.weightedNorm_le_parameterNorm
#check @Carleman.WeakSobolevJet.parameterNorm_le_weightedNorm
#check @Carleman.conformingWeight
#check @Carleman.conformingWeightedNorm
#check @Carleman.conformingWeightedNorm_nonneg
#check @Carleman.conformingWeightedNorm_value
#check @Carleman.shiftedForm
#check @Carleman.weighted_pairing_le
#check @Carleman.shiftedForm_bound
#check @Carleman.shiftedForm_weighted
#check @Carleman.shiftedForm_coercive
#check @Carleman.shiftedForm_margin_threshold
#check @Carleman.smoothWordMultiplier
#check @Carleman.smoothWordMultiplier_smooth
#check @Carleman.smoothWordMultiplier_derivative
#check @Carleman.smoothWordMultiplier_nil
#check @Carleman.weak_leibniz_smooth
#check @Carleman.WeakSobolevJet.leibnizField
#check @Carleman.WeakSobolevJet.leibnizField_nil
#check @Carleman.WeakSobolevJet.leibnizField_weak
#check @Carleman.WeakSobolevJet.wordField_mul
#check @Carleman.WeakSobolevJet.weightedSq
#check @Carleman.WeakSobolevJet.weightedNorm
#check @Carleman.WeakSobolevJet.weightedSq_nonneg
#check @Carleman.WeakSobolevJet.weightedNorm_nonneg
#check @Carleman.WeakSobolevJet.weightedNorm_sq
#check @Carleman.WeakSobolevJet.weighted_component_le
#check @Carleman.WeakSobolevJet.weighted_zero_eq
#check @Carleman.WeakSobolevJet.weighted_value_le
#check @Carleman.WeakSobolevJet.weightedSq_eq_sum_norm
#check @Carleman.BoundedMultiplier.inner_inverse
#check @Carleman.BoundedMultiplier.inner_map_twice
#check @Carleman.SpatialProfile.multiplier_inverse
#check @Carleman.SpatialProfile.multiplier_inverse_map
#check @Carleman.allowed_shiftedForm_bound
#check @Carleman.allowed_shiftedForm_coercive_uniform
#check @Carleman.conformingParameterNorm
#check @Carleman.conforming_conjugation_uniform
#check @Carleman.wordVector
#check @Carleman.wordDerivative
#check @Carleman.wordDerivative_nil
#check @Carleman.wordVector_cons_get
#check @Carleman.wordDerivative_cons
#check @Carleman.wordDerivative_smooth
#check @Carleman.exists_profile_actual_bound
#check @Carleman.allowedWeight_word_derivatives_uniform
#check @Carleman.smooth_parameterNorm_bound
#check @Carleman.allowedWeight_parameterNorm_uniform
#check @Carleman.allowedWeight_weightedNorm_uniform

-- T011: every explicit declaration and its recursive dependency axioms.
#check @Carleman.bochnerL2Norm
#print axioms Carleman.bochnerL2Norm
#check @Carleman.bochnerL2Norm_eq
#print axioms Carleman.bochnerL2Norm_eq
#check @Carleman.bochnerL2Norm_nonneg
#print axioms Carleman.bochnerL2Norm_nonneg
#check @Carleman.bochnerL2Norm_norm
#print axioms Carleman.bochnerL2Norm_norm
#check @Carleman.bochnerL2Norm_add
#print axioms Carleman.bochnerL2Norm_add
#check @Carleman.bochnerL2Norm_finsetSum
#print axioms Carleman.bochnerL2Norm_finsetSum
#check @Carleman.memLp_of_le_sum_norm
#print axioms Carleman.memLp_of_le_sum_norm
#check @Carleman.bochnerL2Norm_le_sum
#print axioms Carleman.bochnerL2Norm_le_sum
#check @Carleman.aestronglyMeasurable_of_injective_clm
#print axioms Carleman.aestronglyMeasurable_of_injective_clm
#check @Carleman.CoerciveForm.operator_aestronglyMeasurable
#print axioms Carleman.CoerciveForm.operator_aestronglyMeasurable
#check @Carleman.CoerciveForm.IsAssociated.operator_aestronglyMeasurable
#print axioms Carleman.CoerciveForm.IsAssociated.operator_aestronglyMeasurable
#check @Carleman.absolutelyContinuous_clm_apply
#print axioms Carleman.absolutelyContinuous_clm_apply
#check @Carleman.HasWeakTimeDerivative.of_ac_ae
#print axioms Carleman.HasWeakTimeDerivative.of_ac_ae
#check @Carleman.HasWeakTimeDerivative.clm_apply
#print axioms Carleman.HasWeakTimeDerivative.clm_apply
#check @Carleman.SpatialProfile.expDerivativeCLM
#print axioms Carleman.SpatialProfile.expDerivativeCLM
#check @Carleman.SpatialProfile.expDerivativeCLM_ae
#print axioms Carleman.SpatialProfile.expDerivativeCLM_ae
#check @Carleman.SpatialProfile.exp_scalar_remainder
#print axioms Carleman.SpatialProfile.exp_scalar_remainder
#check @Carleman.SpatialProfile.expCLM_remainder
#print axioms Carleman.SpatialProfile.expCLM_remainder
#check @Carleman.SpatialProfile.hasDerivAt_expCLM
#print axioms Carleman.SpatialProfile.hasDerivAt_expCLM
#check @Carleman.spatialLp_secondCountable
#print axioms Carleman.spatialLp_secondCountable
#check @Carleman.WeakSobolevJet.aestronglyMeasurable_of_value
#print axioms Carleman.WeakSobolevJet.aestronglyMeasurable_of_value
#check @Carleman.WeakSobolevJet.parameterTimeField
#print axioms Carleman.WeakSobolevJet.parameterTimeField
#check @Carleman.WeakSobolevJet.spacetimeParameterNorm
#print axioms Carleman.WeakSobolevJet.spacetimeParameterNorm
#check @Carleman.WeakSobolevJet.parameterTimeField_norm
#print axioms Carleman.WeakSobolevJet.parameterTimeField_norm
#check @Carleman.WeakSobolevJet.parameterNorm_eq_sum_timeField
#print axioms Carleman.WeakSobolevJet.parameterNorm_eq_sum_timeField
#check @Carleman.WeakSobolevJet.memLp_parameterTimeField
#print axioms Carleman.WeakSobolevJet.memLp_parameterTimeField
#check @Carleman.WeakSobolevJet.memLp_unweightedParameterTimeField
#print axioms Carleman.WeakSobolevJet.memLp_unweightedParameterTimeField
#check @Carleman.WeakSobolevJet.spacetimeParameterNorm_le
#print axioms Carleman.WeakSobolevJet.spacetimeParameterNorm_le
#check @Carleman.WeakSobolevJet.norm_le_parameterNorm
#print axioms Carleman.WeakSobolevJet.norm_le_parameterNorm
#check @Carleman.WeakSobolevJet.parameterNorm_global_le
#print axioms Carleman.WeakSobolevJet.parameterNorm_global_le
#check @Carleman.WeakSobolevJet.memLp_of_weighted_value
#print axioms Carleman.WeakSobolevJet.memLp_of_weighted_value
#check @Carleman.allowedCommutatorPath
#print axioms Carleman.allowedCommutatorPath
#check @Carleman.allowedCommutatorPath_eq
#print axioms Carleman.allowedCommutatorPath_eq
#check @Carleman.allowedCommutatorPath_aestronglyMeasurable
#print axioms Carleman.allowedCommutatorPath_aestronglyMeasurable
#check @Carleman.allowedCommutator_spacetime_le
#print axioms Carleman.allowedCommutator_spacetime_le
#check @Carleman.conforming_spacetime_conjugation_uniform
#print axioms Carleman.conforming_spacetime_conjugation_uniform
#check @Carleman.SpatialProfile.weightCLM
#print axioms Carleman.SpatialProfile.weightCLM
#check @Carleman.SpatialProfile.weightCLM_apply
#print axioms Carleman.SpatialProfile.weightCLM_apply
#check @Carleman.SpatialProfile.weightDerivativeCLM
#print axioms Carleman.SpatialProfile.weightDerivativeCLM
#check @Carleman.SpatialProfile.weightDerivativeCLM_apply
#print axioms Carleman.SpatialProfile.weightDerivativeCLM_apply
#check @Carleman.SpatialProfile.hasDerivWithinAt_weightCLM
#print axioms Carleman.SpatialProfile.hasDerivWithinAt_weightCLM
#check @Carleman.SpatialProfile.weightDerivativeCLM_norm_le
#print axioms Carleman.SpatialProfile.weightDerivativeCLM_norm_le
#check @Carleman.SpatialProfile.weightCLM_absolutelyContinuous
#print axioms Carleman.SpatialProfile.weightCLM_absolutelyContinuous
#check @Carleman.SpatialProfile.ae_hasDerivAt_weightCLM
#print axioms Carleman.SpatialProfile.ae_hasDerivAt_weightCLM
#check @Carleman.SpatialProfile.weightCLM_continuousOn
#print axioms Carleman.SpatialProfile.weightCLM_continuousOn
#check @Carleman.SpatialProfile.weightCLM_periodic_trace
#print axioms Carleman.SpatialProfile.weightCLM_periodic_trace
#check @Carleman.PeriodicWeakTrajectory.domainValue_of_weighted
#print axioms Carleman.PeriodicWeakTrajectory.domainValue_of_weighted
#check @Carleman.PeriodicWeakTrajectory.weighted_conjugation_identity
#print axioms Carleman.PeriodicWeakTrajectory.weighted_conjugation_identity
#check @Carleman.SpatialProfile.weightedTimeDerivative
#print axioms Carleman.SpatialProfile.weightedTimeDerivative
#check @Carleman.SpatialProfile.weightedTimeDerivative_L2
#print axioms Carleman.SpatialProfile.weightedTimeDerivative_L2
#check @Carleman.SpatialProfile.hasWeakTimeDerivative_map
#print axioms Carleman.SpatialProfile.hasWeakTimeDerivative_map
#check @Carleman.SpatialProfile.continuousOn_map
#print axioms Carleman.SpatialProfile.continuousOn_map
#check @Carleman.SpatialProfile.map_periodic_trace
#print axioms Carleman.SpatialProfile.map_periodic_trace
#check @Carleman.conformingWeight_inverse
#print axioms Carleman.conformingWeight_inverse
#check @Carleman.weightedOperator_L2
#print axioms Carleman.weightedOperator_L2
#check @Carleman.PeriodicWeakTrajectory.exists_weighted_trajectory
#print axioms Carleman.PeriodicWeakTrajectory.exists_weighted_trajectory

-- T012: every explicit declaration and its recursive dependency axioms.
#check @Carleman.TimeGrid.affinePath
#print axioms Carleman.TimeGrid.affinePath
#check @Carleman.TimeGrid.affineLp
#print axioms Carleman.TimeGrid.affineLp
#check @Carleman.TimeGrid.affineLp_ae
#print axioms Carleman.TimeGrid.affineLp_ae
#check @Carleman.TimeGrid.affineLp_defect_le
#print axioms Carleman.TimeGrid.affineLp_defect_le
#check @Carleman.TimeGrid.affine_bochner_defect_le
#print axioms Carleman.TimeGrid.affine_bochner_defect_le
#check @Carleman.CoerciveForm.timeEnergy
#print axioms Carleman.CoerciveForm.timeEnergy
#check @Carleman.CoerciveForm.timeEnergy_ae
#print axioms Carleman.CoerciveForm.timeEnergy_ae
#check @Carleman.CoerciveForm.timeEnergy_embed
#print axioms Carleman.CoerciveForm.timeEnergy_embed
#check @Carleman.CoerciveForm.timeEnergy_form_ae
#print axioms Carleman.CoerciveForm.timeEnergy_form_ae
#check @Carleman.CoerciveForm.timeEnergy_coercive
#print axioms Carleman.CoerciveForm.timeEnergy_coercive
#check @Carleman.CoerciveForm.temporal_energy_error_uniform
#print axioms Carleman.CoerciveForm.temporal_energy_error_uniform
#check @Carleman.CoerciveForm.eulerExtension_equation
#print axioms Carleman.CoerciveForm.eulerExtension_equation
#check @Carleman.CoerciveForm.eulerExtension_adjoint
#print axioms Carleman.CoerciveForm.eulerExtension_adjoint
#check @Carleman.CoerciveForm.temporal_error_duality
#print axioms Carleman.CoerciveForm.temporal_error_duality
#check @Carleman.CoerciveForm.temporal_l2_error_uniform
#print axioms Carleman.CoerciveForm.temporal_l2_error_uniform
#check @Carleman.TimeGrid.error_bochner_eq
#print axioms Carleman.TimeGrid.error_bochner_eq
#check @Carleman.CoerciveForm.IsAssociated.temporal_weak_error_uniform
#print axioms Carleman.CoerciveForm.IsAssociated.temporal_weak_error_uniform
#check @Carleman.Orientation.opposite
#print axioms Carleman.Orientation.opposite
#check @Carleman.Orientation.opposite_sign
#print axioms Carleman.Orientation.opposite_sign
#check @Carleman.TimeGrid.weak_pairing_L2
#print axioms Carleman.TimeGrid.weak_pairing_L2
#check @Carleman.TimeGrid.affine_weakTimeClass
#print axioms Carleman.TimeGrid.affine_weakTimeClass
#check @Carleman.BoundedMultiplier.map_inner
#print axioms Carleman.BoundedMultiplier.map_inner
#check @Carleman.CoerciveForm.timeOperatorGraph_symmetric
#print axioms Carleman.CoerciveForm.timeOperatorGraph_symmetric
#check @Carleman.CoerciveForm.evolution_adjoint
#print axioms Carleman.CoerciveForm.evolution_adjoint
#check @Carleman.HasWeakTimeDerivative.periodic_pairing
#print axioms Carleman.HasWeakTimeDerivative.periodic_pairing
#check @Carleman.TimeGrid.forwardSlope
#print axioms Carleman.TimeGrid.forwardSlope
#check @Carleman.TimeGrid.affineReconstruction
#print axioms Carleman.TimeGrid.affineReconstruction
#check @Carleman.TimeGrid.intervalIntegrable_extensionMinus_vector_cell
#print axioms Carleman.TimeGrid.intervalIntegrable_extensionMinus_vector_cell
#check @Carleman.TimeGrid.affineReconstruction_node
#print axioms Carleman.TimeGrid.affineReconstruction_node
#check @Carleman.TimeGrid.affineReconstruction_cell
#print axioms Carleman.TimeGrid.affineReconstruction_cell
#check @Carleman.TimeGrid.affineReconstruction_continuousOn
#print axioms Carleman.TimeGrid.affineReconstruction_continuousOn
#check @Carleman.TimeGrid.affineReconstruction_periodic_trace
#print axioms Carleman.TimeGrid.affineReconstruction_periodic_trace
#check @Carleman.TimeGrid.affineReconstruction_weakDerivative
#print axioms Carleman.TimeGrid.affineReconstruction_weakDerivative
#check @Carleman.TimeGrid.ae_open_cell
#print axioms Carleman.TimeGrid.ae_open_cell
#check @Carleman.TimeGrid.forwardSlope_step
#print axioms Carleman.TimeGrid.forwardSlope_step
#check @Carleman.Orientation.signed_difference_on_open_cell
#print axioms Carleman.Orientation.signed_difference_on_open_cell
#check @Carleman.Orientation.signed_difference_ae
#print axioms Carleman.Orientation.signed_difference_ae
#check @Carleman.Orientation.affine_defect_on_open_cell
#print axioms Carleman.Orientation.affine_defect_on_open_cell
#check @Carleman.Orientation.affine_defect_ae
#print axioms Carleman.Orientation.affine_defect_ae

-- T013: every explicit declaration and its recursive dependency axioms.
#check @Carleman.intrinsicWordMultiplier
#print axioms Carleman.intrinsicWordMultiplier
#check @Carleman.intrinsicWordMultiplier_smooth
#print axioms Carleman.intrinsicWordMultiplier_smooth
#check @Carleman.intrinsicWordMultiplier_derivative
#print axioms Carleman.intrinsicWordMultiplier_derivative
#check @Carleman.intrinsicWordMultiplier_nil
#print axioms Carleman.intrinsicWordMultiplier_nil
#check @Carleman.weak_leibniz_intrinsic
#print axioms Carleman.weak_leibniz_intrinsic
#check @Carleman.bochnerL2Norm_sq_integral
#print axioms Carleman.bochnerL2Norm_sq_integral
#check @Carleman.WeakSobolevJet.spacetimeWeightedSq
#print axioms Carleman.WeakSobolevJet.spacetimeWeightedSq
#check @Carleman.WeakSobolevJet.spacetimeWeightedNorm
#print axioms Carleman.WeakSobolevJet.spacetimeWeightedNorm
#check @Carleman.WeakSobolevJet.spacetimeWeightedNorm_nonneg
#print axioms Carleman.WeakSobolevJet.spacetimeWeightedNorm_nonneg
#check @Carleman.WeakSobolevJet.spacetimeWeightedNorm_sq
#print axioms Carleman.WeakSobolevJet.spacetimeWeightedNorm_sq
#check @Carleman.WeakSobolevJet.weightedSq_eq_timeFields
#print axioms Carleman.WeakSobolevJet.weightedSq_eq_timeFields
#check @Carleman.WeakSobolevJet.weightedSq_integrable
#print axioms Carleman.WeakSobolevJet.weightedSq_integrable
#check @Carleman.WeakSobolevJet.spacetimeWeightedSq_integral
#print axioms Carleman.WeakSobolevJet.spacetimeWeightedSq_integral
#check @Carleman.WeakSobolevJet.spacetimeWeightedNorm_le
#print axioms Carleman.WeakSobolevJet.spacetimeWeightedNorm_le
#check @Carleman.BoundedMultiplier.inner_map_pair
#print axioms Carleman.BoundedMultiplier.inner_map_pair
#check @Carleman.shiftedOperator_weighted_pair
#print axioms Carleman.shiftedOperator_weighted_pair
#check @Carleman.shiftedOperator_weighted_energy
#print axioms Carleman.shiftedOperator_weighted_energy
#check @Carleman.shiftedOperator_spacetime_energy
#print axioms Carleman.shiftedOperator_spacetime_energy
#check @Carleman.allowed_spacetime_operator_energy_uniform
#print axioms Carleman.allowed_spacetime_operator_energy_uniform
#check @Carleman.closure_conforming_conjugation_uniform
#print axioms Carleman.closure_conforming_conjugation_uniform
#check @Carleman.closureDerivative_extension_unique
#print axioms Carleman.closureDerivative_extension_unique
#check @Carleman.SpatialProfile.ofSmoothOnClosure
#print axioms Carleman.SpatialProfile.ofSmoothOnClosure
#check @Carleman.SpatialProfile.ofSmoothOnClosure_value
#print axioms Carleman.SpatialProfile.ofSmoothOnClosure_value
#check @Carleman.closure_spacetime_conjugation_uniform
#print axioms Carleman.closure_spacetime_conjugation_uniform
#check @Carleman.closure_spacetime_energy_conjugation_uniform
#print axioms Carleman.closure_spacetime_energy_conjugation_uniform
#check @Carleman.PeriodicWeakTrajectory.exists_closure_weighted_trajectory
#print axioms Carleman.PeriodicWeakTrajectory.exists_closure_weighted_trajectory
#check @Carleman.intrinsic_parameterNorm_bound
#print axioms Carleman.intrinsic_parameterNorm_bound
#check @Carleman.intrinsic_allowedWeight_parameterNorm_uniform
#print axioms Carleman.intrinsic_allowedWeight_parameterNorm_uniform
#check @Carleman.intrinsic_allowedWeight_weightedNorm_uniform
#print axioms Carleman.intrinsic_allowedWeight_weightedNorm_uniform
#check @Carleman.BoundedSmoothOn.allowedWeight_actual_uniform
#print axioms Carleman.BoundedSmoothOn.allowedWeight_actual_uniform
#check @Carleman.BoundedSmoothOn.allowedWeight_word_uniform
#print axioms Carleman.BoundedSmoothOn.allowedWeight_word_uniform
#check @Carleman.BoundedSmoothOn.allowedWeight
#print axioms Carleman.BoundedSmoothOn.allowedWeight
#check @Carleman.tensorCoordinates
#print axioms Carleman.tensorCoordinates
#check @Carleman.tensorCoordinates_injective
#print axioms Carleman.tensorCoordinates_injective
#check @Carleman.tensorReconstruction
#print axioms Carleman.tensorReconstruction
#check @Carleman.tensorReconstruction_coordinates
#print axioms Carleman.tensorReconstruction_coordinates
#check @Carleman.SmoothOnClosure
#print axioms Carleman.SmoothOnClosure
#check @Carleman.CoordinateSmoothOnClosure
#print axioms Carleman.CoordinateSmoothOnClosure
#check @Carleman.smoothOnClosure_iff_coordinate
#print axioms Carleman.smoothOnClosure_iff_coordinate
#check @Carleman.SmoothOnClosure.of_neighborhood
#print axioms Carleman.SmoothOnClosure.of_neighborhood
#check @Carleman.SmoothOnClosure.neg
#print axioms Carleman.SmoothOnClosure.neg
#check @Carleman.SmoothOnClosure.congr
#print axioms Carleman.SmoothOnClosure.congr
#check @Carleman.BoundedSmoothOn
#print axioms Carleman.BoundedSmoothOn
#check @Carleman.SmoothOnClosure.boundedSmoothOn
#print axioms Carleman.SmoothOnClosure.boundedSmoothOn

-- T014: every explicit declaration and its recursive dependency axioms.
#check @Carleman.bochnerL2Norm_congr_ae
#print axioms Carleman.bochnerL2Norm_congr_ae
#check @Carleman.bochnerL2Norm_neg
#print axioms Carleman.bochnerL2Norm_neg
#check @Carleman.bochnerL2Norm_sub
#print axioms Carleman.bochnerL2Norm_sub
#check @Carleman.bochnerL2Norm_const_smul
#print axioms Carleman.bochnerL2Norm_const_smul
#check @Carleman.PeriodicWeakTrajectory.domainError
#print axioms Carleman.PeriodicWeakTrajectory.domainError
#check @Carleman.PeriodicWeakTrajectory.domainError_value_ae
#print axioms Carleman.PeriodicWeakTrajectory.domainError_value_ae
#check @Carleman.PeriodicWeakTrajectory.domainError_L2
#print axioms Carleman.PeriodicWeakTrajectory.domainError_L2
#check @Carleman.PeriodicWeakTrajectory.domainError_operator_L2
#print axioms Carleman.PeriodicWeakTrajectory.domainError_operator_L2
#check @Carleman.PeriodicWeakTrajectory.domainError_residual_ae
#print axioms Carleman.PeriodicWeakTrajectory.domainError_residual_ae
#check @Carleman.FrozenEulerPair
#print axioms Carleman.FrozenEulerPair
#check @Carleman.CoerciveForm.IsAssociated.nonempty_frozenEulerPair
#print axioms Carleman.CoerciveForm.IsAssociated.nonempty_frozenEulerPair
#check @Carleman.SpatialTest.convolution_square_le
#print axioms Carleman.SpatialTest.convolution_square_le
#check @Carleman.SpatialTest.convolution_memLp_norm_le
#print axioms Carleman.SpatialTest.convolution_memLp_norm_le
#check @Carleman.discrete_convex_maximum
#print axioms Carleman.discrete_convex_maximum
#check @Carleman.discrete_logConvex_maximum
#print axioms Carleman.discrete_logConvex_maximum
#check @Carleman.shrinkingBump
#print axioms Carleman.shrinkingBump
#check @Carleman.spatialMollifier
#print axioms Carleman.spatialMollifier
#check @Carleman.spatialMollifier_nonneg
#print axioms Carleman.spatialMollifier_nonneg
#check @Carleman.spatialMollifier_integral
#print axioms Carleman.spatialMollifier_integral
#check @Carleman.spatialMollifier_converges
#print axioms Carleman.spatialMollifier_converges
#check @Carleman.weak_spatial_chain_norm_sq_le
#print axioms Carleman.weak_spatial_chain_norm_sq_le
#check @Carleman.WeakSobolevJet.componentMaximum
#print axioms Carleman.WeakSobolevJet.componentMaximum
#check @Carleman.WeakSobolevJet.component_le_maximum
#print axioms Carleman.WeakSobolevJet.component_le_maximum
#check @Carleman.WeakSobolevJet.componentMaximum_le_field
#print axioms Carleman.WeakSobolevJet.componentMaximum_le_field
#check @Carleman.WeakSobolevJet.componentMaximum_zero
#print axioms Carleman.WeakSobolevJet.componentMaximum_zero
#check @Carleman.WeakSobolevJet.component_neighbor_sq_le
#print axioms Carleman.WeakSobolevJet.component_neighbor_sq_le
#check @Carleman.WeakSobolevJet.componentMaximum_logConvex
#print axioms Carleman.WeakSobolevJet.componentMaximum_logConvex
#check @Carleman.WeakSobolevJet.scaled_componentMaximum_le
#print axioms Carleman.WeakSobolevJet.scaled_componentMaximum_le
#check @Carleman.WeakSobolevJet.fullSpace_parameter_interpolation
#print axioms Carleman.WeakSobolevJet.fullSpace_parameter_interpolation
#check @Carleman.WeakSobolevJet.fullSpace_parameter_interpolation_uniform
#print axioms Carleman.WeakSobolevJet.fullSpace_parameter_interpolation_uniform
#check @Carleman.shiftedForm_coercive_of_lower
#print axioms Carleman.shiftedForm_coercive_of_lower
#check @Carleman.shiftedOperator_weighted_energy_of_lower
#print axioms Carleman.shiftedOperator_weighted_energy_of_lower
#check @Carleman.shiftedOperator_spacetime_energy_of_lower
#print axioms Carleman.shiftedOperator_spacetime_energy_of_lower
#check @Carleman.real_convolution_comm
#print axioms Carleman.real_convolution_comm
#check @Carleman.SpatialTest.convolution_right_memLp_norm_le
#print axioms Carleman.SpatialTest.convolution_right_memLp_norm_le
#check @Carleman.SpatialTest.weak_chain_convolution_sq_le
#print axioms Carleman.SpatialTest.weak_chain_convolution_sq_le
#check @Carleman.integral_mul_eq_L2_inner
#print axioms Carleman.integral_mul_eq_L2_inner
#check @Carleman.integral_sq_eq_bochnerL2Norm_sq
#print axioms Carleman.integral_sq_eq_bochnerL2Norm_sq
#check @Carleman.integral_mul_sq_le
#print axioms Carleman.integral_mul_sq_le
#check @Carleman.abs_integral_mul_le
#print axioms Carleman.abs_integral_mul_le
#check @Carleman.SpatialTest.reflected
#print axioms Carleman.SpatialTest.reflected
#check @Carleman.SpatialTest.reflected_derivative
#print axioms Carleman.SpatialTest.reflected_derivative
#check @Carleman.IsWeakSpatialDerivative.convolution_exchange
#print axioms Carleman.IsWeakSpatialDerivative.convolution_exchange
#check @Carleman.IsWeakSpatialDerivative.fderiv_convolution
#print axioms Carleman.IsWeakSpatialDerivative.fderiv_convolution
#check @Carleman.SpatialTest.smooth_convolution
#print axioms Carleman.SpatialTest.smooth_convolution
#check @Carleman.PeriodicWeakTrajectory.domainError_conforming_L2
#print axioms Carleman.PeriodicWeakTrajectory.domainError_conforming_L2
#check @Carleman.frozen_error_energy_uniform
#print axioms Carleman.frozen_error_energy_uniform
#check @Carleman.frozen_spacetime_operator_energy_uniform
#print axioms Carleman.frozen_spacetime_operator_energy_uniform
#check @Carleman.TimeWeightRegularity.frozen_shift_lower
#print axioms Carleman.TimeWeightRegularity.frozen_shift_lower
#check @Carleman.TimeWeightRegularity.frozen_shift_lower_ae
#print axioms Carleman.TimeWeightRegularity.frozen_shift_lower_ae
#check @Carleman.frozen_shift_margin_uniform
#print axioms Carleman.frozen_shift_margin_uniform

-- T015: every explicit declaration and its recursive dependency axioms.
#check @Carleman.CoerciveForm.weighted_temporal_duality
#print axioms Carleman.CoerciveForm.weighted_temporal_duality
#check @Carleman.CoerciveForm.weighted_temporal_duality_bound
#print axioms Carleman.CoerciveForm.weighted_temporal_duality_bound
#check @Carleman.CoerciveForm.weighted_temporal_duality_uniform
#print axioms Carleman.CoerciveForm.weighted_temporal_duality_uniform
#check @Carleman.Orientation.affine_defect_scalar_ae
#print axioms Carleman.Orientation.affine_defect_scalar_ae
#check @Carleman.Orientation.affine_defect_seminorm_ae
#print axioms Carleman.Orientation.affine_defect_seminorm_ae
#check @Carleman.SpatialProfile.logDerivative_frozen_small_uniform
#print axioms Carleman.SpatialProfile.logDerivative_frozen_small_uniform
#check @Carleman.SpatialProfile.timeMap
#print axioms Carleman.SpatialProfile.timeMap
#check @Carleman.SpatialProfile.timeMap_ae
#print axioms Carleman.SpatialProfile.timeMap_ae
#check @Carleman.SpatialProfile.timeMap_toLp
#print axioms Carleman.SpatialProfile.timeMap_toLp
#check @Carleman.SpatialProfile.timeMap_norm_le
#print axioms Carleman.SpatialProfile.timeMap_norm_le
#check @Carleman.SpatialProfile.timeMap_inverse
#print axioms Carleman.SpatialProfile.timeMap_inverse
#check @Carleman.SpatialProfile.timeMap_inner_inverse
#print axioms Carleman.SpatialProfile.timeMap_inner_inverse
#check @Carleman.SpatialProfile.timeMap_inner_twice
#print axioms Carleman.SpatialProfile.timeMap_inner_twice
#check @Carleman.CoerciveForm.weighted_adjoint_remainder_uniform
#print axioms Carleman.CoerciveForm.weighted_adjoint_remainder_uniform
#check @Carleman.SpatialProfile.timeMap_extension_norm_sq
#print axioms Carleman.SpatialProfile.timeMap_extension_norm_sq
#check @Carleman.SpatialProfile.timeMap_extension_norm_comparison
#print axioms Carleman.SpatialProfile.timeMap_extension_norm_comparison
#check @Carleman.SpatialProfile.timeMap_affine_defect_le
#print axioms Carleman.SpatialProfile.timeMap_affine_defect_le
#check @Carleman.SpatialProfile.weighted_affine_bochner_defect
#print axioms Carleman.SpatialProfile.weighted_affine_bochner_defect
#check @Carleman.SpatialProfile.weighted_affine_defect_uniform
#print axioms Carleman.SpatialProfile.weighted_affine_defect_uniform
#check @Carleman.CoerciveForm.weighted_graph_domain_ae
#print axioms Carleman.CoerciveForm.weighted_graph_domain_ae
#check @Carleman.CoerciveForm.weighted_graph_commutator_ae
#print axioms Carleman.CoerciveForm.weighted_graph_commutator_ae
#check @Carleman.CoerciveForm.exists_weighted_graph
#print axioms Carleman.CoerciveForm.exists_weighted_graph
#check @Carleman.CoerciveForm.exists_weighted_frozen_graph_remainder_uniform
#print axioms Carleman.CoerciveForm.exists_weighted_frozen_graph_remainder_uniform
#check @Carleman.SpatialProfile.timeMap_commute_multiplier
#print axioms Carleman.SpatialProfile.timeMap_commute_multiplier
#check @Carleman.linear_evolution_residual
#print axioms Carleman.linear_evolution_residual
#check @Carleman.CoerciveForm.weighted_evolution_identity
#print axioms Carleman.CoerciveForm.weighted_evolution_identity
#check @Carleman.CoerciveForm.weighted_frozen_graph_remainder_uniform
#print axioms Carleman.CoerciveForm.weighted_frozen_graph_remainder_uniform

-- T016: every explicit declaration and its recursive dependency axioms.
#check @Carleman.bochnerL2Norm_coe
#print axioms Carleman.bochnerL2Norm_coe
#check @Carleman.lp_norm_le_two
#print axioms Carleman.lp_norm_le_two
#check @Carleman.TimeGrid.l2Norm_le_two
#print axioms Carleman.TimeGrid.l2Norm_le_two
#check @Carleman.SpatialProfile.timeMap_bochnerNorm
#print axioms Carleman.SpatialProfile.timeMap_bochnerNorm
#check @Carleman.SpatialProfile.timeMap_extension_bochnerNorm
#print axioms Carleman.SpatialProfile.timeMap_extension_bochnerNorm
#check @Carleman.CoerciveForm.PeriodicGraph.frozenEulerPair
#print axioms Carleman.CoerciveForm.PeriodicGraph.frozenEulerPair
#check @Carleman.CoerciveForm.PeriodicGraph.weighted_derivative_bochnerNorm
#print axioms Carleman.CoerciveForm.PeriodicGraph.weighted_derivative_bochnerNorm
#check @Carleman.CoerciveForm.PeriodicGraph.weighted_error_bochnerNorm
#print axioms Carleman.CoerciveForm.PeriodicGraph.weighted_error_bochnerNorm
#check @Carleman.TimeGrid.l2Norm_add_le
#print axioms Carleman.TimeGrid.l2Norm_add_le
#check @Carleman.TimeGrid.l2Norm_neg
#print axioms Carleman.TimeGrid.l2Norm_neg
#check @Carleman.TimeGrid.l2Norm_sub_le
#print axioms Carleman.TimeGrid.l2Norm_sub_le
#check @Carleman.TimeGrid.l2Norm_comp_equiv
#print axioms Carleman.TimeGrid.l2Norm_comp_equiv
#check @Carleman.weighted_lowOrder_absorption
#print axioms Carleman.weighted_lowOrder_absorption
#check @Carleman.secondOrder_lower_sum_le
#print axioms Carleman.secondOrder_lower_sum_le
#check @Carleman.conjugatedCommutator_weighted_eq
#print axioms Carleman.conjugatedCommutator_weighted_eq
#check @Carleman.secondOrder_commutator_small_shift
#print axioms Carleman.secondOrder_commutator_small_shift
#check @Carleman.secondOrder_parameter_graph_uniform
#print axioms Carleman.secondOrder_parameter_graph_uniform
#check @Carleman.SecondOrderWeightData
#print axioms Carleman.SecondOrderWeightData
#check @Carleman.SpatialProfile.neg_neg_profile
#print axioms Carleman.SpatialProfile.neg_neg_profile
#check @Carleman.SpatialProfile.inverse_timeMap_left
#print axioms Carleman.SpatialProfile.inverse_timeMap_left
#check @Carleman.TimeWeightRegularity.weight_oriented_quotient
#print axioms Carleman.TimeWeightRegularity.weight_oriented_quotient
#check @Carleman.SpatialProfile.nodeMap
#print axioms Carleman.SpatialProfile.nodeMap
#check @Carleman.SpatialProfile.eulerTimeCommutator
#print axioms Carleman.SpatialProfile.eulerTimeCommutator
#check @Carleman.SpatialProfile.eulerTimeCommutator_eq
#print axioms Carleman.SpatialProfile.eulerTimeCommutator_eq
#check @Carleman.SpatialProfile.eulerTimeCommutator_node_le
#print axioms Carleman.SpatialProfile.eulerTimeCommutator_node_le
#check @Carleman.SpatialProfile.eulerTimeCommutator_small_uniform
#print axioms Carleman.SpatialProfile.eulerTimeCommutator_small_uniform
#check @Carleman.CoerciveForm.secondOrder_weighted_euler_graph_uniform
#print axioms Carleman.CoerciveForm.secondOrder_weighted_euler_graph_uniform
#check @Carleman.WeakSobolevJet.nodeParameterNorm
#print axioms Carleman.WeakSobolevJet.nodeParameterNorm
#check @Carleman.CoerciveForm.secondOrder_weighted_euler_sobolev_uniform
#print axioms Carleman.CoerciveForm.secondOrder_weighted_euler_sobolev_uniform
#check @Carleman.CoerciveForm.secondOrder_weighted_frozen_graph_uniform
#print axioms Carleman.CoerciveForm.secondOrder_weighted_frozen_graph_uniform
#check @Carleman.CoerciveForm.secondOrder_weighted_temporal_error_uniform
#print axioms Carleman.CoerciveForm.secondOrder_weighted_temporal_error_uniform
#check @Carleman.CoerciveForm.secondOrder_weighted_temporal_l2_uniform
#print axioms Carleman.CoerciveForm.secondOrder_weighted_temporal_l2_uniform
#check @Carleman.SpatialProfile.weightedNodes
#print axioms Carleman.SpatialProfile.weightedNodes
#check @Carleman.SpatialProfile.weightedNodes_value
#print axioms Carleman.SpatialProfile.weightedNodes_value
#check @Carleman.SpatialProfile.nodeMap_l2Norm
#print axioms Carleman.SpatialProfile.nodeMap_l2Norm
#check @Carleman.CoerciveForm.weighted_euler_identity
#print axioms Carleman.CoerciveForm.weighted_euler_identity
#check @Carleman.CoerciveForm.weighted_euler_graph_remainder_uniform
#print axioms Carleman.CoerciveForm.weighted_euler_graph_remainder_uniform

-- T017: actual declarations, followed by the recursive project-wide audit.
#check @Carleman.InwardConePatch
#print axioms Carleman.InwardConePatch
#check @Carleman.lipschitz_graph_inward_ball
#print axioms Carleman.lipschitz_graph_inward_ball
#check @Carleman.InwardConePatch.ofGraph
#print axioms Carleman.InwardConePatch.ofGraph
#check @Carleman.InwardConePatch.ofInterior
#print axioms Carleman.InwardConePatch.ofInterior
#check @Carleman.HasLipschitzGraphCharts
#print axioms Carleman.HasLipschitzGraphCharts
#check @Carleman.exists_inwardConePatch_of_mem_closure
#print axioms Carleman.exists_inwardConePatch_of_mem_closure
#check @Carleman.finite_uniform_inwardCone_cover
#print axioms Carleman.finite_uniform_inwardCone_cover
#check @Carleman.AllowedWeightData
#print axioms Carleman.AllowedWeightData
#check @Carleman.DomainParameterInterpolation
#print axioms Carleman.DomainParameterInterpolation
#check @Carleman.fullSpace_domain_parameter_interpolation
#print axioms Carleman.fullSpace_domain_parameter_interpolation
#check @Carleman.interpolated_commutator_small_shift
#print axioms Carleman.interpolated_commutator_small_shift
#check @Carleman.interpolated_parameter_graph_uniform
#print axioms Carleman.interpolated_parameter_graph_uniform
#check @Carleman.CoerciveForm.interpolated_weighted_euler_graph_uniform
#print axioms Carleman.CoerciveForm.interpolated_weighted_euler_graph_uniform
#check @Carleman.CoerciveForm.interpolated_weighted_euler_sobolev_uniform
#print axioms Carleman.CoerciveForm.interpolated_weighted_euler_sobolev_uniform
#check @Carleman.CoerciveForm.interpolated_weighted_frozen_graph_uniform
#print axioms Carleman.CoerciveForm.interpolated_weighted_frozen_graph_uniform
#check @Carleman.CoerciveForm.interpolated_weighted_temporal_error_uniform
#print axioms Carleman.CoerciveForm.interpolated_weighted_temporal_error_uniform
#check @Carleman.CoerciveForm.interpolated_weighted_temporal_l2_uniform
#print axioms Carleman.CoerciveForm.interpolated_weighted_temporal_l2_uniform


-- T018: original-domain interpolation and its actual weighted consequences.
#check @Carleman.interiorRegion
#print axioms Carleman.interiorRegion
#check @Carleman.isOpen_interiorRegion
#print axioms Carleman.isOpen_interiorRegion
#check @Carleman.interiorRegion_subset
#print axioms Carleman.interiorRegion_subset
#check @Carleman.interiorRegion_closedBall_subset
#print axioms Carleman.interiorRegion_closedBall_subset
#check @Carleman.eventually_mem_interiorRegion
#print axioms Carleman.eventually_mem_interiorRegion
#check @Carleman.InwardConePatch.tube_subset
#print axioms Carleman.InwardConePatch.tube_subset
#check @Carleman.LocalLipschitzGraphChart
#print axioms Carleman.LocalLipschitzGraphChart
#check @Carleman.IsBoundedLipschitzDomain
#print axioms Carleman.IsBoundedLipschitzDomain
#check @Carleman.LocalLipschitzGraphChart.exists_global_graph
#print axioms Carleman.LocalLipschitzGraphChart.exists_global_graph
#check @Carleman.IsBoundedLipschitzDomain.global_graph_charts
#print axioms Carleman.IsBoundedLipschitzDomain.global_graph_charts
#check @Carleman.HasLipschitzGraphCharts.local_charts
#print axioms Carleman.HasLipschitzGraphCharts.local_charts
#check @Carleman.boundedLipschitz_iff_global_graph_charts
#print axioms Carleman.boundedLipschitz_iff_global_graph_charts
#check @Carleman.IsBoundedLipschitzDomain.finite_uniform_cones
#print axioms Carleman.IsBoundedLipschitzDomain.finite_uniform_cones
#check @Carleman.coneCoordinateConstant
#print axioms Carleman.coneCoordinateConstant
#check @Carleman.coneCoordinateConstant_nonneg
#print axioms Carleman.coneCoordinateConstant_nonneg
#check @Carleman.weak_cone_coordinate_interpolation
#print axioms Carleman.weak_cone_coordinate_interpolation
#check @Carleman.discrete_interpolation_maximum
#print axioms Carleman.discrete_interpolation_maximum
#check @Carleman.IsWeakSpatialDerivative.zeroExtend
#print axioms Carleman.IsWeakSpatialDerivative.zeroExtend
#check @Carleman.SpatialTest.reflectedWithin
#print axioms Carleman.SpatialTest.reflectedWithin
#check @Carleman.SpatialTest.fderiv_convolution_integral
#print axioms Carleman.SpatialTest.fderiv_convolution_integral
#check @Carleman.IsWeakSpatialDerivative.convolution_exchange_local
#print axioms Carleman.IsWeakSpatialDerivative.convolution_exchange_local
#check @Carleman.IsWeakSpatialDerivative.fderiv_convolution_local
#print axioms Carleman.IsWeakSpatialDerivative.fderiv_convolution_local
#check @Carleman.finite_cones_common_height
#print axioms Carleman.finite_cones_common_height
#check @Carleman.finite_cones_coordinate_interpolation
#print axioms Carleman.finite_cones_coordinate_interpolation
#check @Carleman.WeakSobolevJet.boundedLipschitz_scaled_components
#print axioms Carleman.WeakSobolevJet.boundedLipschitz_scaled_components
#check @Carleman.WeakSobolevJet.boundedLipschitz_parameter_interpolation
#print axioms Carleman.WeakSobolevJet.boundedLipschitz_parameter_interpolation
#check @Carleman.boundedLipschitz_jet_neighbor
#print axioms Carleman.boundedLipschitz_jet_neighbor
#check @Carleman.coordinateCombination
#print axioms Carleman.coordinateCombination
#check @Carleman.coordinateSize
#print axioms Carleman.coordinateSize
#check @Carleman.coordinateSize_nonneg
#print axioms Carleman.coordinateSize_nonneg
#check @Carleman.coordinateCombination_add
#print axioms Carleman.coordinateCombination_add
#check @Carleman.coordinateCombination_basis
#print axioms Carleman.coordinateCombination_basis
#check @Carleman.coordinateCombination_norm_le
#print axioms Carleman.coordinateCombination_norm_le
#check @Carleman.weak_coordinateCombination
#print axioms Carleman.weak_coordinateCombination
#check @Carleman.weak_coordinateCombination_second
#print axioms Carleman.weak_coordinateCombination_second
#check @Carleman.bochnerL2Norm_restrict_le
#print axioms Carleman.bochnerL2Norm_restrict_le
#check @Carleman.l2_average_square_le
#print axioms Carleman.l2_average_square_le
#check @Carleman.integrable_square_of_slice_bound
#print axioms Carleman.integrable_square_of_slice_bound
#check @Carleman.l2_average_le_of_slice_bound
#print axioms Carleman.l2_average_le_of_slice_bound
#check @Carleman.bochnerL2Norm_finite_cover
#print axioms Carleman.bochnerL2Norm_finite_cover
#check @Carleman.boundedLipschitz_domain_parameter_interpolation
#print axioms Carleman.boundedLipschitz_domain_parameter_interpolation
#check @Carleman.local_mollifier_norm_bound
#print axioms Carleman.local_mollifier_norm_bound
#check @Carleman.mollified_cone_ftc
#print axioms Carleman.mollified_cone_ftc
#check @Carleman.mollified_cone_interpolation
#print axioms Carleman.mollified_cone_interpolation
#check @Carleman.mollified_cone_translation_l2
#print axioms Carleman.mollified_cone_translation_l2
#check @Carleman.weak_cone_interpolation_fullLp
#print axioms Carleman.weak_cone_interpolation_fullLp
#check @Carleman.weak_cone_interpolation
#print axioms Carleman.weak_cone_interpolation
#check @Carleman.SpatialTest.derivativeLp_zero
#print axioms Carleman.SpatialTest.derivativeLp_zero
#check @Carleman.SpatialTest.derivativeLp_add
#print axioms Carleman.SpatialTest.derivativeLp_add
#check @Carleman.SpatialTest.derivativeLp_smul
#print axioms Carleman.SpatialTest.derivativeLp_smul
#check @Carleman.IsWeakSpatialDerivative.direction_zero
#print axioms Carleman.IsWeakSpatialDerivative.direction_zero
#check @Carleman.IsWeakSpatialDerivative.direction_add
#print axioms Carleman.IsWeakSpatialDerivative.direction_add
#check @Carleman.IsWeakSpatialDerivative.direction_smul
#print axioms Carleman.IsWeakSpatialDerivative.direction_smul
#check @Carleman.IsWeakSpatialDerivative.direction_sum
#print axioms Carleman.IsWeakSpatialDerivative.direction_sum
#check @Carleman.IsWeakSpatialDerivative.sum_states
#print axioms Carleman.IsWeakSpatialDerivative.sum_states
#check @Carleman.zeroExtendLp
#print axioms Carleman.zeroExtendLp
#check @Carleman.zeroExtendLp_ae
#print axioms Carleman.zeroExtendLp_ae
#check @Carleman.zeroExtendLp_ae_restrict
#print axioms Carleman.zeroExtendLp_ae_restrict
#check @Carleman.zeroExtendLp_norm
#print axioms Carleman.zeroExtendLp_norm
#check @Carleman.integral_mul_zeroExtendLp
#print axioms Carleman.integral_mul_zeroExtendLp
#check @Carleman.CoerciveForm.lipschitz_weighted_euler_sobolev_uniform
#print axioms Carleman.CoerciveForm.lipschitz_weighted_euler_sobolev_uniform
#check @Carleman.CoerciveForm.lipschitz_weighted_frozen_sobolev_uniform
#print axioms Carleman.CoerciveForm.lipschitz_weighted_frozen_sobolev_uniform
#check @Carleman.CoerciveForm.lipschitz_weighted_temporal_error_uniform
#print axioms Carleman.CoerciveForm.lipschitz_weighted_temporal_error_uniform
#check @Carleman.WeakSobolevJet.componentMaximum
#print axioms Carleman.WeakSobolevJet.componentMaximum
#check @Carleman.WeakSobolevJet.component_le_maximum
#print axioms Carleman.WeakSobolevJet.component_le_maximum
#check @Carleman.WeakSobolevJet.componentMaximum_le_field
#print axioms Carleman.WeakSobolevJet.componentMaximum_le_field
#check @Carleman.WeakSobolevJet.componentMaximum_zero
#print axioms Carleman.WeakSobolevJet.componentMaximum_zero
#check @Carleman.boundedLipschitz_operator_parameter_graph
#print axioms Carleman.boundedLipschitz_operator_parameter_graph

#check @Carleman.CoerciveForm.interpolated_weighted_frozen_sobolev_uniform
#print axioms Carleman.CoerciveForm.interpolated_weighted_frozen_sobolev_uniform


-- T019: full Section 3 and original-input bridges.
#check @Carleman.Section3.AllowedFamily
#print axioms Carleman.Section3.AllowedFamily
#check @Carleman.Section3.AllowedFamily.inverse
#print axioms Carleman.Section3.AllowedFamily.inverse
#check @Carleman.Section3.Conclusions
#print axioms Carleman.Section3.Conclusions
#check @Carleman.Section3.complete_uniform
#print axioms Carleman.Section3.complete_uniform
#check @Carleman.OriginalForm.section3
#print axioms Carleman.OriginalForm.section3
#check @Carleman.periodCarrier
#print axioms Carleman.periodCarrier
#check @Carleman.periodCarrier_period
#print axioms Carleman.periodCarrier_period
#check @Carleman.periodCarrier_measure
#print axioms Carleman.periodCarrier_measure
#check @Carleman.intervalWeightRegularity
#print axioms Carleman.intervalWeightRegularity
#check @Carleman.Section3.mesh_dt_le_one
#print axioms Carleman.Section3.mesh_dt_le_one
#check @Carleman.Section3.Conclusions.primitive_on_interval
#print axioms Carleman.Section3.Conclusions.primitive_on_interval
#check @Carleman.boundedRealForm
#print axioms Carleman.boundedRealForm
#check @Carleman.conformingValue
#print axioms Carleman.conformingValue
#check @Carleman.OriginalForm.ofBilinear
#print axioms Carleman.OriginalForm.ofBilinear
#check @Carleman.OriginalForm.ofBilinear_scalarForm
#print axioms Carleman.OriginalForm.ofBilinear_scalarForm
#check @Carleman.OriginalForm
#print axioms Carleman.OriginalForm
#check @Carleman.OriginalForm.Energy
#print axioms Carleman.OriginalForm.Energy
#check @Carleman.OriginalForm.model
#print axioms Carleman.OriginalForm.model
#check @Carleman.OriginalForm.valueEquiv
#print axioms Carleman.OriginalForm.valueEquiv
#check @Carleman.OriginalForm.valueEquiv_coe
#print axioms Carleman.OriginalForm.valueEquiv_coe
#check @Carleman.OriginalForm.scalarForm
#print axioms Carleman.OriginalForm.scalarForm
#check @Carleman.OriginalForm.scalarForm_value
#print axioms Carleman.OriginalForm.scalarForm_value
#check @Carleman.OriginalForm.domain_le
#print axioms Carleman.OriginalForm.domain_le
#check @Carleman.OriginalForm.operator_test
#print axioms Carleman.OriginalForm.operator_test
#check @Carleman.OriginalForm.associated_iff
#print axioms Carleman.OriginalForm.associated_iff
#check @Carleman.OriginalForm.identify_operator
#print axioms Carleman.OriginalForm.identify_operator
#check @Carleman.OriginalForm.section3_original_operator
#print axioms Carleman.OriginalForm.section3_original_operator
#check @Carleman.TimeWeight.ofInterval
#print axioms Carleman.TimeWeight.ofInterval
#check @Carleman.TimeWeight.ofInterval_on
#print axioms Carleman.TimeWeight.ofInterval_on
#check @Carleman.TimeWeight.ofInterval_regularity
#print axioms Carleman.TimeWeight.ofInterval_regularity
#check @Carleman.exists_profile_of_smooth
#print axioms Carleman.exists_profile_of_smooth
#check @Carleman.Section3.ProfileEstimates
#print axioms Carleman.Section3.ProfileEstimates
#check @Carleman.Section3.ProfileEstimates.mono
#print axioms Carleman.Section3.ProfileEstimates.mono
#check @Carleman.Section3.profile_uniform
#print axioms Carleman.Section3.profile_uniform
#check @Carleman.SpatialProfile.signed
#print axioms Carleman.SpatialProfile.signed
#check @Carleman.SpatialProfile.signed_neg
#print axioms Carleman.SpatialProfile.signed_neg
#check @Carleman.Section3.signed_uniform
#print axioms Carleman.Section3.signed_uniform
#check @Carleman.Section3.euler_solved_uniform
#print axioms Carleman.Section3.euler_solved_uniform
#check @Carleman.Section3.shift_solved_uniform
#print axioms Carleman.Section3.shift_solved_uniform
#check @Carleman.Section3.frozen_solved_uniform
#print axioms Carleman.Section3.frozen_solved_uniform
#check @Carleman.Section3.temporal_arbitrary_uniform
#print axioms Carleman.Section3.temporal_arbitrary_uniform
#check @Carleman.Section3.EulerEstimate
#print axioms Carleman.Section3.EulerEstimate
#check @Carleman.Section3.ContinuousEstimate
#print axioms Carleman.Section3.ContinuousEstimate
#check @Carleman.Section3.TemporalEstimate
#print axioms Carleman.Section3.TemporalEstimate
#check @Carleman.Section3.EulerEstimate.mono
#print axioms Carleman.Section3.EulerEstimate.mono
#check @Carleman.Section3.ContinuousEstimate.mono
#print axioms Carleman.Section3.ContinuousEstimate.mono
#check @Carleman.Section3.TemporalEstimate.mono
#print axioms Carleman.Section3.TemporalEstimate.mono
#check @Carleman.PeriodicWeakTrajectory.graph_equation_iff
#print axioms Carleman.PeriodicWeakTrajectory.graph_equation_iff
#check @Carleman.CoerciveForm.interpolated_weighted_shift_graph_uniform
#print axioms Carleman.CoerciveForm.interpolated_weighted_shift_graph_uniform
#check @Carleman.CoerciveForm.interpolated_weighted_shift_sobolev_uniform
#print axioms Carleman.CoerciveForm.interpolated_weighted_shift_sobolev_uniform
#check @Carleman.CoerciveForm.lipschitz_weighted_shift_sobolev_uniform
#print axioms Carleman.CoerciveForm.lipschitz_weighted_shift_sobolev_uniform
#check @Carleman.continuous_shift_margin_uniform
#print axioms Carleman.continuous_shift_margin_uniform
#check @Carleman.SpatialProfile.logDerivative_shift_small_uniform
#print axioms Carleman.SpatialProfile.logDerivative_shift_small_uniform
#check @Carleman.CoerciveForm.weighted_shift_graph_remainder_uniform
#print axioms Carleman.CoerciveForm.weighted_shift_graph_remainder_uniform
#check @Carleman.Section3.Conclusions.threshold
#print axioms Carleman.Section3.Conclusions.threshold
#check @Carleman.Section3.Conclusions.primitive
#print axioms Carleman.Section3.Conclusions.primitive
#check @Carleman.Section3.Conclusions.form_bound
#print axioms Carleman.Section3.Conclusions.form_bound
#check @Carleman.Section3.Conclusions.form_coercive
#print axioms Carleman.Section3.Conclusions.form_coercive
#check @Carleman.Section3.Conclusions.euler
#print axioms Carleman.Section3.Conclusions.euler
#check @Carleman.Section3.Conclusions.frozen
#print axioms Carleman.Section3.Conclusions.frozen
#check @Carleman.Section3.Conclusions.temporal
#print axioms Carleman.Section3.Conclusions.temporal

#check @Carleman.sum_variable_bilinear_increment
#print axioms Carleman.sum_variable_bilinear_increment
#check @Carleman.TimeGrid.pairing_variable_operator
#print axioms Carleman.TimeGrid.pairing_variable_operator
#check @Carleman.TimeGrid.pairing_variable_operator_lower
#print axioms Carleman.TimeGrid.pairing_variable_operator_lower
#check @Carleman.Orientation.difference_map
#print axioms Carleman.Orientation.difference_map
#check @Carleman.Orientation.difference_sub
#print axioms Carleman.Orientation.difference_sub
#check @Carleman.Reconstruction.spatialForm
#print axioms Carleman.Reconstruction.spatialForm
#check @Carleman.Reconstruction.spatialForm_sub_left
#print axioms Carleman.Reconstruction.spatialForm_sub_left
#check @Carleman.Reconstruction.spatialForm_sub_right
#print axioms Carleman.Reconstruction.spatialForm_sub_right
#check @Carleman.Reconstruction.spatial_continuous_test
#print axioms Carleman.Reconstruction.spatial_continuous_test
#check @Carleman.Reconstruction.spatial_discrete_test
#print axioms Carleman.Reconstruction.spatial_discrete_test
#check @Carleman.Reconstruction.spatial_error_equation
#print axioms Carleman.Reconstruction.spatial_error_equation
#check @Carleman.Reconstruction.spatial_consistency_identity
#print axioms Carleman.Reconstruction.spatial_consistency_identity
#check @Carleman.Orientation.pairing_difference_opposite
#print axioms Carleman.Orientation.pairing_difference_opposite
#check @Carleman.Reconstruction.spatial_complete_identity
#print axioms Carleman.Reconstruction.spatial_complete_identity
#check @Carleman.Reconstruction.spatial_weighted_duality
#print axioms Carleman.Reconstruction.spatial_weighted_duality
#check @Carleman.Reconstruction.auxiliaryEuler
#print axioms Carleman.Reconstruction.auxiliaryEuler
#check @Carleman.Reconstruction.auxiliaryEuler_injective
#print axioms Carleman.Reconstruction.auxiliaryEuler_injective
#check @Carleman.Reconstruction.existsUnique_auxiliaryEuler
#print axioms Carleman.Reconstruction.existsUnique_auxiliaryEuler

#check @Carleman.TimeGrid.testOperator_cell_increment
#print axioms Carleman.TimeGrid.testOperator_cell_increment
#check @Carleman.TimeGrid.pairing_testOperator_dPlus_lower
#print axioms Carleman.TimeGrid.pairing_testOperator_dPlus_lower
#check @Carleman.TimeGrid.pairing_testOperator_dMinus_lower
#print axioms Carleman.TimeGrid.pairing_testOperator_dMinus_lower

#check @Carleman.WeakSobolevJet.weightedFieldMap
#print axioms Carleman.WeakSobolevJet.weightedFieldMap
#check @Carleman.WeakSobolevJet.weightedFieldMap_norm_sq
#print axioms Carleman.WeakSobolevJet.weightedFieldMap_norm_sq
#check @Carleman.WeakSobolevJet.weightedSeminorm
#print axioms Carleman.WeakSobolevJet.weightedSeminorm
#check @Carleman.WeakSobolevJet.weightedSeminorm_apply
#print axioms Carleman.WeakSobolevJet.weightedSeminorm_apply
#check @Carleman.WeakSobolevJet.weightedNorm_add_le
#print axioms Carleman.WeakSobolevJet.weightedNorm_add_le
#check @Carleman.WeakSobolevJet.weightedNorm_sub_le
#print axioms Carleman.WeakSobolevJet.weightedNorm_sub_le
#check @Carleman.conformingWeightedSeminorm
#print axioms Carleman.conformingWeightedSeminorm
#check @Carleman.conformingWeightedSeminorm_apply
#print axioms Carleman.conformingWeightedSeminorm_apply

#check @Carleman.TimeGrid.weightedNorm_nonneg
#print axioms Carleman.TimeGrid.weightedNorm_nonneg
#check @Carleman.TimeGrid.weightedNorm_product_sum
#print axioms Carleman.TimeGrid.weightedNorm_product_sum
#check @Carleman.TimeGrid.weightedNorm_add_le
#print axioms Carleman.TimeGrid.weightedNorm_add_le
#check @Carleman.TimeGrid.weightedNorm_sub_le
#print axioms Carleman.TimeGrid.weightedNorm_sub_le
#check @Carleman.TimeGrid.weightedNorm_le_of_bound
#print axioms Carleman.TimeGrid.weightedNorm_le_of_bound
#check @Carleman.TimeGrid.weighted_bilinear_sum_bound
#print axioms Carleman.TimeGrid.weighted_bilinear_sum_bound

-- Section 4 actual weighted test, Cea and nodal approximation bounds.
#check @Carleman.SpatialProfile.test_mass_cell_le
#print axioms Carleman.SpatialProfile.test_mass_cell_le
#check @Carleman.SpatialProfile.test_derivative_cell_bound
#print axioms Carleman.SpatialProfile.test_derivative_cell_bound
#check @Carleman.SpatialProfile.pairing_test_dPlus_lower
#print axioms Carleman.SpatialProfile.pairing_test_dPlus_lower
#check @Carleman.SpatialProfile.pairing_test_dMinus_lower
#print axioms Carleman.SpatialProfile.pairing_test_dMinus_lower
#check @Carleman.Reconstruction.spatial_test_stability
#print axioms Carleman.Reconstruction.spatial_test_stability
#check @Carleman.Reconstruction.spatial_test_node
#print axioms Carleman.Reconstruction.spatial_test_node
#check @Carleman.Reconstruction.spatial_test_energy_bound
#print axioms Carleman.Reconstruction.spatial_test_energy_bound
#check @Carleman.squared_weight_test_uniform
#print axioms Carleman.squared_weight_test_uniform
#check @Carleman.OriginalForm.bilinearForm
#print axioms Carleman.OriginalForm.bilinearForm
#check @Carleman.OriginalForm.bilinearForm_apply
#print axioms Carleman.OriginalForm.bilinearForm_apply
#check @Carleman.Section4.energySeminorm
#print axioms Carleman.Section4.energySeminorm
#check @Carleman.Section4.spatial_cea
#print axioms Carleman.Section4.spatial_cea
#check @Carleman.TimeGrid.weightedNorm_sum_le
#print axioms Carleman.TimeGrid.weightedNorm_sum_le
#check @Carleman.TimeGrid.weightedNorm_le_field_sum
#print axioms Carleman.TimeGrid.weightedNorm_le_field_sum
#check @Carleman.WeakSobolevJet.weightedNorm_truncate_le_parameterNorm
#print axioms Carleman.WeakSobolevJet.weightedNorm_truncate_le_parameterNorm
#check @Carleman.WeakSobolevJet.nodal_approximation_bound
#print axioms Carleman.WeakSobolevJet.nodal_approximation_bound
#check @Carleman.Section4.conforming_energy_le_parameterNorm
#print axioms Carleman.Section4.conforming_energy_le_parameterNorm

-- Full Section 4 spatial energy and Aubin–Nitsche rates.
#check @Carleman.Section4.energyNorm
#print axioms Carleman.Section4.energyNorm
#check @Carleman.Section4.regularityNorm
#print axioms Carleman.Section4.regularityNorm
#check @Carleman.Section4.WeightedApproximation
#print axioms Carleman.Section4.WeightedApproximation
#check @Carleman.Section4.WeightedApproximation.energy
#print axioms Carleman.Section4.WeightedApproximation.energy
#check @Carleman.Section4.WeightedApproximation.l2
#print axioms Carleman.Section4.WeightedApproximation.l2
#check @Carleman.Section4.nodal_energy_le_regularity
#print axioms Carleman.Section4.nodal_energy_le_regularity
#check @Carleman.Section4.WeightedApproximation.nodal_energy
#print axioms Carleman.Section4.WeightedApproximation.nodal_energy
#check @Carleman.Section4.WeightedApproximation.nodal_Q
#print axioms Carleman.Section4.WeightedApproximation.nodal_Q
#check @Carleman.Section4.WeightedApproximation.nodal_l2
#print axioms Carleman.Section4.WeightedApproximation.nodal_l2
#check @Carleman.Section4.regularityNorm_nonneg
#print axioms Carleman.Section4.regularityNorm_nonneg
#check @Carleman.Section4.energy_rates_of_cea
#print axioms Carleman.Section4.energy_rates_of_cea
#check @Carleman.Section4.WeightedTest
#print axioms Carleman.Section4.WeightedTest
#check @Carleman.Section4.WeightedTest.op
#print axioms Carleman.Section4.WeightedTest.op
#check @Carleman.Section4.WeightedTest.derivative
#print axioms Carleman.Section4.WeightedTest.derivative
#check @Carleman.Section4.WeightedTest.endpoint
#print axioms Carleman.Section4.WeightedTest.endpoint
#check @Carleman.Section4.WeightedTest.hasDeriv
#print axioms Carleman.Section4.WeightedTest.hasDeriv
#check @Carleman.Section4.WeightedTest.symmetric
#print axioms Carleman.Section4.WeightedTest.symmetric
#check @Carleman.Section4.WeightedTest.nonneg
#print axioms Carleman.Section4.WeightedTest.nonneg
#check @Carleman.Section4.WeightedTest.time_bound
#print axioms Carleman.Section4.WeightedTest.time_bound
#check @Carleman.Section4.WeightedTest.superapprox
#print axioms Carleman.Section4.WeightedTest.superapprox
#check @Carleman.Section4.spatial_smallness_thresholds
#print axioms Carleman.Section4.spatial_smallness_thresholds
#check @Carleman.Section4.EnergyEstimate
#print axioms Carleman.Section4.EnergyEstimate
#check @Carleman.Section4.energy_estimate_of_cea
#print axioms Carleman.Section4.energy_estimate_of_cea
#check @Carleman.Section4.squared_weight_signed_uniform
#print axioms Carleman.Section4.squared_weight_signed_uniform
#check @Carleman.Section4.spatial_time_threshold
#print axioms Carleman.Section4.spatial_time_threshold
#check @Carleman.Section4.EnergyUniform
#print axioms Carleman.Section4.EnergyUniform
#check @Carleman.Section4.energy_uniform_of_section3
#print axioms Carleman.Section4.energy_uniform_of_section3
#check @Carleman.OriginalForm.spatial_energy_uniform
#print axioms Carleman.OriginalForm.spatial_energy_uniform
#check @Carleman.Section4.weighted_pairing_bound
#print axioms Carleman.Section4.weighted_pairing_bound
#check @Carleman.Section4.spatial_duality_bound
#print axioms Carleman.Section4.spatial_duality_bound
#check @Carleman.Section4.L2Estimate
#print axioms Carleman.Section4.L2Estimate
#check @Carleman.Section4.duality_rate_coefficient
#print axioms Carleman.Section4.duality_rate_coefficient
#check @Carleman.Section4.l2_estimate_of_energy
#print axioms Carleman.Section4.l2_estimate_of_energy
#check @Carleman.Section4.SpatialUniform
#print axioms Carleman.Section4.SpatialUniform
#check @Carleman.Section4.spatial_uniform_of_section3
#print axioms Carleman.Section4.spatial_uniform_of_section3
#check @Carleman.OriginalForm.spatial_uniform
#print axioms Carleman.OriginalForm.spatial_uniform

-- Full original Theorem 4.2 with actual weak space-time error.
#check @Carleman.WeakSobolevJet.parameterTimeField_add
#print axioms Carleman.WeakSobolevJet.parameterTimeField_add
#check @Carleman.WeakSobolevJet.spacetimeWeightedNorm_add_le
#print axioms Carleman.WeakSobolevJet.spacetimeWeightedNorm_add_le
#check @Carleman.WeakSobolevJet.spacetimeWeightedNorm_congr_ae
#print axioms Carleman.WeakSobolevJet.spacetimeWeightedNorm_congr_ae
#check @Carleman.WeakSobolevJet.spacetimeWeightedNorm_extension_le
#print axioms Carleman.WeakSobolevJet.spacetimeWeightedNorm_extension_le
#check @Carleman.Section4.reconstructedError
#print axioms Carleman.Section4.reconstructedError
#check @Carleman.Section4.reconstructedError_value_ae
#print axioms Carleman.Section4.reconstructedError_value_ae
#check @Carleman.Section4.reconstructedError_decomposition
#print axioms Carleman.Section4.reconstructedError_decomposition
#check @Carleman.Section4.CombinedEstimate
#print axioms Carleman.Section4.CombinedEstimate
#check @Carleman.Section4.combine_nonnegative_rates
#print axioms Carleman.Section4.combine_nonnegative_rates
#check @Carleman.Section4.combined_estimate_of_spatial_temporal
#print axioms Carleman.Section4.combined_estimate_of_spatial_temporal
#check @Carleman.Section4.CombinedUniform
#print axioms Carleman.Section4.CombinedUniform
#check @Carleman.Section4.combined_uniform_of_section3
#print axioms Carleman.Section4.combined_uniform_of_section3
#check @Carleman.OriginalForm.combined_uniform
#print axioms Carleman.OriginalForm.combined_uniform

-- Original Theorem 2.1: all actual bridges constructed internally.
#check @Carleman.SpatialProfile.timeSq_eq_bochnerL2Norm_sq
#print axioms Carleman.SpatialProfile.timeSq_eq_bochnerL2Norm_sq
#check @Carleman.SpatialProfile.nodeMap_l2Norm_sq_powerSq
#print axioms Carleman.SpatialProfile.nodeMap_l2Norm_sq_powerSq
#check @Carleman.WeakSobolevJet.spacetimeWeightedNorm_sq_powerSum
#print axioms Carleman.WeakSobolevJet.spacetimeWeightedNorm_sq_powerSum
#check @Carleman.sobolevGeometry_graphSq_eq
#print axioms Carleman.sobolevGeometry_graphSq_eq
#check @Carleman.sobolevGeometry_errorBridge_of_combined
#print axioms Carleman.sobolevGeometry_errorBridge_of_combined
#check @Carleman.sobolevGeometry_transferBridges
#print axioms Carleman.sobolevGeometry_transferBridges
#check @Carleman.Section5.NumericalData
#print axioms Carleman.Section5.NumericalData
#check @Carleman.Section5.NumericalData.stiffness
#print axioms Carleman.Section5.NumericalData.stiffness
#check @Carleman.Section5.NumericalData.approximation
#print axioms Carleman.Section5.NumericalData.approximation
#check @Carleman.Section5.NumericalData.test
#print axioms Carleman.Section5.NumericalData.test
#check @Carleman.Section5.NumericalData.defect
#print axioms Carleman.Section5.NumericalData.defect
#check @Carleman.Section5.NumericalData.reconstruction_upper
#print axioms Carleman.Section5.NumericalData.reconstruction_upper
#check @Carleman.Section5.NumericalData.reconstruction_lower
#print axioms Carleman.Section5.NumericalData.reconstruction_lower
#check @Carleman.Section5.NumericalData.lift_bound
#print axioms Carleman.Section5.NumericalData.lift_bound
#check @Carleman.Section5.NumericalData.observation_bound
#print axioms Carleman.Section5.NumericalData.observation_bound
#check @Carleman.Section5.TransferUniform
#print axioms Carleman.Section5.TransferUniform
#check @Carleman.Section5.transfer_uniform_of_combined
#print axioms Carleman.Section5.transfer_uniform_of_combined
#check @Carleman.OriginalForm.transfer_uniform
#print axioms Carleman.OriginalForm.transfer_uniform

#check @Carleman.CarlemanExponents.nuEnergy
#print axioms Carleman.CarlemanExponents.nuEnergy
#check @Carleman.CarlemanExponents.nuL2
#print axioms Carleman.CarlemanExponents.nuL2
#check @Carleman.CarlemanExponents.omittedRatio
#print axioms Carleman.CarlemanExponents.omittedRatio
#check @Carleman.CarlemanExponents.alphaX
#print axioms Carleman.CarlemanExponents.alphaX
#check @Carleman.CarlemanExponents.alphaT
#print axioms Carleman.CarlemanExponents.alphaT
#check @Carleman.CarlemanExponents.nuEnergy_nonneg
#print axioms Carleman.CarlemanExponents.nuEnergy_nonneg
#check @Carleman.CarlemanExponents.nuL2_pos
#print axioms Carleman.CarlemanExponents.nuL2_pos
#check @Carleman.CarlemanExponents.omittedRatio_pos
#print axioms Carleman.CarlemanExponents.omittedRatio_pos
#check @Carleman.CarlemanExponents.mul_le_of_le_omittedRatio
#print axioms Carleman.CarlemanExponents.mul_le_of_le_omittedRatio
#check @Carleman.CarlemanExponents.scale_bounds
#print axioms Carleman.CarlemanExponents.scale_bounds
#check @Carleman.CarlemanExponents.heat
#print axioms Carleman.CarlemanExponents.heat
#check @Carleman.CarlemanExponents.heat_scale_exponents
#print axioms Carleman.CarlemanExponents.heat_scale_exponents
#check @Carleman.exists_small_rpow
#print axioms Carleman.exists_small_rpow
#check @Carleman.scale_monomial_le
#print axioms Carleman.scale_monomial_le
#check @Carleman.ErrorScales.approximationConstant
#print axioms Carleman.ErrorScales.approximationConstant
#check @Carleman.ErrorScales.approximationConstant_pos
#print axioms Carleman.ErrorScales.approximationConstant_pos
#check @Carleman.ErrorScales.approximation_rates
#print axioms Carleman.ErrorScales.approximation_rates
#check @Carleman.ErrorScales.defects_le_budget
#print axioms Carleman.ErrorScales.defects_le_budget
#check @Carleman.exists_scale_smallness
#print axioms Carleman.exists_scale_smallness
#check @Carleman.Section5.ScaleUniform
#print axioms Carleman.Section5.ScaleUniform
#check @Carleman.Section5.scale_uniform_of_transfer
#print axioms Carleman.Section5.scale_uniform_of_transfer
#check @Carleman.OriginalForm.scale_uniform
#print axioms Carleman.OriginalForm.scale_uniform
#check @Carleman.OriginalForm.heat_scale_uniform
#print axioms Carleman.OriginalForm.heat_scale_uniform

#check @Carleman.Physical.step
#print axioms Carleman.Physical.step
#check @Carleman.Physical.step_apply
#print axioms Carleman.Physical.step_apply
#check @Carleman.Physical.one_sub_mul_exp_ge_one
#print axioms Carleman.Physical.one_sub_mul_exp_ge_one
#check @Carleman.Physical.step_norm_lower
#print axioms Carleman.Physical.step_norm_lower
#check @Carleman.Physical.step_inverse_bound
#print axioms Carleman.Physical.step_inverse_bound
#check @Carleman.Physical.step_bijective
#print axioms Carleman.Physical.step_bijective
#check @Carleman.Physical.stiffness_potential_lower
#print axioms Carleman.Physical.stiffness_potential_lower
#check @Carleman.Physical.Forward
#print axioms Carleman.Physical.Forward
#check @Carleman.Physical.Adjoint
#print axioms Carleman.Physical.Adjoint
#check @Carleman.Physical.existsUnique_forward
#print axioms Carleman.Physical.existsUnique_forward
#check @Carleman.Physical.existsUnique_adjoint
#print axioms Carleman.Physical.existsUnique_adjoint
#check @Carleman.Physical.duality_increment
#print axioms Carleman.Physical.duality_increment
#check @Carleman.Physical.physical_duality
#print axioms Carleman.Physical.physical_duality
#check @Carleman.Physical.control_duality
#print axioms Carleman.Physical.control_duality
#check @Carleman.Physical.adjoint_energy
#print axioms Carleman.Physical.adjoint_energy
#check @Carleman.Physical.partialSum
#print axioms Carleman.Physical.partialSum
#check @Carleman.Physical.partialSum_zero
#print axioms Carleman.Physical.partialSum_zero
#check @Carleman.Physical.partialSum_succ
#print axioms Carleman.Physical.partialSum_succ
#check @Carleman.Physical.partialSum_le_sum
#print axioms Carleman.Physical.partialSum_le_sum
#check @Carleman.Physical.forward_recurrence_bound
#print axioms Carleman.Physical.forward_recurrence_bound
#check @Carleman.Physical.controlNorm
#print axioms Carleman.Physical.controlNorm
#check @Carleman.Physical.time_l1_le_l2
#print axioms Carleman.Physical.time_l1_le_l2
#check @Carleman.Physical.energyConstant
#print axioms Carleman.Physical.energyConstant
#check @Carleman.Physical.energyConstant_pos
#print axioms Carleman.Physical.energyConstant_pos
#check @Carleman.Physical.forward_energy
#print axioms Carleman.Physical.forward_energy
#check @Carleman.Physical.step_equation_iff
#print axioms Carleman.Physical.step_equation_iff
#check @Carleman.Physical.ForwardEquation
#print axioms Carleman.Physical.ForwardEquation
#check @Carleman.Physical.AdjointEquation
#print axioms Carleman.Physical.AdjointEquation
#check @Carleman.Physical.forward_equation_iff
#print axioms Carleman.Physical.forward_equation_iff
#check @Carleman.Physical.adjoint_equation_iff
#print axioms Carleman.Physical.adjoint_equation_iff
#check @Carleman.Physical.physical_duality_lemma
#print axioms Carleman.Physical.physical_duality_lemma

#check @Carleman.Physical.rayleigh
#print axioms Carleman.Physical.rayleigh
#check @Carleman.Physical.rayleigh_nonneg
#print axioms Carleman.Physical.rayleigh_nonneg
#check @Carleman.Physical.rayleigh_step_normalized
#print axioms Carleman.Physical.rayleigh_step_normalized
#check @Carleman.Physical.rayleigh_smul
#print axioms Carleman.Physical.rayleigh_smul
#check @Carleman.Physical.rayleigh_step
#print axioms Carleman.Physical.rayleigh_step
#check @Carleman.Physical.positive_form_cauchy
#print axioms Carleman.Physical.positive_form_cauchy
#check @Carleman.Physical.positive_resolvent_lower
#print axioms Carleman.Physical.positive_resolvent_lower
#check @Carleman.Physical.perturbed_resolvent_lower
#print axioms Carleman.Physical.perturbed_resolvent_lower
#check @Carleman.Physical.adjoint_nonzero
#print axioms Carleman.Physical.adjoint_nonzero
#check @Carleman.Physical.exponential_recurrence
#print axioms Carleman.Physical.exponential_recurrence
#check @Carleman.Physical.adjoint_rayleigh_bound
#print axioms Carleman.Physical.adjoint_rayleigh_bound
#check @Carleman.Physical.adjoint_reverse_rayleigh
#print axioms Carleman.Physical.adjoint_reverse_rayleigh
#check @Carleman.Physical.filterRayleigh
#print axioms Carleman.Physical.filterRayleigh
#check @Carleman.Physical.rayleigh_le_opNorm
#print axioms Carleman.Physical.rayleigh_le_opNorm
#check @Carleman.Physical.filterRayleigh_bot
#print axioms Carleman.Physical.filterRayleigh_bot
#check @Carleman.Physical.rayleigh_le_filterRayleigh
#print axioms Carleman.Physical.rayleigh_le_filterRayleigh
#check @Carleman.Physical.filterConstant
#print axioms Carleman.Physical.filterConstant
#check @Carleman.Physical.filterConstant_pos
#print axioms Carleman.Physical.filterConstant_pos
#check @Carleman.Physical.filter_reverse
#print axioms Carleman.Physical.filter_reverse

#check @Carleman.Physical.physicalStepEquiv
#print axioms Carleman.Physical.physicalStepEquiv
#check @Carleman.Physical.adjointNode
#print axioms Carleman.Physical.adjointNode
#check @Carleman.Physical.adjointNode_last
#print axioms Carleman.Physical.adjointNode_last
#check @Carleman.Physical.adjointNode_step
#print axioms Carleman.Physical.adjointNode_step
#check @Carleman.Physical.adjointNode_injective
#print axioms Carleman.Physical.adjointNode_injective
#check @Carleman.Physical.initialMap
#print axioms Carleman.Physical.initialMap
#check @Carleman.Physical.initialMap_injective
#print axioms Carleman.Physical.initialMap_injective
#check @Carleman.Physical.initialMap_bound
#print axioms Carleman.Physical.initialMap_bound
#check @Carleman.Physical.observationLinear
#print axioms Carleman.Physical.observationLinear
#check @Carleman.Physical.observationMap
#print axioms Carleman.Physical.observationMap
#check @Carleman.Physical.observationMap_norm_sq
#print axioms Carleman.Physical.observationMap_norm_sq
#check @Carleman.Physical.humOperator
#print axioms Carleman.Physical.humOperator
#check @Carleman.Physical.humOperator_pairing
#print axioms Carleman.Physical.humOperator_pairing
#check @Carleman.Physical.humOperator_bijective
#print axioms Carleman.Physical.humOperator_bijective
#check @Carleman.Physical.hum_optimality
#print axioms Carleman.Physical.hum_optimality
#check @Carleman.Physical.penalized_hum_control
#print axioms Carleman.Physical.penalized_hum_control
#check @Carleman.Physical.controlVector
#print axioms Carleman.Physical.controlVector
#check @Carleman.Physical.controlVector_norm
#print axioms Carleman.Physical.controlVector_norm
#check @Carleman.Physical.controlVector_unscale
#print axioms Carleman.Physical.controlVector_unscale
#check @Carleman.Physical.control_observation_pairing
#print axioms Carleman.Physical.control_observation_pairing
#check @Carleman.Physical.terminal_representation
#print axioms Carleman.Physical.terminal_representation
#check @Carleman.Physical.physical_hum_control
#print axioms Carleman.Physical.physical_hum_control
#check @Carleman.Physical.relaxed_control_of_observation
#print axioms Carleman.Physical.relaxed_control_of_observation

#check @Carleman.Physical.periodic_next_of_endpoints
#print axioms Carleman.Physical.periodic_next_of_endpoints
#check @Carleman.Physical.cutoffState
#print axioms Carleman.Physical.cutoffState
#check @Carleman.Physical.cutoffRemainder
#print axioms Carleman.Physical.cutoffRemainder
#check @Carleman.Physical.cutoff_next
#print axioms Carleman.Physical.cutoff_next
#check @Carleman.Physical.cutoff_difference
#print axioms Carleman.Physical.cutoff_difference
#check @Carleman.Physical.cutoff_residual
#print axioms Carleman.Physical.cutoff_residual
#check @Carleman.Physical.physicalWeightDenom
#print axioms Carleman.Physical.physicalWeightDenom
#check @Carleman.Physical.physicalWeight
#print axioms Carleman.Physical.physicalWeight
#check @Carleman.Physical.physicalWeightDenom_pos
#print axioms Carleman.Physical.physicalWeightDenom_pos
#check @Carleman.Physical.physicalWeightDenom_sq
#print axioms Carleman.Physical.physicalWeightDenom_sq
#check @Carleman.Physical.physicalWeightDenom_bounds
#print axioms Carleman.Physical.physicalWeightDenom_bounds
#check @Carleman.Physical.physicalWeight_bounds
#print axioms Carleman.Physical.physicalWeight_bounds
#check @Carleman.Physical.physicalWeight_zero
#print axioms Carleman.Physical.physicalWeight_zero
#check @Carleman.Physical.physicalWeight_periodic
#print axioms Carleman.Physical.physicalWeight_periodic
#check @Carleman.Physical.physicalWeightDenom_hasDerivAt
#print axioms Carleman.Physical.physicalWeightDenom_hasDerivAt
#check @Carleman.Physical.physicalWeightDerivative
#print axioms Carleman.Physical.physicalWeightDerivative
#check @Carleman.Physical.physicalWeight_hasDerivAt
#print axioms Carleman.Physical.physicalWeight_hasDerivAt
#check @Carleman.Physical.physicalWeight_smooth
#print axioms Carleman.Physical.physicalWeight_smooth
#check @Carleman.Physical.physicalWeight_derivative_bound
#print axioms Carleman.Physical.physicalWeight_derivative_bound
#check @Carleman.Physical.physicalTimeWeight
#print axioms Carleman.Physical.physicalTimeWeight
#check @Carleman.Physical.physicalTimeWeightRegularity
#print axioms Carleman.Physical.physicalTimeWeightRegularity
#check @Carleman.Physical.physicalWeightSecondDerivative
#print axioms Carleman.Physical.physicalWeightSecondDerivative
#check @Carleman.Physical.physicalWeightDerivative_hasDerivAt
#print axioms Carleman.Physical.physicalWeightDerivative_hasDerivAt
#check @Carleman.Physical.physicalWeight_second_derivative_bound
#print axioms Carleman.Physical.physicalWeight_second_derivative_bound
#check @Carleman.Physical.physicalWeight_deriv
#print axioms Carleman.Physical.physicalWeight_deriv
#check @Carleman.Physical.physicalWeight_second_deriv
#print axioms Carleman.Physical.physicalWeight_second_deriv
#check @Carleman.Physical.physicalWeightDerivative_zero
#print axioms Carleman.Physical.physicalWeightDerivative_zero
#check @Carleman.Physical.physicalWeightDerivative_periodic
#print axioms Carleman.Physical.physicalWeightDerivative_periodic
#check @Carleman.Physical.clipUnit
#print axioms Carleman.Physical.clipUnit
#check @Carleman.Physical.clipUnit_bounds
#print axioms Carleman.Physical.clipUnit_bounds
#check @Carleman.Physical.clipUnit_zero
#print axioms Carleman.Physical.clipUnit_zero
#check @Carleman.Physical.clipUnit_one
#print axioms Carleman.Physical.clipUnit_one
#check @Carleman.Physical.clipUnit_lipschitz
#print axioms Carleman.Physical.clipUnit_lipschitz
#check @Carleman.Physical.endpointDistance
#print axioms Carleman.Physical.endpointDistance
#check @Carleman.Physical.endpointDistance_lipschitz
#print axioms Carleman.Physical.endpointDistance_lipschitz
#check @Carleman.Physical.physicalCutoff
#print axioms Carleman.Physical.physicalCutoff
#check @Carleman.Physical.physicalCutoff_bounds
#print axioms Carleman.Physical.physicalCutoff_bounds
#check @Carleman.Physical.physicalCutoff_zero
#print axioms Carleman.Physical.physicalCutoff_zero
#check @Carleman.Physical.physicalCutoff_one
#print axioms Carleman.Physical.physicalCutoff_one
#check @Carleman.Physical.physicalCutoff_endpoints
#print axioms Carleman.Physical.physicalCutoff_endpoints
#check @Carleman.Physical.physicalCutoff_lipschitz
#print axioms Carleman.Physical.physicalCutoff_lipschitz
#check @Carleman.Physical.cutoffNodes
#print axioms Carleman.Physical.cutoffNodes
#check @Carleman.Physical.cutoffNodes_endpoints
#print axioms Carleman.Physical.cutoffNodes_endpoints
#check @Carleman.Physical.cutoffNodes_difference
#print axioms Carleman.Physical.cutoffNodes_difference
#check @Carleman.Physical.cutoffNodes_transition_location
#print axioms Carleman.Physical.cutoffNodes_transition_location
#check @Carleman.Physical.leftNodes
#print axioms Carleman.Physical.leftNodes
#check @Carleman.Physical.rightNodes
#print axioms Carleman.Physical.rightNodes
#check @Carleman.Physical.leftNodes_measure
#print axioms Carleman.Physical.leftNodes_measure
#check @Carleman.Physical.rightNodes_measure
#print axioms Carleman.Physical.rightNodes_measure
#check @Carleman.Physical.middleNodes
#print axioms Carleman.Physical.middleNodes
#check @Carleman.Physical.middleNodes_measure
#print axioms Carleman.Physical.middleNodes_measure
#check @Carleman.Physical.transitionNodes
#print axioms Carleman.Physical.transitionNodes
#check @Carleman.Physical.transitionNodes_measure
#print axioms Carleman.Physical.transitionNodes_measure
#check @Carleman.Physical.sine_reflect
#print axioms Carleman.Physical.sine_reflect
#check @Carleman.Physical.sine_endpoint_bound
#print axioms Carleman.Physical.sine_endpoint_bound
#check @Carleman.Physical.physicalWeight_near_endpoint
#print axioms Carleman.Physical.physicalWeight_near_endpoint
#check @Carleman.Physical.sine_middle_lower
#print axioms Carleman.Physical.sine_middle_lower
#check @Carleman.Physical.physicalWeight_middle_upper
#print axioms Carleman.Physical.physicalWeight_middle_upper
#check @Carleman.Physical.concrete_cutoff_residual
#print axioms Carleman.Physical.concrete_cutoff_residual
#check @Carleman.Physical.cutoffNodes_one_middle
#print axioms Carleman.Physical.cutoffNodes_one_middle
#check @Carleman.Physical.cutoff_remainder_zero
#print axioms Carleman.Physical.cutoff_remainder_zero
#check @Carleman.Physical.cutoff_remainder_norm_bound
#print axioms Carleman.Physical.cutoff_remainder_norm_bound
#check @Carleman.Physical.cutoff_remainder_energy_bound
#print axioms Carleman.Physical.cutoff_remainder_energy_bound
#check @Carleman.Physical.physical_adjoint_terminal_bound
#print axioms Carleman.Physical.physical_adjoint_terminal_bound
#check @Carleman.Physical.physical_cutoff_remainder_energy
#print axioms Carleman.Physical.physical_cutoff_remainder_energy
#check @Carleman.Physical.physical_adjoint_initial_lower
#print axioms Carleman.Physical.physical_adjoint_initial_lower
#check @Carleman.Physical.physical_middle_energy
#print axioms Carleman.Physical.physical_middle_energy
#check @Carleman.Physical.physical_delta_conditions
#print axioms Carleman.Physical.physical_delta_conditions
#check @Carleman.Physical.physical_transition_weight
#print axioms Carleman.Physical.physical_transition_weight
#check @Carleman.Physical.physical_weight_endpoint_decay
#print axioms Carleman.Physical.physical_weight_endpoint_decay

#check @Carleman.Physical.physicalBaseAmplitude
#print axioms Carleman.Physical.physicalBaseAmplitude
#check @Carleman.Physical.physicalBaseAmplitude_bounds
#print axioms Carleman.Physical.physicalBaseAmplitude_bounds
#check @Carleman.Physical.physicalBaseAmplitude_ge_two
#print axioms Carleman.Physical.physicalBaseAmplitude_ge_two
#check @Carleman.Physical.physicalBaseAmplitude_derivative_budgets
#print axioms Carleman.Physical.physicalBaseAmplitude_derivative_budgets
#check @Carleman.Physical.physicalWeightSecondDerivative_periodic
#print axioms Carleman.Physical.physicalWeightSecondDerivative_periodic
#check @Carleman.Physical.PhysicalQClass
#print axioms Carleman.Physical.PhysicalQClass
#check @Carleman.Physical.PhysicalQClass.toRegularity
#print axioms Carleman.Physical.PhysicalQClass.toRegularity
#check @Carleman.Physical.physicalWeight_lower_qc
#print axioms Carleman.Physical.physicalWeight_lower_qc
#check @Carleman.Physical.physicalTimeWeight_qclass
#print axioms Carleman.Physical.physicalTimeWeight_qclass
#check @Carleman.Physical.physical_qclass_uniform
#print axioms Carleman.Physical.physical_qclass_uniform
#check @Carleman.Physical.spatial_weight_upper
#print axioms Carleman.Physical.spatial_weight_upper
#check @Carleman.Physical.spatial_weight_lower
#print axioms Carleman.Physical.spatial_weight_lower
#check @Carleman.Physical.spatial_weight_upper_sq
#print axioms Carleman.Physical.spatial_weight_upper_sq
#check @Carleman.Physical.spatial_weight_lower_sq
#print axioms Carleman.Physical.spatial_weight_lower_sq
#check @Carleman.Physical.physical_spatial_endpoint
#print axioms Carleman.Physical.physical_spatial_endpoint
#check @Carleman.Physical.physical_spatial_middle
#print axioms Carleman.Physical.physical_spatial_middle
#check @Carleman.Physical.cubic_exponential_bound
#print axioms Carleman.Physical.cubic_exponential_bound
#check @Carleman.Physical.linear_exponential_decay
#print axioms Carleman.Physical.linear_exponential_decay
#check @Carleman.Physical.spatial_observation_weight_bound
#print axioms Carleman.Physical.spatial_observation_weight_bound
#check @Carleman.Physical.physical_weighted_remainder_energy
#print axioms Carleman.Physical.physical_weighted_remainder_energy
#check @Carleman.Physical.physical_weighted_remainder_decay
#print axioms Carleman.Physical.physical_weighted_remainder_decay
#check @Carleman.Physical.physical_weighted_initial_recovery
#print axioms Carleman.Physical.physical_weighted_initial_recovery

#check @Carleman.Physical.weighted_potential_bound
#print axioms Carleman.Physical.weighted_potential_bound
#check @Carleman.Physical.physicalCutoffLoad
#print axioms Carleman.Physical.physicalCutoffLoad
#check @Carleman.Physical.physical_cutoff_load_equation
#print axioms Carleman.Physical.physical_cutoff_load_equation
#check @Carleman.Physical.physical_cutoff_load_bound
#print axioms Carleman.Physical.physical_cutoff_load_bound
#check @Carleman.Physical.physicalWeight_lower_half
#print axioms Carleman.Physical.physicalWeight_lower_half
#check @Carleman.Physical.physical_potential_budget
#print axioms Carleman.Physical.physical_potential_budget
#check @Carleman.Physical.physicalWeightedSq
#print axioms Carleman.Physical.physicalWeightedSq
#check @Carleman.Physical.physicalWeightedCubeSq
#print axioms Carleman.Physical.physicalWeightedCubeSq
#check @Carleman.Physical.PhysicalLoadCarleman
#print axioms Carleman.Physical.PhysicalLoadCarleman
#check @Carleman.Physical.cutoff_observation_budget
#print axioms Carleman.Physical.cutoff_observation_budget
#check @Carleman.Physical.cutoff_carleman_absorb
#print axioms Carleman.Physical.cutoff_carleman_absorb
#check @Carleman.Physical.physicalEndpointRate
#print axioms Carleman.Physical.physicalEndpointRate
#check @Carleman.Physical.physicalEndpointRate_pos
#print axioms Carleman.Physical.physicalEndpointRate_pos
#check @Carleman.Physical.physicalInitialFactor
#print axioms Carleman.Physical.physicalInitialFactor
#check @Carleman.Physical.physicalInitialFactor_pos
#print axioms Carleman.Physical.physicalInitialFactor_pos
#check @Carleman.Physical.physicalRemainderFactor
#print axioms Carleman.Physical.physicalRemainderFactor
#check @Carleman.Physical.physicalObservationConstant
#print axioms Carleman.Physical.physicalObservationConstant
#check @Carleman.Physical.physicalObservationConstant_pos
#print axioms Carleman.Physical.physicalObservationConstant_pos
#check @Carleman.Physical.physical_observation_of_load_carleman
#print axioms Carleman.Physical.physical_observation_of_load_carleman
#check @Carleman.Physical.physical_observation_uniform_of_load_carleman
#print axioms Carleman.Physical.physical_observation_uniform_of_load_carleman

#check @Carleman.Physical.multiplier_clm_norm
#print axioms Carleman.Physical.multiplier_clm_norm
#check @Carleman.Physical.multiplier_clm_symmetric
#print axioms Carleman.Physical.multiplier_clm_symmetric
#check @Carleman.Physical.conformingPotential
#print axioms Carleman.Physical.conformingPotential
#check @Carleman.Physical.conformingPotential_apply
#print axioms Carleman.Physical.conformingPotential_apply
#check @Carleman.Physical.conformingPotential_symmetric
#print axioms Carleman.Physical.conformingPotential_symmetric
#check @Carleman.Physical.conformingPotential_norm
#print axioms Carleman.Physical.conformingPotential_norm
#check @Carleman.Physical.conformingPotential_form
#print axioms Carleman.Physical.conformingPotential_form
#check @Carleman.Physical.conforming_load_right_inverse
#print axioms Carleman.Physical.conforming_load_right_inverse
#check @Carleman.Physical.conforming_mass_norm
#print axioms Carleman.Physical.conforming_mass_norm
#check @Carleman.Physical.conformingAmbientControl
#print axioms Carleman.Physical.conformingAmbientControl
#check @Carleman.Physical.conformingAmbientControl_norm
#print axioms Carleman.Physical.conformingAmbientControl_norm
#check @Carleman.Physical.conformingAmbientControl_adjoint
#print axioms Carleman.Physical.conformingAmbientControl_adjoint
#check @Carleman.Physical.conforming_observation_integral
#print axioms Carleman.Physical.conforming_observation_integral
#check @Carleman.Physical.restrictRegionLp
#print axioms Carleman.Physical.restrictRegionLp
#check @Carleman.Physical.restrictRegionLp_ae
#print axioms Carleman.Physical.restrictRegionLp_ae
#check @Carleman.Physical.restrictRegionLp_norm_le
#print axioms Carleman.Physical.restrictRegionLp_norm_le
#check @Carleman.Physical.restrictRegionLinear
#print axioms Carleman.Physical.restrictRegionLinear
#check @Carleman.Physical.restrictRegionCLM
#print axioms Carleman.Physical.restrictRegionCLM
#check @Carleman.Physical.integral_inner_zeroExtend
#print axioms Carleman.Physical.integral_inner_zeroExtend
#check @Carleman.Physical.restrictRegion_adjoint
#print axioms Carleman.Physical.restrictRegion_adjoint
#check @Carleman.Physical.zeroExtend_restrictRegion
#print axioms Carleman.Physical.zeroExtend_restrictRegion
#check @Carleman.Physical.restrictRegion_norm_eq_cutoff
#print axioms Carleman.Physical.restrictRegion_norm_eq_cutoff
#check @Carleman.Physical.restrictRegionCLM_norm
#print axioms Carleman.Physical.restrictRegionCLM_norm
#check @Carleman.Physical.conformingRegionControl
#print axioms Carleman.Physical.conformingRegionControl
#check @Carleman.Physical.conformingRegionControl_apply
#print axioms Carleman.Physical.conformingRegionControl_apply
#check @Carleman.Physical.conformingRegionControl_adjoint
#print axioms Carleman.Physical.conformingRegionControl_adjoint
#check @Carleman.Physical.conformingRegionControl_adjoint_apply
#print axioms Carleman.Physical.conformingRegionControl_adjoint_apply
#check @Carleman.Physical.conformingRegionControl_norm
#print axioms Carleman.Physical.conformingRegionControl_norm
#check @Carleman.Physical.conforming_region_observation_norm
#print axioms Carleman.Physical.conforming_region_observation_norm
#check @Carleman.Physical.conformingRegionControl_pairing
#print axioms Carleman.Physical.conformingRegionControl_pairing
#check @Carleman.Physical.conforming_physical_observation_uniform
#print axioms Carleman.Physical.conforming_physical_observation_uniform
#check @Carleman.Physical.conforming_observation_control_uniform
#print axioms Carleman.Physical.conforming_observation_control_uniform

#check @Carleman.Physical.physical_cube_le_nodeEnergy
#print axioms Carleman.Physical.physical_cube_le_nodeEnergy
#check @Carleman.Physical.physical_load_eq_transfer
#print axioms Carleman.Physical.physical_load_eq_transfer
#check @Carleman.Physical.physical_observation_eq_transfer
#print axioms Carleman.Physical.physical_observation_eq_transfer
#check @Carleman.Physical.physical_load_carleman_of_transfer
#print axioms Carleman.Physical.physical_load_carleman_of_transfer
#check @Carleman.Physical.conformingReconstruction
#print axioms Carleman.Physical.conformingReconstruction
#check @Carleman.Physical.conformingReconstruction_RH
#print axioms Carleman.Physical.conformingReconstruction_RH
#check @Carleman.Physical.conformingLoad
#print axioms Carleman.Physical.conformingLoad
#check @Carleman.Physical.conformingWeightedState
#print axioms Carleman.Physical.conformingWeightedState
#check @Carleman.Physical.conformingWeightedState_definite
#print axioms Carleman.Physical.conformingWeightedState_definite
#check @Carleman.Physical.conformingHeatGeometry
#print axioms Carleman.Physical.conformingHeatGeometry
#check @Carleman.Physical.ConformingHeatData
#print axioms Carleman.Physical.ConformingHeatData
#check @Carleman.Physical.conforming_heat_load_uniform
#print axioms Carleman.Physical.conforming_heat_load_uniform
#check @Carleman.Physical.physicalMeshScale
#print axioms Carleman.Physical.physicalMeshScale
#check @Carleman.Physical.physicalMeshScale_pos
#print axioms Carleman.Physical.physicalMeshScale_pos
#check @Carleman.Physical.conforming_heat_observation_control_uniform
#print axioms Carleman.Physical.conforming_heat_observation_control_uniform

#check @Carleman.Physical.conformingEnergyLift
#print axioms Carleman.Physical.conformingEnergyLift
#check @Carleman.Physical.conformingEnergyLift_value
#print axioms Carleman.Physical.conformingEnergyLift_value
#check @Carleman.Physical.galerkinStiffness
#print axioms Carleman.Physical.galerkinStiffness
#check @Carleman.Physical.galerkinStiffness_form
#print axioms Carleman.Physical.galerkinStiffness_form
#check @Carleman.Physical.galerkinStiffness_symmetric
#print axioms Carleman.Physical.galerkinStiffness_symmetric
#check @Carleman.Physical.galerkinStiffness_nonneg
#print axioms Carleman.Physical.galerkinStiffness_nonneg
#check @Carleman.Physical.galerkinStiffness_unique
#print axioms Carleman.Physical.galerkinStiffness_unique
#check @Carleman.Physical.galerkinStiffness_defect_zero
#print axioms Carleman.Physical.galerkinStiffness_defect_zero
#check @Carleman.Physical.conformingReconstruction_injective
#print axioms Carleman.Physical.conformingReconstruction_injective
#check @Carleman.Physical.conformingReconstruction_G
#print axioms Carleman.Physical.conformingReconstruction_G
#check @Carleman.Physical.conformingReconstruction_QH
#print axioms Carleman.Physical.conformingReconstruction_QH
#check @Carleman.Physical.conforming_weighted_observation
#print axioms Carleman.Physical.conforming_weighted_observation
#check @Carleman.Physical.galerkinNumericalData
#print axioms Carleman.Physical.galerkinNumericalData
#check @Carleman.Physical.GalerkinHeatData
#print axioms Carleman.Physical.GalerkinHeatData
#check @Carleman.Physical.GalerkinHeatData.toConforming
#print axioms Carleman.Physical.GalerkinHeatData.toConforming
#check @Carleman.Physical.galerkin_heat_observation_control_uniform
#print axioms Carleman.Physical.galerkin_heat_observation_control_uniform

#check @Carleman.Physical.weightedInclusion
#print axioms Carleman.Physical.weightedInclusion
#check @Carleman.Physical.galerkinWeightedTest
#print axioms Carleman.Physical.galerkinWeightedTest
#check @Carleman.Physical.galerkinWeightedTest_pairing
#print axioms Carleman.Physical.galerkinWeightedTest_pairing
#check @Carleman.Physical.galerkinWeightedTest_apply
#print axioms Carleman.Physical.galerkinWeightedTest_apply
#check @Carleman.Physical.galerkinWeightedTest_symmetric
#print axioms Carleman.Physical.galerkinWeightedTest_symmetric
#check @Carleman.Physical.galerkinWeightedTest_energy
#print axioms Carleman.Physical.galerkinWeightedTest_energy
#check @Carleman.Physical.galerkinWeightedTest_nonneg
#print axioms Carleman.Physical.galerkinWeightedTest_nonneg
#check @Carleman.Physical.weightedInclusionDerivative
#print axioms Carleman.Physical.weightedInclusionDerivative
#check @Carleman.Physical.galerkinWeightedTestDerivative
#print axioms Carleman.Physical.galerkinWeightedTestDerivative
#check @Carleman.Physical.galerkinWeightedTestDerivative_pairing
#print axioms Carleman.Physical.galerkinWeightedTestDerivative_pairing
#check @Carleman.Physical.galerkinWeightedTest_endpoint
#print axioms Carleman.Physical.galerkinWeightedTest_endpoint
#check @Carleman.Physical.galerkinWeightedTest_hasDeriv
#print axioms Carleman.Physical.galerkinWeightedTest_hasDeriv
#check @Carleman.Physical.weightedInclusionDerivative_bound
#print axioms Carleman.Physical.weightedInclusionDerivative_bound
#check @Carleman.Physical.galerkinWeightedTest_time_bound
#print axioms Carleman.Physical.galerkinWeightedTest_time_bound
#check @Carleman.Physical.galerkinWeightedTest_time_bound_uniform
#print axioms Carleman.Physical.galerkinWeightedTest_time_bound_uniform
#check @Carleman.Physical.GalerkinSuperapprox
#print axioms Carleman.Physical.GalerkinSuperapprox
#check @Carleman.Physical.galerkinWeightedTestData
#print axioms Carleman.Physical.galerkinWeightedTestData
#check @Carleman.Physical.ProjectedHeatData
#print axioms Carleman.Physical.ProjectedHeatData
#check @Carleman.Physical.ProjectedHeatData.toGalerkin
#print axioms Carleman.Physical.ProjectedHeatData.toGalerkin
#check @Carleman.Physical.projected_heat_observation_control_uniform
#print axioms Carleman.Physical.projected_heat_observation_control_uniform

#check @Carleman.Physical.conformingProjector
#print axioms Carleman.Physical.conformingProjector
#check @Carleman.Physical.conformingProjector_eq_Q
#print axioms Carleman.Physical.conformingProjector_eq_Q
#check @Carleman.Physical.conformingProjector_inclusion
#print axioms Carleman.Physical.conformingProjector_inclusion
#check @Carleman.Physical.conformingProjector_error_decomposition
#print axioms Carleman.Physical.conformingProjector_error_decomposition
#check @Carleman.Physical.conformingProjector_l2_error
#print axioms Carleman.Physical.conformingProjector_l2_error
#check @Carleman.Physical.conformingProjector_energy_error
#print axioms Carleman.Physical.conformingProjector_energy_error
#check @Carleman.Physical.ConformingInterpolationBounds
#print axioms Carleman.Physical.ConformingInterpolationBounds
#check @Carleman.Physical.conformingWeightedApproximation_of_interpolation
#print axioms Carleman.Physical.conformingWeightedApproximation_of_interpolation
#check @Carleman.Physical.GalerkinSuperapproxInterpolation
#print axioms Carleman.Physical.GalerkinSuperapproxInterpolation
#check @Carleman.Physical.galerkinSuperapprox_of_interpolation
#print axioms Carleman.Physical.galerkinSuperapprox_of_interpolation
#check @Carleman.Physical.conformingHeatGradient
#print axioms Carleman.Physical.conformingHeatGradient
#check @Carleman.Physical.conformingHeatGradient_nonneg
#print axioms Carleman.Physical.conformingHeatGradient_nonneg
#check @Carleman.Physical.conformingHeatNorm_le
#print axioms Carleman.Physical.conformingHeatNorm_le
#check @Carleman.Physical.scaled_seminorm_le_auxiliary
#print axioms Carleman.Physical.scaled_seminorm_le_auxiliary
#check @Carleman.Physical.conformingHeatNorm_le_auxiliary
#print axioms Carleman.Physical.conformingHeatNorm_le_auxiliary
#check @Carleman.Physical.conformingHeatInverse_of_gradient
#print axioms Carleman.Physical.conformingHeatInverse_of_gradient
#check @Carleman.Physical.HeatInterpolationData
#print axioms Carleman.Physical.HeatInterpolationData
#check @Carleman.Physical.HeatInterpolationData.toBounds
#print axioms Carleman.Physical.HeatInterpolationData.toBounds
#check @Carleman.Physical.HeatInterpolationData.approximation
#print axioms Carleman.Physical.HeatInterpolationData.approximation
#check @Carleman.Physical.HeatSuperapproxData
#print axioms Carleman.Physical.HeatSuperapproxData
#check @Carleman.Physical.HeatSuperapproxData.toBounds
#print axioms Carleman.Physical.HeatSuperapproxData.toBounds
#check @Carleman.Physical.HeatSuperapproxData.superapprox
#print axioms Carleman.Physical.HeatSuperapproxData.superapprox
#check @Carleman.Physical.heatInterpolationErrors
#print axioms Carleman.Physical.heatInterpolationErrors
#check @Carleman.Physical.heatInterpolationErrors_orders
#print axioms Carleman.Physical.heatInterpolationErrors_orders
#check @Carleman.Physical.interpolatedHeatNumericalData
#print axioms Carleman.Physical.interpolatedHeatNumericalData

#check @Carleman.affineCoordinate
#print axioms Carleman.affineCoordinate
#check @Carleman.affineCoordinate_continuous
#print axioms Carleman.affineCoordinate_continuous
#check @Carleman.affineCoordinate_bound
#print axioms Carleman.affineCoordinate_bound
#check @Carleman.affineCellGenerator
#print axioms Carleman.affineCellGenerator
#check @Carleman.affineCellGenerator_ae
#print axioms Carleman.affineCellGenerator_ae
#check @Carleman.piecewiseAffineMap
#print axioms Carleman.piecewiseAffineMap
#check @Carleman.piecewiseAffineMap_ae
#print axioms Carleman.piecewiseAffineMap_ae
#check @Carleman.piecewiseAffineSpace
#print axioms Carleman.piecewiseAffineSpace
#check @Carleman.mem_piecewiseAffineSpace_iff
#print axioms Carleman.mem_piecewiseAffineSpace_iff
#check @Carleman.piecewiseAffineSpace_bound_independent
#print axioms Carleman.piecewiseAffineSpace_bound_independent
#check @Carleman.piecewiseAffineSpace_finiteDimensional
#print axioms Carleman.piecewiseAffineSpace_finiteDimensional
#check @Carleman.conformingPiecewiseAffineSpace
#print axioms Carleman.conformingPiecewiseAffineSpace
#check @Carleman.conformingPiecewiseAffineSpace_finiteDimensional
#print axioms Carleman.conformingPiecewiseAffineSpace_finiteDimensional
#check @Carleman.conformingPiecewiseAffineSpace_le
#print axioms Carleman.conformingPiecewiseAffineSpace_le
#check @Carleman.affineCoordinate_sum
#print axioms Carleman.affineCoordinate_sum
#check @Carleman.piecewiseAffine_formula_on_cell
#print axioms Carleman.piecewiseAffine_formula_on_cell
#check @Carleman.mem_piecewiseAffineSpace_iff_on_cells
#print axioms Carleman.mem_piecewiseAffineSpace_iff_on_cells
#check @Carleman.mem_conformingPiecewiseAffineSpace_iff
#print axioms Carleman.mem_conformingPiecewiseAffineSpace_iff
#check @Carleman.Physical.affineGalerkinSpace
#print axioms Carleman.Physical.affineGalerkinSpace
#check @Carleman.Physical.affineGalerkinStiffness
#print axioms Carleman.Physical.affineGalerkinStiffness
#check @Carleman.Physical.affineGalerkinStiffness_pairing
#print axioms Carleman.Physical.affineGalerkinStiffness_pairing
#check @Carleman.Physical.affineGalerkinStiffness_symmetric
#print axioms Carleman.Physical.affineGalerkinStiffness_symmetric
#check @Carleman.Physical.affineGalerkinStiffness_nonneg
#print axioms Carleman.Physical.affineGalerkinStiffness_nonneg
#check @Carleman.Physical.affineGalerkinSpace_membership
#print axioms Carleman.Physical.affineGalerkinSpace_membership

#check @Carleman.simplicialCell
#print axioms Carleman.simplicialCell
#check @Carleman.simplicialCell_convex
#print axioms Carleman.simplicialCell_convex
#check @Carleman.simplicialCell_compact
#print axioms Carleman.simplicialCell_compact
#check @Carleman.simplicialCell_measurable
#print axioms Carleman.simplicialCell_measurable
#check @Carleman.simplicialCell_frontier_null
#print axioms Carleman.simplicialCell_frontier_null
#check @Carleman.simplicialCell_interior_nonempty
#print axioms Carleman.simplicialCell_interior_nonempty
#check @Carleman.simplicialRadius
#print axioms Carleman.simplicialRadius
#check @Carleman.simplicialRadius_nonneg
#print axioms Carleman.simplicialRadius_nonneg
#check @Carleman.simplicialCell_norm_le
#print axioms Carleman.simplicialCell_norm_le
#check @Carleman.simplicialCells_ae_partition
#print axioms Carleman.simplicialCells_ae_partition
#check @Carleman.SimplicialPartition
#print axioms Carleman.SimplicialPartition
#check @Carleman.SimplicialPartition.cell
#print axioms Carleman.SimplicialPartition.cell
#check @Carleman.SimplicialPartition.vertex_mem_closure
#print axioms Carleman.SimplicialPartition.vertex_mem_closure
#check @Carleman.SimplicialPartition.cells_union
#print axioms Carleman.SimplicialPartition.cells_union
#check @Carleman.SimplicialPartition.ae_partition
#print axioms Carleman.SimplicialPartition.ae_partition
#check @Carleman.SimplicialPartition.conformingSpace
#print axioms Carleman.SimplicialPartition.conformingSpace
#check @Carleman.SimplicialPartition.conformingSpace_finiteDimensional
#print axioms Carleman.SimplicialPartition.conformingSpace_finiteDimensional
#check @Carleman.SimplicialPartition.conformingSpace_le
#print axioms Carleman.SimplicialPartition.conformingSpace_le
#check @Carleman.SimplicialPartition.mem_conformingSpace_iff
#print axioms Carleman.SimplicialPartition.mem_conformingSpace_iff
#check @Carleman.simplexAffineBasis
#print axioms Carleman.simplexAffineBasis
#check @Carleman.simplexAffineBasis_apply
#print axioms Carleman.simplexAffineBasis_apply
#check @Carleman.simplexBarycentric
#print axioms Carleman.simplexBarycentric
#check @Carleman.simplexBarycentric_vertex
#print axioms Carleman.simplexBarycentric_vertex
#check @Carleman.simplexBarycentric_sum
#print axioms Carleman.simplexBarycentric_sum
#check @Carleman.simplexBarycentric_nonneg
#print axioms Carleman.simplexBarycentric_nonneg
#check @Carleman.simplexNodalInterpolant
#print axioms Carleman.simplexNodalInterpolant
#check @Carleman.simplexNodalInterpolant_apply
#print axioms Carleman.simplexNodalInterpolant_apply
#check @Carleman.simplexNodalInterpolant_vertex
#print axioms Carleman.simplexNodalInterpolant_vertex
#check @Carleman.simplexNodalInterpolant_reproduces
#print axioms Carleman.simplexNodalInterpolant_reproduces
#check @Carleman.simplexNodalInterpolant_abs_le
#print axioms Carleman.simplexNodalInterpolant_abs_le

#check @Carleman.SimplicialPartition.FaceMatching
#print axioms Carleman.SimplicialPartition.FaceMatching
#check @Carleman.SimplicialPartition.localNodal
#print axioms Carleman.SimplicialPartition.localNodal
#check @Carleman.SimplicialPartition.localNodal_vertex
#print axioms Carleman.SimplicialPartition.localNodal_vertex
#check @Carleman.SimplicialPartition.localNodal_agree
#print axioms Carleman.SimplicialPartition.localNodal_agree
#check @Carleman.SimplicialPartition.nodalFunction
#print axioms Carleman.SimplicialPartition.nodalFunction
#check @Carleman.SimplicialPartition.nodalFunction_on_cell
#print axioms Carleman.SimplicialPartition.nodalFunction_on_cell
#check @Carleman.SimplicialPartition.nodalFunction_vertex
#print axioms Carleman.SimplicialPartition.nodalFunction_vertex
#check @Carleman.SimplicialPartition.nodalFunction_continuousOn
#print axioms Carleman.SimplicialPartition.nodalFunction_continuousOn
#check @Carleman.SimplicialPartition.nodalFunction_reproduces
#print axioms Carleman.SimplicialPartition.nodalFunction_reproduces
#check @Carleman.affinePolynomialCoefficients
#print axioms Carleman.affinePolynomialCoefficients
#check @Carleman.affinePolynomialCoefficients_apply
#print axioms Carleman.affinePolynomialCoefficients_apply
#check @Carleman.SimplicialPartition.nodalBound
#print axioms Carleman.SimplicialPartition.nodalBound
#check @Carleman.SimplicialPartition.nodalBound_nonneg
#print axioms Carleman.SimplicialPartition.nodalBound_nonneg
#check @Carleman.SimplicialPartition.nodalBound_vertex
#print axioms Carleman.SimplicialPartition.nodalBound_vertex
#check @Carleman.SimplicialPartition.nodalFunction_bound
#print axioms Carleman.SimplicialPartition.nodalFunction_bound
#check @Carleman.SimplicialPartition.nodalFunction_memLp
#print axioms Carleman.SimplicialPartition.nodalFunction_memLp
#check @Carleman.SimplicialPartition.nodalLp
#print axioms Carleman.SimplicialPartition.nodalLp
#check @Carleman.SimplicialPartition.nodalLp_ae
#print axioms Carleman.SimplicialPartition.nodalLp_ae
#check @Carleman.SimplicialPartition.nodalLp_piecewise_affine
#print axioms Carleman.SimplicialPartition.nodalLp_piecewise_affine
#check @Carleman.SimplicialPartition.nodalFunction_congr
#print axioms Carleman.SimplicialPartition.nodalFunction_congr
#check @Carleman.SimplicialPartition.nodalFunction_add
#print axioms Carleman.SimplicialPartition.nodalFunction_add
#check @Carleman.SimplicialPartition.nodalFunction_smul
#print axioms Carleman.SimplicialPartition.nodalFunction_smul
#check @Carleman.SimplicialPartition.nodalFunctionLinearMap
#print axioms Carleman.SimplicialPartition.nodalFunctionLinearMap
#check @Carleman.SimplicialPartition.nodalFunction_unique
#print axioms Carleman.SimplicialPartition.nodalFunction_unique
#check @Carleman.SimplicialPartition.nodalFunction_idempotent
#print axioms Carleman.SimplicialPartition.nodalFunction_idempotent
#check @Carleman.SimplicialPartition.nodalFunction_abs_le
#print axioms Carleman.SimplicialPartition.nodalFunction_abs_le
#check @Carleman.SimplicialPartition.nodalLp_congr
#print axioms Carleman.SimplicialPartition.nodalLp_congr
#check @Carleman.SimplicialPartition.nodalLp_add
#print axioms Carleman.SimplicialPartition.nodalLp_add
#check @Carleman.SimplicialPartition.nodalLp_smul
#print axioms Carleman.SimplicialPartition.nodalLp_smul
#check @Carleman.SimplicialPartition.nodalLpLinearMap
#print axioms Carleman.SimplicialPartition.nodalLpLinearMap

#check @Carleman.lipschitzWith_of_eventually_norm_sub_le
#print axioms Carleman.lipschitzWith_of_eventually_norm_sub_le
#check @Carleman.finite_selection_eventually_norm_sub_le
#print axioms Carleman.finite_selection_eventually_norm_sub_le
#check @Carleman.lipschitzWith_finite_selection
#print axioms Carleman.lipschitzWith_finite_selection
#check @Carleman.SimplicialPartition.localNodalDerivative
#print axioms Carleman.SimplicialPartition.localNodalDerivative
#check @Carleman.SimplicialPartition.localNodalDerivative_apply
#print axioms Carleman.SimplicialPartition.localNodalDerivative_apply
#check @Carleman.SimplicialPartition.localNodal_hasFDerivAt
#print axioms Carleman.SimplicialPartition.localNodal_hasFDerivAt
#check @Carleman.SimplicialPartition.nodalFunction_hasFDerivAt_on_interior
#print axioms Carleman.SimplicialPartition.nodalFunction_hasFDerivAt_on_interior
#check @Carleman.SimplicialPartition.ae_mem_cell_interior
#print axioms Carleman.SimplicialPartition.ae_mem_cell_interior
#check @Carleman.SimplicialPartition.nodalDerivativeFunction
#print axioms Carleman.SimplicialPartition.nodalDerivativeFunction
#check @Carleman.SimplicialPartition.nodalDerivativeFunction_on_interior
#print axioms Carleman.SimplicialPartition.nodalDerivativeFunction_on_interior
#check @Carleman.SimplicialPartition.nodalFunction_hasFDerivAt_ae
#print axioms Carleman.SimplicialPartition.nodalFunction_hasFDerivAt_ae
#check @Carleman.SimplicialPartition.nodalDerivativeFunction_memLp
#print axioms Carleman.SimplicialPartition.nodalDerivativeFunction_memLp
#check @Carleman.SimplicialPartition.nodalDerivativeLp
#print axioms Carleman.SimplicialPartition.nodalDerivativeLp
#check @Carleman.SimplicialPartition.nodalDerivativeLp_ae
#print axioms Carleman.SimplicialPartition.nodalDerivativeLp_ae
#check @Carleman.SimplicialPartition.nodalFunction_fderiv_memLp
#print axioms Carleman.SimplicialPartition.nodalFunction_fderiv_memLp
#check @Carleman.SimplicialPartition.BoundaryFitted
#print axioms Carleman.SimplicialPartition.BoundaryFitted
#check @Carleman.SimplicialPartition.localNodal_zero_on_boundary
#print axioms Carleman.SimplicialPartition.localNodal_zero_on_boundary
#check @Carleman.SimplicialPartition.nodalFunction_zero_outside
#print axioms Carleman.SimplicialPartition.nodalFunction_zero_outside
#check @Carleman.SimplicialPartition.nodalFunction_zero_on_boundary
#print axioms Carleman.SimplicialPartition.nodalFunction_zero_on_boundary
#check @Carleman.SimplicialPartition.nodalFunction_zero_on_compl
#print axioms Carleman.SimplicialPartition.nodalFunction_zero_on_compl
#check @Carleman.SimplicialPartition.nodalFunction_continuous_of_boundary
#print axioms Carleman.SimplicialPartition.nodalFunction_continuous_of_boundary
#check @Carleman.SimplicialPartition.nodalFunction_hasCompactSupport
#print axioms Carleman.SimplicialPartition.nodalFunction_hasCompactSupport
#check @Carleman.SimplicialPartition.nodalLipschitzConstant
#print axioms Carleman.SimplicialPartition.nodalLipschitzConstant
#check @Carleman.SimplicialPartition.localNodal_lipschitzWith
#print axioms Carleman.SimplicialPartition.localNodal_lipschitzWith
#check @Carleman.SimplicialPartition.nodalFunction_lipschitzWith
#print axioms Carleman.SimplicialPartition.nodalFunction_lipschitzWith
#check @Carleman.weakSpatialDerivative_of_lipschitz
#print axioms Carleman.weakSpatialDerivative_of_lipschitz
#check @Carleman.SimplicialPartition.nodalDirectionalLp
#print axioms Carleman.SimplicialPartition.nodalDirectionalLp
#check @Carleman.SimplicialPartition.nodalDirectionalLp_ae
#print axioms Carleman.SimplicialPartition.nodalDirectionalLp_ae
#check @Carleman.SimplicialPartition.nodalLp_weakDerivative
#print axioms Carleman.SimplicialPartition.nodalLp_weakDerivative
#check @Carleman.scalarZeroFiber
#print axioms Carleman.scalarZeroFiber
#check @Carleman.derivativeOneFiber
#print axioms Carleman.derivativeOneFiber
#check @Carleman.scalarZeroFiber_component
#print axioms Carleman.scalarZeroFiber_component
#check @Carleman.derivativeOneFiber_component
#print axioms Carleman.derivativeOneFiber_component
#check @Carleman.firstOrderFields
#print axioms Carleman.firstOrderFields
#check @Carleman.firstOrderJet
#print axioms Carleman.firstOrderJet
#check @Carleman.firstOrderJet_value
#print axioms Carleman.firstOrderJet_value
#check @Carleman.SimplicialPartition.nodalSobolevJet
#print axioms Carleman.SimplicialPartition.nodalSobolevJet
#check @Carleman.SimplicialPartition.nodalSobolevJet_value
#print axioms Carleman.SimplicialPartition.nodalSobolevJet_value
#check @Carleman.SimplicialPartition.nodalLp_mem_sobolev
#print axioms Carleman.SimplicialPartition.nodalLp_mem_sobolev

#check @Carleman.SimplicialPartition.nodalDerivativeFunction_zero_outside
#print axioms Carleman.SimplicialPartition.nodalDerivativeFunction_zero_outside
#check @Carleman.SimplicialPartition.nodalFunction_hasFDerivAt_global_ae
#print axioms Carleman.SimplicialPartition.nodalFunction_hasFDerivAt_global_ae
#check @Carleman.SimplicialPartition.nodalDerivativeFunction_global_memLp
#print axioms Carleman.SimplicialPartition.nodalDerivativeFunction_global_memLp
#check @Carleman.SimplicialPartition.nodalGlobalDerivativeLp
#print axioms Carleman.SimplicialPartition.nodalGlobalDerivativeLp
#check @Carleman.SimplicialPartition.nodalGlobalDerivativeLp_ae
#print axioms Carleman.SimplicialPartition.nodalGlobalDerivativeLp_ae
#check @Carleman.SimplicialPartition.nodalFunction_global_memLp
#print axioms Carleman.SimplicialPartition.nodalFunction_global_memLp
#check @Carleman.SimplicialPartition.nodalGlobalLp
#print axioms Carleman.SimplicialPartition.nodalGlobalLp
#check @Carleman.SimplicialPartition.nodalGlobalLp_ae
#print axioms Carleman.SimplicialPartition.nodalGlobalLp_ae
#check @Carleman.weakSpatialDerivative_of_lipschitz_full
#print axioms Carleman.weakSpatialDerivative_of_lipschitz_full
#check @Carleman.lipschitzGlobalJet
#print axioms Carleman.lipschitzGlobalJet
#check @Carleman.lipschitzGlobalJet_value
#print axioms Carleman.lipschitzGlobalJet_value
#check @Carleman.SimplicialPartition.nodalGlobalSobolevJet
#print axioms Carleman.SimplicialPartition.nodalGlobalSobolevJet
#check @Carleman.SimplicialPartition.nodalGlobalSobolevJet_value
#print axioms Carleman.SimplicialPartition.nodalGlobalSobolevJet_value
#check @Carleman.SimplicialPartition.nodalGlobalLp_mem_sobolev
#print axioms Carleman.SimplicialPartition.nodalGlobalLp_mem_sobolev
#check @Carleman.SpatialTest.memLp_fderiv
#print axioms Carleman.SpatialTest.memLp_fderiv
#check @Carleman.SpatialTest.fderivLp
#print axioms Carleman.SpatialTest.fderivLp
#check @Carleman.SpatialTest.fderivLp_ae
#print axioms Carleman.SpatialTest.fderivLp_ae
#check @Carleman.SpatialTest.sobolevJet
#print axioms Carleman.SpatialTest.sobolevJet
#check @Carleman.SpatialTest.sobolevJet_value
#print axioms Carleman.SpatialTest.sobolevJet_value
#check @Carleman.dirichletJetSpace
#print axioms Carleman.dirichletJetSpace
#check @Carleman.dirichletSubspace
#print axioms Carleman.dirichletSubspace
#check @Carleman.dirichletSubspace_sobolev
#print axioms Carleman.dirichletSubspace_sobolev
#check @Carleman.test_mem_dirichletJetSpace
#print axioms Carleman.test_mem_dirichletJetSpace
#check @Carleman.test_mem_dirichletSubspace
#print axioms Carleman.test_mem_dirichletSubspace
#check @Carleman.mem_dirichletJetSpace_iff
#print axioms Carleman.mem_dirichletJetSpace_iff
#check @Carleman.dirichletSubspace_closed
#print axioms Carleman.dirichletSubspace_closed
#check @Carleman.dirichletSubspace_dense
#print axioms Carleman.dirichletSubspace_dense

#check @Carleman.SpatialTest.zeroTest
#print axioms Carleman.SpatialTest.zeroTest
#check @Carleman.SpatialTest.addTest
#print axioms Carleman.SpatialTest.addTest
#check @Carleman.SpatialTest.smulTest
#print axioms Carleman.SpatialTest.smulTest
#check @Carleman.SpatialTest.zeroTest_jet
#print axioms Carleman.SpatialTest.zeroTest_jet
#check @Carleman.SpatialTest.addTest_jet
#print axioms Carleman.SpatialTest.addTest_jet
#check @Carleman.SpatialTest.smulTest_jet
#print axioms Carleman.SpatialTest.smulTest_jet
#check @Carleman.exists_test_of_mem_test_span
#print axioms Carleman.exists_test_of_mem_test_span
#check @Carleman.SpatialTest.linearMul
#print axioms Carleman.SpatialTest.linearMul
#check @Carleman.SpatialTest.linearMul_derivative
#print axioms Carleman.SpatialTest.linearMul_derivative
#check @Carleman.SpatialTest.weakDerivative
#print axioms Carleman.SpatialTest.weakDerivative
#check @Carleman.SpatialTest.linearMul_norm_le
#print axioms Carleman.SpatialTest.linearMul_norm_le
#check @Carleman.SpatialTest.poincare_slab
#print axioms Carleman.SpatialTest.poincare_slab
#check @Carleman.SpatialTest.sobolevJet_derivative
#print axioms Carleman.SpatialTest.sobolevJet_derivative
#check @Carleman.derivativeComponent_norm_le
#print axioms Carleman.derivativeComponent_norm_le
#check @Carleman.dirichlet_poincare
#print axioms Carleman.dirichlet_poincare
#check @Carleman.WeakSobolevJet.norm_zero_field
#print axioms Carleman.WeakSobolevJet.norm_zero_field
#check @Carleman.DirichletEnergy
#print axioms Carleman.DirichletEnergy
#check @Carleman.dirichletGradient
#print axioms Carleman.dirichletGradient
#check @Carleman.dirichletForm
#print axioms Carleman.dirichletForm
#check @Carleman.dirichletForm_apply
#print axioms Carleman.dirichletForm_apply
#check @Carleman.dirichletForm_symmetric
#print axioms Carleman.dirichletForm_symmetric
#check @Carleman.dirichletForm_integral
#print axioms Carleman.dirichletForm_integral
#check @Carleman.dirichletEnergy_norm_sq
#print axioms Carleman.dirichletEnergy_norm_sq
#check @Carleman.dirichletForm_coercive
#print axioms Carleman.dirichletForm_coercive
#check @Carleman.dirichletOriginalForm
#print axioms Carleman.dirichletOriginalForm
#check @Carleman.dirichletForm_coercive_of_bounded
#print axioms Carleman.dirichletForm_coercive_of_bounded
#check @Carleman.boundedDirichletOriginalForm
#print axioms Carleman.boundedDirichletOriginalForm

#check @Carleman.derivativeField_inner
#print axioms Carleman.derivativeField_inner
#check @Carleman.firstDerivativeField_inner
#print axioms Carleman.firstDerivativeField_inner
#check @Carleman.weakGradientPairing
#print axioms Carleman.weakGradientPairing
#check @Carleman.weakGradientPairing_apply
#print axioms Carleman.weakGradientPairing_apply
#check @Carleman.negativeLaplacian
#print axioms Carleman.negativeLaplacian
#check @Carleman.negativeLaplacian_apply
#print axioms Carleman.negativeLaplacian_apply
#check @Carleman.negativeLaplacian_test
#print axioms Carleman.negativeLaplacian_test
#check @Carleman.negativeLaplacian_dirichlet
#print axioms Carleman.negativeLaplacian_dirichlet
#check @Carleman.dirichletH2Energy
#print axioms Carleman.dirichletH2Energy
#check @Carleman.dirichletH2Energy_value
#print axioms Carleman.dirichletH2Energy_value
#check @Carleman.dirichletH2Energy_green
#print axioms Carleman.dirichletH2Energy_green
#check @Carleman.dirichletH2DomainElement
#print axioms Carleman.dirichletH2DomainElement
#check @Carleman.dirichletH2DomainElement_value
#print axioms Carleman.dirichletH2DomainElement_value
#check @Carleman.dirichletH2DomainElement_operator
#print axioms Carleman.dirichletH2DomainElement_operator
#check @Carleman.h2_dirichlet_le_domain
#print axioms Carleman.h2_dirichlet_le_domain
#check @Carleman.IsWeakNegativeLaplacian
#print axioms Carleman.IsWeakNegativeLaplacian
#check @Carleman.isWeakNegativeLaplacian_iff_dirichlet
#print axioms Carleman.isWeakNegativeLaplacian_iff_dirichlet
#check @Carleman.negativeLaplacian_isWeak
#print axioms Carleman.negativeLaplacian_isWeak
#check @Carleman.dirichletJetEnergy
#print axioms Carleman.dirichletJetEnergy
#check @Carleman.dirichlet_operator_graph_iff
#print axioms Carleman.dirichlet_operator_graph_iff

#check @Carleman.centeredDilation
#print axioms Carleman.centeredDilation
#check @Carleman.centeredDilation_mem
#print axioms Carleman.centeredDilation_mem
#check @Carleman.contractedFunction
#print axioms Carleman.contractedFunction
#check @Carleman.contractedFunction_tsupport
#print axioms Carleman.contractedFunction_tsupport
#check @Carleman.contractedFunction_compact
#print axioms Carleman.contractedFunction_compact
#check @Carleman.contractedFunction_support_inside
#print axioms Carleman.contractedFunction_support_inside
#check @Carleman.contractedFunction_buffer
#print axioms Carleman.contractedFunction_buffer
#check @Carleman.contractedFunction_continuous
#print axioms Carleman.contractedFunction_continuous
#check @Carleman.contractedFunction_hasFDerivAt
#print axioms Carleman.contractedFunction_hasFDerivAt
#check @Carleman.compactLipschitz_fderiv_memLp
#print axioms Carleman.compactLipschitz_fderiv_memLp
#check @Carleman.compactLipschitzDerivativeLp
#print axioms Carleman.compactLipschitzDerivativeLp
#check @Carleman.compactLipschitzDerivativeLp_ae
#print axioms Carleman.compactLipschitzDerivativeLp_ae
#check @Carleman.compactLipschitzLp
#print axioms Carleman.compactLipschitzLp
#check @Carleman.compactLipschitzLp_ae
#print axioms Carleman.compactLipschitzLp_ae
#check @Carleman.compactLipschitzSobolevJet
#print axioms Carleman.compactLipschitzSobolevJet
#check @Carleman.compactLipschitzSobolevJet_value
#print axioms Carleman.compactLipschitzSobolevJet_value
#check @Carleman.centeredDilation_lipschitz
#print axioms Carleman.centeredDilation_lipschitz
#check @Carleman.contractedFunction_lipschitz
#print axioms Carleman.contractedFunction_lipschitz
#check @Carleman.contractedSobolevJet
#print axioms Carleman.contractedSobolevJet
#check @Carleman.contractedSobolevJet_value_ae
#print axioms Carleman.contractedSobolevJet_value_ae
#check @Carleman.SimplicialPartition.nodalFunction_tsupport_subset
#print axioms Carleman.SimplicialPartition.nodalFunction_tsupport_subset
#check @Carleman.SimplicialPartition.nodal_contraction_buffer
#print axioms Carleman.SimplicialPartition.nodal_contraction_buffer
#check @Carleman.SimplicialPartition.nodalContractedSobolevJet
#print axioms Carleman.SimplicialPartition.nodalContractedSobolevJet
#check @Carleman.SimplicialPartition.nodalContractedSobolevJet_value_ae
#print axioms Carleman.SimplicialPartition.nodalContractedSobolevJet_value_ae

#check @Carleman.lp_two_norm_sub_sq_integral
#print axioms Carleman.lp_two_norm_sub_sq_integral
#check @Carleman.lp_two_tendsto_of_dominated_norm_sq
#print axioms Carleman.lp_two_tendsto_of_dominated_norm_sq
#check @Carleman.lp_two_tendsto_of_bounded_support
#print axioms Carleman.lp_two_tendsto_of_bounded_support
#check @Carleman.firstOrderFields_tendsto
#print axioms Carleman.firstOrderFields_tendsto
#check @Carleman.compactLipschitzSobolevJet_tendsto
#print axioms Carleman.compactLipschitzSobolevJet_tendsto
#check @Carleman.inwardRatio
#print axioms Carleman.inwardRatio
#check @Carleman.inwardRatio_pos
#print axioms Carleman.inwardRatio_pos
#check @Carleman.inwardRatio_lt_one
#print axioms Carleman.inwardRatio_lt_one
#check @Carleman.inwardRatio_half_le
#print axioms Carleman.inwardRatio_half_le
#check @Carleman.inwardRatio_inv_le_two
#print axioms Carleman.inwardRatio_inv_le_two
#check @Carleman.inwardRatio_tendsto
#print axioms Carleman.inwardRatio_tendsto
#check @Carleman.inverse_inward_tendsto
#print axioms Carleman.inverse_inward_tendsto
#check @Carleman.inwardFunction_tendsto
#print axioms Carleman.inwardFunction_tendsto
#check @Carleman.inward_fderiv_tendsto_of_local_affine
#print axioms Carleman.inward_fderiv_tendsto_of_local_affine
#check @Carleman.SimplicialPartition.nodal_inward_fderiv_tendsto_ae
#print axioms Carleman.SimplicialPartition.nodal_inward_fderiv_tendsto_ae
#check @Carleman.SimplicialPartition.closure_isCompact
#print axioms Carleman.SimplicialPartition.closure_isCompact
#check @Carleman.SimplicialPartition.nodalCompactJet_eq
#print axioms Carleman.SimplicialPartition.nodalCompactJet_eq
#check @Carleman.SimplicialPartition.nodal_inward_tendsto_H1
#print axioms Carleman.SimplicialPartition.nodal_inward_tendsto_H1

#check @Carleman.SpatialTest.convolution_norm_bound
#print axioms Carleman.SpatialTest.convolution_norm_bound
#check @Carleman.SpatialTest.convolution_lipschitz
#print axioms Carleman.SpatialTest.convolution_lipschitz
#check @Carleman.SpatialTest.convolution_tsupport_subset_thickening
#print axioms Carleman.SpatialTest.convolution_tsupport_subset_thickening
#check @Carleman.SpatialTest.convolution_smooth
#print axioms Carleman.SpatialTest.convolution_smooth
#check @Carleman.SpatialTest.convolution_compact
#print axioms Carleman.SpatialTest.convolution_compact
#check @Carleman.compactLipschitz_weakDerivative
#print axioms Carleman.compactLipschitz_weakDerivative
#check @Carleman.compactLipschitz_convolution_fderiv
#print axioms Carleman.compactLipschitz_convolution_fderiv
#check @Carleman.shrinkingBump_radius_tendsto
#print axioms Carleman.shrinkingBump_radius_tendsto
#check @Carleman.shrinkingBump_radius_le_two
#print axioms Carleman.shrinkingBump_radius_le_two
#check @Carleman.compactMollification
#print axioms Carleman.compactMollification
#check @Carleman.compactMollification_smooth
#print axioms Carleman.compactMollification_smooth
#check @Carleman.compactMollification_compact
#print axioms Carleman.compactMollification_compact
#check @Carleman.compactMollification_lipschitz
#print axioms Carleman.compactMollification_lipschitz
#check @Carleman.compactMollification_support
#print axioms Carleman.compactMollification_support
#check @Carleman.compactMollification_tendsto
#print axioms Carleman.compactMollification_tendsto
#check @Carleman.compactMollification_fderiv_tendsto
#print axioms Carleman.compactMollification_fderiv_tendsto
#check @Carleman.compactMollification_tendsto_H1
#print axioms Carleman.compactMollification_tendsto_H1
#check @Carleman.SpatialTest.toUniv
#print axioms Carleman.SpatialTest.toUniv
#check @Carleman.IsWeakSpatialDerivative.restrictDomain
#print axioms Carleman.IsWeakSpatialDerivative.restrictDomain
#check @Carleman.derivativeComponent_restrict
#print axioms Carleman.derivativeComponent_restrict
#check @Carleman.WeakSobolevJet.restrictDomain
#print axioms Carleman.WeakSobolevJet.restrictDomain
#check @Carleman.WeakSobolevJet.restrictDomain_value
#print axioms Carleman.WeakSobolevJet.restrictDomain_value
#check @Carleman.WeakSobolevJet.restrictDomain_tendsto
#print axioms Carleman.WeakSobolevJet.restrictDomain_tendsto
#check @Carleman.restrictedJet_eq_test
#print axioms Carleman.restrictedJet_eq_test
#check @Carleman.compactLipschitzSobolevJet_value_ae
#print axioms Carleman.compactLipschitzSobolevJet_value_ae
#check @Carleman.compactLipschitz_mem_dirichletJetSpace
#print axioms Carleman.compactLipschitz_mem_dirichletJetSpace
#check @Carleman.SimplicialPartition.nodal_inward_mem_dirichletJetSpace
#print axioms Carleman.SimplicialPartition.nodal_inward_mem_dirichletJetSpace
#check @Carleman.SimplicialPartition.nodal_global_restrict_mem_dirichletJetSpace
#print axioms Carleman.SimplicialPartition.nodal_global_restrict_mem_dirichletJetSpace
#check @Carleman.SimplicialPartition.nodalLp_mem_dirichletSubspace
#print axioms Carleman.SimplicialPartition.nodalLp_mem_dirichletSubspace
#check @Carleman.SimplicialPartition.nodalLp_mem_dirichletConformingSpace
#print axioms Carleman.SimplicialPartition.nodalLp_mem_dirichletConformingSpace

#check @Carleman.simplexCell_finiteMeasure
#print axioms Carleman.simplexCell_finiteMeasure
#check @Carleman.simplexCell_subset_closure_interior
#print axioms Carleman.simplexCell_subset_closure_interior
#check @Carleman.simplexNodalInterpolant_memLp
#print axioms Carleman.simplexNodalInterpolant_memLp
#check @Carleman.simplexNodalLp
#print axioms Carleman.simplexNodalLp
#check @Carleman.simplexNodalLp_ae
#print axioms Carleman.simplexNodalLp_ae
#check @Carleman.simplexNodalLpLinear
#print axioms Carleman.simplexNodalLpLinear
#check @Carleman.simplexNodalLp_injective
#print axioms Carleman.simplexNodalLp_injective
#check @Carleman.simplexNodalLp_coefficient_bound
#print axioms Carleman.simplexNodalLp_coefficient_bound
#check @Carleman.simplexBarycentricDerivative
#print axioms Carleman.simplexBarycentricDerivative
#check @Carleman.simplexNodalDerivativeLinear
#print axioms Carleman.simplexNodalDerivativeLinear
#check @Carleman.simplexNodalInterpolant_hasFDerivAt
#print axioms Carleman.simplexNodalInterpolant_hasFDerivAt
#check @Carleman.simplexNodalGradientLp
#print axioms Carleman.simplexNodalGradientLp
#check @Carleman.simplexNodalGradientLp_ae
#print axioms Carleman.simplexNodalGradientLp_ae
#check @Carleman.simplexNodalGradientLinear
#print axioms Carleman.simplexNodalGradientLinear
#check @Carleman.simplex_reference_inverse
#print axioms Carleman.simplex_reference_inverse


#check @Carleman.affineChange
#print axioms Carleman.affineChange
#check @Carleman.affineChange_apply
#print axioms Carleman.affineChange_apply
#check @Carleman.affineJacobian
#print axioms Carleman.affineJacobian
#check @Carleman.affineJacobian_pos
#print axioms Carleman.affineJacobian_pos
#check @Carleman.affineChange_map_volume
#print axioms Carleman.affineChange_map_volume
#check @Carleman.affineChange_map_restrict
#print axioms Carleman.affineChange_map_restrict
#check @Carleman.integral_comp_affineChange
#print axioms Carleman.integral_comp_affineChange
#check @Carleman.affineChangeEquiv
#print axioms Carleman.affineChangeEquiv
#check @Carleman.affineChangeEquiv_apply
#print axioms Carleman.affineChangeEquiv_apply
#check @Carleman.affineSimplex
#print axioms Carleman.affineSimplex
#check @Carleman.affineSimplex_points
#print axioms Carleman.affineSimplex_points
#check @Carleman.affineSimplex_cell
#print axioms Carleman.affineSimplex_cell
#check @Carleman.affineSimplex_nodal_comp
#print axioms Carleman.affineSimplex_nodal_comp
#check @Carleman.affineSimplex_derivative_comp
#print axioms Carleman.affineSimplex_derivative_comp
#check @Carleman.affineSimplex_derivative
#print axioms Carleman.affineSimplex_derivative
#check @Carleman.derivativeOneFiber_injective
#print axioms Carleman.derivativeOneFiber_injective
#check @Carleman.derivativeOneFiber_reverse_bound
#print axioms Carleman.derivativeOneFiber_reverse_bound
#check @Carleman.derivativeOneFiber_comp_bound
#print axioms Carleman.derivativeOneFiber_comp_bound
#check @Carleman.lp_two_norm_sq_integral
#print axioms Carleman.lp_two_norm_sq_integral
#check @Carleman.simplexNodalLp_norm_sq
#print axioms Carleman.simplexNodalLp_norm_sq
#check @Carleman.simplexNodalGradientLp_norm_sq
#print axioms Carleman.simplexNodalGradientLp_norm_sq
#check @Carleman.affineSimplex_nodal_norm_sq
#print axioms Carleman.affineSimplex_nodal_norm_sq
#check @Carleman.affineSimplex_gradient_norm_sq
#print axioms Carleman.affineSimplex_gradient_norm_sq
#check @Carleman.affineSimplex_gradient_bound_sq
#print axioms Carleman.affineSimplex_gradient_bound_sq
#check @Carleman.affineSimplex_inverse
#print axioms Carleman.affineSimplex_inverse
#check @Carleman.affineSimplex_inverse_uniform
#print axioms Carleman.affineSimplex_inverse_uniform
#check @Carleman.affineSimplex_inverse_map_bound
#print axioms Carleman.affineSimplex_inverse_map_bound
#check @Carleman.affineSimplex_shape_inverse
#print axioms Carleman.affineSimplex_shape_inverse


#check @Carleman.simplexCoordinateLinearEquiv
#print axioms Carleman.simplexCoordinateLinearEquiv
#check @Carleman.simplexCoordinateLinearEquiv_sub
#print axioms Carleman.simplexCoordinateLinearEquiv_sub
#check @Carleman.simplexCoordinateShift
#print axioms Carleman.simplexCoordinateShift
#check @Carleman.affineSimplex_coordinate_eq
#print axioms Carleman.affineSimplex_coordinate_eq
#check @Carleman.referenceSimplex
#print axioms Carleman.referenceSimplex
#check @Carleman.simplex_shape_inverse
#print axioms Carleman.simplex_shape_inverse
#check @Carleman.simplex_weighted_shape_inverse
#print axioms Carleman.simplex_weighted_shape_inverse
#check @Carleman.simplex_local_weighted_inverse
#print axioms Carleman.simplex_local_weighted_inverse
#check @Carleman.simplexNodalLp_weighted_sq
#print axioms Carleman.simplexNodalLp_weighted_sq
#check @Carleman.simplexNodalGradientLp_weighted_sq
#print axioms Carleman.simplexNodalGradientLp_weighted_sq
#check @Carleman.simplex_weighted_inverse_integral
#print axioms Carleman.simplex_weighted_inverse_integral


#check @Carleman.subdomainLp
#print axioms Carleman.subdomainLp
#check @Carleman.subdomainLp_ae
#print axioms Carleman.subdomainLp_ae
#check @Carleman.SpatialTest.monoDomain
#print axioms Carleman.SpatialTest.monoDomain
#check @Carleman.IsWeakSpatialDerivative.restrictSubdomain
#print axioms Carleman.IsWeakSpatialDerivative.restrictSubdomain
#check @Carleman.derivativeComponent_subdomain
#print axioms Carleman.derivativeComponent_subdomain
#check @Carleman.WeakSobolevJet.restrictSubdomain
#print axioms Carleman.WeakSobolevJet.restrictSubdomain
#check @Carleman.WeakSobolevJet.restrictSubdomain_value
#print axioms Carleman.WeakSobolevJet.restrictSubdomain_value
#check @Carleman.affineScalarDerivative
#print axioms Carleman.affineScalarDerivative
#check @Carleman.affineScalar_hasFDerivAt
#print axioms Carleman.affineScalar_hasFDerivAt
#check @Carleman.affineScalar_lipschitz
#print axioms Carleman.affineScalar_lipschitz
#check @Carleman.weakDerivative_eq_affine
#print axioms Carleman.weakDerivative_eq_affine
#check @Carleman.WeakSobolevJet.gradient_eq_affine
#print axioms Carleman.WeakSobolevJet.gradient_eq_affine
#check @Carleman.simplexCell_ae_interior
#print axioms Carleman.simplexCell_ae_interior
#check @Carleman.simplexInterior_finiteMeasure
#print axioms Carleman.simplexInterior_finiteMeasure
#check @Carleman.SimplicialPartition.cell_interior_subset
#print axioms Carleman.SimplicialPartition.cell_interior_subset
#check @Carleman.SimplicialPartition.cell_measure_le_domain
#print axioms Carleman.SimplicialPartition.cell_measure_le_domain
#check @Carleman.SimplicialPartition.gradient_on_cell
#print axioms Carleman.SimplicialPartition.gradient_on_cell
#check @Carleman.affinePolynomialOfCoefficients
#print axioms Carleman.affinePolynomialOfCoefficients
#check @Carleman.affinePolynomialOfCoefficients_apply
#print axioms Carleman.affinePolynomialOfCoefficients_apply
#check @Carleman.SimplicialPartition.conforming_local_polynomial
#print axioms Carleman.SimplicialPartition.conforming_local_polynomial


#check @Carleman.SimplicialPartition.cell_restrict_domain
#print axioms Carleman.SimplicialPartition.cell_restrict_domain
#check @Carleman.SimplicialPartition.integral_eq_sum_cells
#print axioms Carleman.SimplicialPartition.integral_eq_sum_cells
#check @Carleman.SimplicialPartition.inverseScale
#print axioms Carleman.SimplicialPartition.inverseScale
#check @Carleman.SimplicialPartition.inverseScale_on_cell
#print axioms Carleman.SimplicialPartition.inverseScale_on_cell
#check @Carleman.SimplicialPartition.inverseWeight
#print axioms Carleman.SimplicialPartition.inverseWeight
#check @Carleman.SimplicialPartition.inverseWeight_on_cell
#print axioms Carleman.SimplicialPartition.inverseWeight_on_cell
#check @Carleman.SimplicialPartition.inverseWeight_sq_sum
#print axioms Carleman.SimplicialPartition.inverseWeight_sq_sum
#check @Carleman.conforming_weighted_inverse
#print axioms Carleman.conforming_weighted_inverse

#check @Carleman.uniqueDiffOn_closure_open_convex
#print axioms Carleman.uniqueDiffOn_closure_open_convex
#check @Carleman.smooth_profile_lipschitz
#print axioms Carleman.smooth_profile_lipschitz
#check @Carleman.allowedWeight_spatial_ratio
#print axioms Carleman.allowedWeight_spatial_ratio
#check @Carleman.allowedWeight_spatial_comparison
#print axioms Carleman.allowedWeight_spatial_comparison
#check @Carleman.SpatialProfile.scaled
#print axioms Carleman.SpatialProfile.scaled
#check @Carleman.SpatialProfile.scaled_multiplier_value
#print axioms Carleman.SpatialProfile.scaled_multiplier_value
#check @Carleman.SpatialProfile.scaled_one
#print axioms Carleman.SpatialProfile.scaled_one
#check @Carleman.SpatialProfile.scaled_neg_one
#print axioms Carleman.SpatialProfile.scaled_neg_one
#check @Carleman.SpatialProfile.scaled_multiplier_pos
#print axioms Carleman.SpatialProfile.scaled_multiplier_pos
#check @Carleman.SpatialProfile.scaled_multiplier_spatial_le
#print axioms Carleman.SpatialProfile.scaled_multiplier_spatial_le
#check @Carleman.SimplicialPartition.cellDiameter
#print axioms Carleman.SimplicialPartition.cellDiameter
#check @Carleman.SimplicialPartition.cellDiameter_nonneg
#print axioms Carleman.SimplicialPartition.cellDiameter_nonneg
#check @Carleman.SimplicialPartition.dist_le_cellDiameter
#print axioms Carleman.SimplicialPartition.dist_le_cellDiameter
#check @Carleman.SimplicialPartition.maxDiameter
#print axioms Carleman.SimplicialPartition.maxDiameter
#check @Carleman.SimplicialPartition.maxDiameter_nonneg
#print axioms Carleman.SimplicialPartition.maxDiameter_nonneg
#check @Carleman.SimplicialPartition.cellDiameter_le_max
#print axioms Carleman.SimplicialPartition.cellDiameter_le_max
#check @Carleman.SimplicialPartition.cellScale_le_inball
#print axioms Carleman.SimplicialPartition.cellScale_le_inball
#check @Carleman.SimplicialPartition.maxDiameter_mul_q_le
#print axioms Carleman.SimplicialPartition.maxDiameter_mul_q_le
#check @Carleman.SimplicialPartition.allowedWeight_cell_comparison
#print axioms Carleman.SimplicialPartition.allowedWeight_cell_comparison
#check @Carleman.conforming_allowed_weight_inverse
#print axioms Carleman.conforming_allowed_weight_inverse

#check @Carleman.SimplicialPartition.VertexNeighbors
#print axioms Carleman.SimplicialPartition.VertexNeighbors
#check @Carleman.SimplicialPartition.VertexNeighbors.symm
#print axioms Carleman.SimplicialPartition.VertexNeighbors.symm
#check @Carleman.SimplicialPartition.vertexNeighbors_dist_le
#print axioms Carleman.SimplicialPartition.vertexNeighbors_dist_le
#check @Carleman.SimplicialPartition.vertexNeighbors_dist_le_max
#print axioms Carleman.SimplicialPartition.vertexNeighbors_dist_le_max
#check @Carleman.exists_weight_grading_threshold
#print axioms Carleman.exists_weight_grading_threshold
#check @Carleman.SpatialProfile.scaled_multiplier_inverse_value
#print axioms Carleman.SpatialProfile.scaled_multiplier_inverse_value
#check @Carleman.SimplicialPartition.scale_grading_from_ratios
#print axioms Carleman.SimplicialPartition.scale_grading_from_ratios
#check @Carleman.SimplicialPartition.allowedWeight_neighbor_le
#print axioms Carleman.SimplicialPartition.allowedWeight_neighbor_le
#check @Carleman.SimplicialPartition.gradedWeight
#print axioms Carleman.SimplicialPartition.gradedWeight
#check @Carleman.SimplicialPartition.gradedWeight_on_cell
#print axioms Carleman.SimplicialPartition.gradedWeight_on_cell
#check @Carleman.SimplicialPartition.gradedWeight_neighbor_le
#print axioms Carleman.SimplicialPartition.gradedWeight_neighbor_le
#check @Carleman.p1GradingLimit
#print axioms Carleman.p1GradingLimit
#check @Carleman.p1GradingLimit_gt_one
#print axioms Carleman.p1GradingLimit_gt_one
#check @Carleman.p1GradingLimit_two
#print axioms Carleman.p1GradingLimit_two
#check @Carleman.p1GradingLimit_three
#print axioms Carleman.p1GradingLimit_three
#check @Carleman.allowed_weights_uniform_neighbor_grading
#print axioms Carleman.allowed_weights_uniform_neighbor_grading

#check @Carleman.p1MassMargin
#print axioms Carleman.p1MassMargin
#check @Carleman.p1MassMargin_pos
#print axioms Carleman.p1MassMargin_pos
#check @Carleman.weight_deviation_bound
#print axioms Carleman.weight_deviation_bound
#check @Carleman.p1CoefficientForm
#print axioms Carleman.p1CoefficientForm
#check @Carleman.p1CoefficientForm_smul_right
#print axioms Carleman.p1CoefficientForm_smul_right
#check @Carleman.weighted_coefficient_deviation
#print axioms Carleman.weighted_coefficient_deviation
#check @Carleman.weighted_p1_coefficient_coercive
#print axioms Carleman.weighted_p1_coefficient_coercive
#check @Carleman.weighted_p1_coefficient_coercive_scaled
#print axioms Carleman.weighted_p1_coefficient_coercive_scaled
#check @Carleman.weighted_p1_coefficient_form_pos
#print axioms Carleman.weighted_p1_coefficient_form_pos

#check @Carleman.mem_simplexCell_iff_barycentric
#print axioms Carleman.mem_simplexCell_iff_barycentric
#check @Carleman.simplexBarycentric_homothety
#print axioms Carleman.simplexBarycentric_homothety
#check @Carleman.simplexBarycentric_superlevel_image
#print axioms Carleman.simplexBarycentric_superlevel_image
#check @Carleman.simplexBarycentric_superlevel_volume
#print axioms Carleman.simplexBarycentric_superlevel_volume
#check @Carleman.simplexBarycentric_superlevel_real
#print axioms Carleman.simplexBarycentric_superlevel_real
#check @Carleman.simplexBarycentric_le_one
#print axioms Carleman.simplexBarycentric_le_one
#check @Carleman.integral_simplexBarycentric
#print axioms Carleman.integral_simplexBarycentric

#check @Carleman.integral_sq_eq_tail
#print axioms Carleman.integral_sq_eq_tail
#check @Carleman.integral_unit_tail_power
#print axioms Carleman.integral_unit_tail_power
#check @Carleman.integral_simplexBarycentric_sq
#print axioms Carleman.integral_simplexBarycentric_sq
#check @Carleman.simplexPermutationLinear
#print axioms Carleman.simplexPermutationLinear
#check @Carleman.simplexPermutationShift
#print axioms Carleman.simplexPermutationShift
#check @Carleman.simplexPermutation_vertex
#print axioms Carleman.simplexPermutation_vertex
#check @Carleman.simplexPermutation_cell
#print axioms Carleman.simplexPermutation_cell
#check @Carleman.simplexPermutation_barycentric
#print axioms Carleman.simplexPermutation_barycentric
#check @Carleman.simplexPermutation_jacobian
#print axioms Carleman.simplexPermutation_jacobian
#check @Carleman.integral_comp_simplexPermutation
#print axioms Carleman.integral_comp_simplexPermutation
#check @Carleman.integral_simplexBarycentric_mul_permutation
#print axioms Carleman.integral_simplexBarycentric_mul_permutation
#check @Carleman.integral_simplexBarycentric_mul_offdiag
#print axioms Carleman.integral_simplexBarycentric_mul_offdiag
#check @Carleman.integral_simplexBarycentric_mul
#print axioms Carleman.integral_simplexBarycentric_mul
#check @Carleman.p1CoefficientForm_sum
#print axioms Carleman.p1CoefficientForm_sum
#check @Carleman.integral_simplexNodalInterpolant_mul
#print axioms Carleman.integral_simplexNodalInterpolant_mul
#check @Carleman.simplex_mass_factor_pos
#print axioms Carleman.simplex_mass_factor_pos
#check @Carleman.integral_simplexNodalInterpolant_sq_bounds
#print axioms Carleman.integral_simplexNodalInterpolant_sq_bounds
#check @Carleman.weighted_simplex_mass_coercive
#print axioms Carleman.weighted_simplex_mass_coercive
#check @Carleman.weighted_simplex_mass_pos
#print axioms Carleman.weighted_simplex_mass_pos

#check @Carleman.SimplicialPartition.incidentCells
#print axioms Carleman.SimplicialPartition.incidentCells
#check @Carleman.SimplicialPartition.mem_incidentCells
#print axioms Carleman.SimplicialPartition.mem_incidentCells
#check @Carleman.SimplicialPartition.nodalWeightMinimum
#print axioms Carleman.SimplicialPartition.nodalWeightMinimum
#check @Carleman.SimplicialPartition.nodalWeightMinimum_pos
#print axioms Carleman.SimplicialPartition.nodalWeightMinimum_pos
#check @Carleman.SimplicialPartition.nodalWeightMinimum_vertex_bounds
#print axioms Carleman.SimplicialPartition.nodalWeightMinimum_vertex_bounds
#check @Carleman.SimplicialPartition.nodalWeightMinimum_local_ratio
#print axioms Carleman.SimplicialPartition.nodalWeightMinimum_local_ratio
#check @Carleman.SimplicialPartition.gradedCellWeight
#print axioms Carleman.SimplicialPartition.gradedCellWeight
#check @Carleman.SimplicialPartition.gradedCellWeight_pos
#print axioms Carleman.SimplicialPartition.gradedCellWeight_pos
#check @Carleman.SimplicialPartition.allowedWeight_scaled_neighbor_le
#print axioms Carleman.SimplicialPartition.allowedWeight_scaled_neighbor_le
#check @Carleman.SimplicialPartition.sizeWeightFactor_grading
#print axioms Carleman.SimplicialPartition.sizeWeightFactor_grading
#check @Carleman.SimplicialPartition.gradedCellWeight_neighbor_le
#print axioms Carleman.SimplicialPartition.gradedCellWeight_neighbor_le
#check @Carleman.SimplicialPartition.gradedCellWeight_compare
#print axioms Carleman.SimplicialPartition.gradedCellWeight_compare
#check @Carleman.allowed_weights_uniform_nodal_weights
#print axioms Carleman.allowed_weights_uniform_nodal_weights
#check @Carleman.SimplicialPartition.nodal_squared_weight_test_mem
#print axioms Carleman.SimplicialPartition.nodal_squared_weight_test_mem
#check @Carleman.SimplicialPartition.nodal_weighted_mass_coercive
#print axioms Carleman.SimplicialPartition.nodal_weighted_mass_coercive
#check @Carleman.SimplicialPartition.nodal_weighted_pairing_coercive
#print axioms Carleman.SimplicialPartition.nodal_weighted_pairing_coercive

#check @Carleman.weighted_simplexNodal_integrable
#print axioms Carleman.weighted_simplexNodal_integrable
#check @Carleman.weighted_simplexNodal_coefficient_bound
#print axioms Carleman.weighted_simplexNodal_coefficient_bound
#check @Carleman.weighted_simplex_state_bound
#print axioms Carleman.weighted_simplex_state_bound
#check @Carleman.weighted_simplex_test_bound
#print axioms Carleman.weighted_simplex_test_bound
#check @Carleman.SimplicialPartition.nodalCoefficientEnergy
#print axioms Carleman.SimplicialPartition.nodalCoefficientEnergy
#check @Carleman.SimplicialPartition.nodalCoefficientEnergy_nonneg
#print axioms Carleman.SimplicialPartition.nodalCoefficientEnergy_nonneg
#check @Carleman.SimplicialPartition.ae_of_cells
#print axioms Carleman.SimplicialPartition.ae_of_cells
#check @Carleman.SimplicialPartition.nodal_weighted_norm_sq_sum
#print axioms Carleman.SimplicialPartition.nodal_weighted_norm_sq_sum
#check @Carleman.SimplicialPartition.nodal_weighted_state_bound
#print axioms Carleman.SimplicialPartition.nodal_weighted_state_bound
#check @Carleman.SimplicialPartition.nodal_weighted_test_bound
#print axioms Carleman.SimplicialPartition.nodal_weighted_test_bound
#check @Carleman.BoundedMultiplier.inner_le_weighted_pair
#print axioms Carleman.BoundedMultiplier.inner_le_weighted_pair
#check @Carleman.weighted_mass_norm_absorption
#print axioms Carleman.weighted_mass_norm_absorption
#check @Carleman.SimplicialPartition.weighted_projection_bound_of_nodal_representation
#print axioms Carleman.SimplicialPartition.weighted_projection_bound_of_nodal_representation
#check @Carleman.SimplicialPartition.gradedReciprocalWeight
#print axioms Carleman.SimplicialPartition.gradedReciprocalWeight
#check @Carleman.SimplicialPartition.gradedReciprocalWeight_product_cell
#print axioms Carleman.SimplicialPartition.gradedReciprocalWeight_product_cell
#check @Carleman.SimplicialPartition.gradedReciprocalWeight_product
#print axioms Carleman.SimplicialPartition.gradedReciprocalWeight_product
#check @Carleman.SimplicialPartition.gradedReciprocalWeight_cell_bound
#print axioms Carleman.SimplicialPartition.gradedReciprocalWeight_cell_bound
#check @Carleman.allowed_weight_projection_of_nodal_representation
#print axioms Carleman.allowed_weight_projection_of_nodal_representation

#check @Carleman.SpatialTest.dirichlet_full_test_pairing
#print axioms Carleman.SpatialTest.dirichlet_full_test_pairing
#check @Carleman.dirichlet_full_test_pairing
#print axioms Carleman.dirichlet_full_test_pairing
#check @Carleman.dirichlet_zeroExtend_weak_derivative
#print axioms Carleman.dirichlet_zeroExtend_weak_derivative
#check @Carleman.derivativeComponent_zeroExtend
#print axioms Carleman.derivativeComponent_zeroExtend
#check @Carleman.WeakSobolevJet.zeroExtendDirichlet
#print axioms Carleman.WeakSobolevJet.zeroExtendDirichlet
#check @Carleman.WeakSobolevJet.zeroExtendDirichlet_value
#print axioms Carleman.WeakSobolevJet.zeroExtendDirichlet_value
#check @Carleman.WeakSobolevJet.zeroExtendDirichlet_field_norm
#print axioms Carleman.WeakSobolevJet.zeroExtendDirichlet_field_norm
#check @Carleman.WeakSobolevJet.zeroExtendDirichlet_restrict
#print axioms Carleman.WeakSobolevJet.zeroExtendDirichlet_restrict

#check @Carleman.SpatialTest.convolution_ae_norm_bound
#print axioms Carleman.SpatialTest.convolution_ae_norm_bound
#check @Carleman.spatialLinearMap_norm_of_basis_bound
#print axioms Carleman.spatialLinearMap_norm_of_basis_bound
#check @Carleman.convolution_lipschitz_of_bounded_weak_derivatives
#print axioms Carleman.convolution_lipschitz_of_bounded_weak_derivatives
#check @Carleman.exists_lipschitzRepresentative_of_bounded_weak_derivatives
#print axioms Carleman.exists_lipschitzRepresentative_of_bounded_weak_derivatives
#check @Carleman.SimplicialPartition.conforming_gradient_bounded
#print axioms Carleman.SimplicialPartition.conforming_gradient_bounded
#check @Carleman.SimplicialPartition.conforming_dirichlet_lipschitz_representative
#print axioms Carleman.SimplicialPartition.conforming_dirichlet_lipschitz_representative
#check @Carleman.continuous_zeroExtend_zero_compl
#print axioms Carleman.continuous_zeroExtend_zero_compl
#check @Carleman.SimplicialPartition.conforming_representative_affine_on_cells
#print axioms Carleman.SimplicialPartition.conforming_representative_affine_on_cells
#check @Carleman.SimplicialPartition.conforming_dirichlet_nodal_representation
#print axioms Carleman.SimplicialPartition.conforming_dirichlet_nodal_representation
#check @Carleman.allowed_weight_full_projection
#print axioms Carleman.allowed_weight_full_projection

#check @Carleman.affineScalarDerivative_inball_bound
#print axioms Carleman.affineScalarDerivative_inball_bound
#check @Carleman.simplexNodalInterpolant_sub_affine
#print axioms Carleman.simplexNodalInterpolant_sub_affine
#check @Carleman.simplexNodal_error_of_affine_approximation
#print axioms Carleman.simplexNodal_error_of_affine_approximation
#check @Carleman.simplexNodal_derivative_error_of_affine_approximation
#print axioms Carleman.simplexNodal_derivative_error_of_affine_approximation
#check @Carleman.affineFirstOrder
#print axioms Carleman.affineFirstOrder
#check @Carleman.affineFirstOrder_apply
#print axioms Carleman.affineFirstOrder_apply
#check @Carleman.affineFirstOrder_derivative
#print axioms Carleman.affineFirstOrder_derivative
#check @Carleman.affineFirstOrder_remainder
#print axioms Carleman.affineFirstOrder_remainder
#check @Carleman.simplexNodal_error_of_lipschitz_derivative
#print axioms Carleman.simplexNodal_error_of_lipschitz_derivative
#check @Carleman.simplexNodal_gradient_error_of_lipschitz_derivative
#print axioms Carleman.simplexNodal_gradient_error_of_lipschitz_derivative
#check @Carleman.simplexNodal_error_sq_integral
#print axioms Carleman.simplexNodal_error_sq_integral
#check @Carleman.simplexNodal_gradient_error_sq_integral
#print axioms Carleman.simplexNodal_gradient_error_sq_integral
#check @Carleman.derivative_lipschitzOn_of_second_derivative_bound
#print axioms Carleman.derivative_lipschitzOn_of_second_derivative_bound

#check @Carleman.affineJetPolynomial
#print axioms Carleman.affineJetPolynomial
#check @Carleman.affineJetPolynomial_apply
#print axioms Carleman.affineJetPolynomial_apply
#check @Carleman.affineJetPolynomial_derivative
#print axioms Carleman.affineJetPolynomial_derivative
#check @Carleman.withinFirstOrder_remainder
#print axioms Carleman.withinFirstOrder_remainder
#check @Carleman.simplexNodal_within_value_error
#print axioms Carleman.simplexNodal_within_value_error
#check @Carleman.simplexNodal_within_gradient_error
#print axioms Carleman.simplexNodal_within_gradient_error
#check @Carleman.affineProductDerivative
#print axioms Carleman.affineProductDerivative
#check @Carleman.affineProduct_hasFDerivWithinAt
#print axioms Carleman.affineProduct_hasFDerivWithinAt
#check @Carleman.affineProductDerivative_lipschitzOn
#print axioms Carleman.affineProductDerivative_lipschitzOn
#check @Carleman.affineProduct_nodal_value_error
#print axioms Carleman.affineProduct_nodal_value_error
#check @Carleman.affineProduct_nodal_gradient_error
#print axioms Carleman.affineProduct_nodal_gradient_error
#check @Carleman.affineProduct_derivative_interior
#print axioms Carleman.affineProduct_derivative_interior
#check @Carleman.derivativeField_lipschitzOn_of_within_bound
#print axioms Carleman.derivativeField_lipschitzOn_of_within_bound

#check @Carleman.allowedSquaredWeight
#print axioms Carleman.allowedSquaredWeight
#check @Carleman.allowedSquaredWeight_eq
#print axioms Carleman.allowedSquaredWeight_eq
#check @Carleman.allowedSquaredWeight_contDiffOn
#print axioms Carleman.allowedSquaredWeight_contDiffOn
#check @Carleman.allowedSquaredWeight_hasFDerivWithinAt
#print axioms Carleman.allowedSquaredWeight_hasFDerivWithinAt
#check @Carleman.allowedSquaredWeight_secondWithin
#print axioms Carleman.allowedSquaredWeight_secondWithin
#check @Carleman.allowedSquaredWeight_within_derivatives_uniform
#print axioms Carleman.allowedSquaredWeight_within_derivatives_uniform
#check @Carleman.allowedSquaredWeight_cell_le
#print axioms Carleman.allowedSquaredWeight_cell_le
#check @Carleman.allowedSquaredWeight_local_derivative_data
#print axioms Carleman.allowedSquaredWeight_local_derivative_data
#check @Carleman.allowedSquaredWeight_multiplier_value
#print axioms Carleman.allowedSquaredWeight_multiplier_value
#check @Carleman.allowedSquaredWeight_product_errors
#print axioms Carleman.allowedSquaredWeight_product_errors

#check @Carleman.affineNodalBound
#print axioms Carleman.affineNodalBound
#check @Carleman.affineNodalBound_abs
#print axioms Carleman.affineNodalBound_abs
#check @Carleman.affineNodalBound_sq_mass
#print axioms Carleman.affineNodalBound_sq_mass
#check @Carleman.affineNodalBound_energy
#print axioms Carleman.affineNodalBound_energy
#check @Carleman.norm_sq_div_integral_le
#print axioms Carleman.norm_sq_div_integral_le
#check @Carleman.affineNodalBound_weighted_energy
#print axioms Carleman.affineNodalBound_weighted_energy
#check @Carleman.weighted_cell_error_transfer
#print axioms Carleman.weighted_cell_error_transfer
#check @Carleman.allowedSquaredWeight_local_integral_errors
#print axioms Carleman.allowedSquaredWeight_local_integral_errors
#check @Carleman.squaredNodalResidual_fderiv_ae
#print axioms Carleman.squaredNodalResidual_fderiv_ae
#check @Carleman.allowedSquaredWeight_local_residual_integrals
#print axioms Carleman.allowedSquaredWeight_local_residual_integrals

#check @Carleman.SimplicialPartition.integrable_of_cells
#print axioms Carleman.SimplicialPartition.integrable_of_cells
#check @Carleman.SimplicialPartition.nodalProductResidual
#print axioms Carleman.SimplicialPartition.nodalProductResidual
#check @Carleman.SimplicialPartition.localNodal_weighted_interpolant
#print axioms Carleman.SimplicialPartition.localNodal_weighted_interpolant
#check @Carleman.SimplicialPartition.nodalProductResidual_on_cell
#print axioms Carleman.SimplicialPartition.nodalProductResidual_on_cell
#check @Carleman.SimplicialPartition.nodalProductResidual_fderiv_ae
#print axioms Carleman.SimplicialPartition.nodalProductResidual_fderiv_ae
#check @Carleman.SimplicialPartition.nodalFunction_fderiv_on_cell_ae
#print axioms Carleman.SimplicialPartition.nodalFunction_fderiv_on_cell_ae
#check @Carleman.SimplicialPartition.squaredNodal_integrability
#print axioms Carleman.SimplicialPartition.squaredNodal_integrability
#check @Carleman.allowedSquaredWeight_nodal_cell_integrals
#print axioms Carleman.allowedSquaredWeight_nodal_cell_integrals
#check @Carleman.allowedSquaredWeight_nodal_global_integrals
#print axioms Carleman.allowedSquaredWeight_nodal_global_integrals
#check @Carleman.SimplicialPartition.nodal_representation_weak_gradient
#print axioms Carleman.SimplicialPartition.nodal_representation_weak_gradient
#check @Carleman.SimplicialPartition.conforming_dirichlet_nodal_with_gradient
#print axioms Carleman.SimplicialPartition.conforming_dirichlet_nodal_with_gradient
#check @Carleman.SimplicialPartition.weighted_nodal_mem_dirichletConformingSpace
#print axioms Carleman.SimplicialPartition.weighted_nodal_mem_dirichletConformingSpace
#check @Carleman.allowedSquaredWeight_full_nodal_residual
#print axioms Carleman.allowedSquaredWeight_full_nodal_residual

#check @Carleman.supported_lipschitz_product
#print axioms Carleman.supported_lipschitz_product
#check @Carleman.SimplicialPartition.squared_nodal_product_lipschitz
#print axioms Carleman.SimplicialPartition.squared_nodal_product_lipschitz
#check @Carleman.compactLipschitz_restricted_jet_exists
#print axioms Carleman.compactLipschitz_restricted_jet_exists
#check @Carleman.SimplicialPartition.squared_nodal_residual_weak_jet
#print axioms Carleman.SimplicialPartition.squared_nodal_residual_weak_jet
#check @Carleman.allowedSquaredWeight_full_weak_residual
#print axioms Carleman.allowedSquaredWeight_full_weak_residual
#check @Carleman.SimplicialPartition.nodalProductResidual_lp
#print axioms Carleman.SimplicialPartition.nodalProductResidual_lp
#check @Carleman.allowed_weight_sq_integral
#print axioms Carleman.allowed_weight_sq_integral
#check @Carleman.allowed_inverse_weight_sq_integral
#print axioms Carleman.allowed_inverse_weight_sq_integral
#check @Carleman.allowed_full_nodal_weak_norms
#print axioms Carleman.allowed_full_nodal_weak_norms

#check @Carleman.inverseScale_diameter_four_bound
#print axioms Carleman.inverseScale_diameter_four_bound
#check @Carleman.SimplicialPartition.inverseWeight_residual_sq_sum
#print axioms Carleman.SimplicialPartition.inverseWeight_residual_sq_sum
#check @Carleman.allowed_scaled_nodal_residual
#print axioms Carleman.allowed_scaled_nodal_residual
#check @Carleman.allowed_full_nodal_scaled_norms
#print axioms Carleman.allowed_full_nodal_scaled_norms
#check @Carleman.WeakSobolevJet.heat_weightedNorm_sq
#print axioms Carleman.WeakSobolevJet.heat_weightedNorm_sq
#check @Carleman.nonneg_le_sqrt_mul_of_sq_le
#print axioms Carleman.nonneg_le_sqrt_mul_of_sq_le
#check @Carleman.allowed_full_nodal_superapproximation
#print axioms Carleman.allowed_full_nodal_superapproximation

#check @Carleman.WeakSobolevJet.heat_weightedNorm_le_fields
#print axioms Carleman.WeakSobolevJet.heat_weightedNorm_le_fields
#check @Carleman.projection_error_of_residual
#print axioms Carleman.projection_error_of_residual
#check @Carleman.weak_projected_residual_estimate
#print axioms Carleman.weak_projected_residual_estimate
#check @Carleman.allowed_full_projected_superapproximation
#print axioms Carleman.allowed_full_projected_superapproximation
#check @Carleman.SpatialProfile.scaled_neg
#print axioms Carleman.SpatialProfile.scaled_neg
#check @Carleman.full_p1_galerkin_superapproximation
#print axioms Carleman.full_p1_galerkin_superapproximation

#check @Carleman.firstDerivativeInjection
#print axioms Carleman.firstDerivativeInjection
#check @Carleman.firstDerivativeInjection_component
#print axioms Carleman.firstDerivativeInjection_component
#check @Carleman.firstGradientAssembly
#print axioms Carleman.firstGradientAssembly
#check @Carleman.firstGradientAssembly_component
#print axioms Carleman.firstGradientAssembly_component
#check @Carleman.firstProductFields
#print axioms Carleman.firstProductFields
#check @Carleman.weakFirstProduct
#print axioms Carleman.weakFirstProduct
#check @Carleman.weakFirstProduct_value
#print axioms Carleman.weakFirstProduct_value
#check @Carleman.weakFirstProductCLM
#print axioms Carleman.weakFirstProductCLM
#check @Carleman.clm_mem_closed_span
#print axioms Carleman.clm_mem_closed_span
#check @Carleman.weakFirstProductCLM_test
#print axioms Carleman.weakFirstProductCLM_test
#check @Carleman.weakFirstProductCLM_mem_dirichlet
#print axioms Carleman.weakFirstProductCLM_mem_dirichlet
#check @Carleman.boundedSmooth_map_mem_dirichlet
#print axioms Carleman.boundedSmooth_map_mem_dirichlet
#check @Carleman.allowed_multiplier_boundedSmooth
#print axioms Carleman.allowed_multiplier_boundedSmooth
#check @Carleman.allowed_weight_mem_dirichlet
#print axioms Carleman.allowed_weight_mem_dirichlet
#check @Carleman.allowed_squared_residual_mem_dirichlet
#print axioms Carleman.allowed_squared_residual_mem_dirichlet

#check @Carleman.weakGradientPairing_coordinates
#print axioms Carleman.weakGradientPairing_coordinates
#check @Carleman.weakFirstProduct_component
#print axioms Carleman.weakFirstProduct_component
#check @Carleman.weak_product_coordinate_test
#print axioms Carleman.weak_product_coordinate_test
#check @Carleman.weakGradientPairing_product_test
#print axioms Carleman.weakGradientPairing_product_test
#check @Carleman.IsWeakNegativeLaplacian.mul
#print axioms Carleman.IsWeakNegativeLaplacian.mul
#check @Carleman.smoothLaplacianCorrection
#print axioms Carleman.smoothLaplacianCorrection
#check @Carleman.boundedSmooth_weakLaplacian_product
#print axioms Carleman.boundedSmooth_weakLaplacian_product
#check @Carleman.boundedSmooth_dirichlet_operator_product
#print axioms Carleman.boundedSmooth_dirichlet_operator_product
#check @Carleman.boundedSmooth_map_mem_dirichlet_domain
#print axioms Carleman.boundedSmooth_map_mem_dirichlet_domain
#check @Carleman.allowed_weight_mem_dirichlet_domain
#print axioms Carleman.allowed_weight_mem_dirichlet_domain

#check @Carleman.derivativeComponent_weighted_norm_le
#print axioms Carleman.derivativeComponent_weighted_norm_le
#check @Carleman.WeakSobolevJet.heat_parameterNorm
#print axioms Carleman.WeakSobolevJet.heat_parameterNorm
#check @Carleman.smoothLaplacianCorrection_norm_le
#print axioms Carleman.smoothLaplacianCorrection_norm_le
#check @Carleman.allowed_laplacian_correction_uniform
#print axioms Carleman.allowed_laplacian_correction_uniform
#check @Carleman.dirichletDomainJet
#print axioms Carleman.dirichletDomainJet
#check @Carleman.dirichletDomainJet_value
#print axioms Carleman.dirichletDomainJet_value
#check @Carleman.dirichletDomainJet_graph
#print axioms Carleman.dirichletDomainJet_graph
#check @Carleman.conformingWeight_operator_of_graph
#print axioms Carleman.conformingWeight_operator_of_graph
#check @Carleman.dirichlet_operator_mul_eq
#print axioms Carleman.dirichlet_operator_mul_eq
#check @Carleman.dirichlet_conjugatedCommutator_eq
#print axioms Carleman.dirichlet_conjugatedCommutator_eq
#check @Carleman.allowed_laplacian_correction_conjugated
#print axioms Carleman.allowed_laplacian_correction_conjugated
#check @Carleman.dirichlet_allowed_commutator_uniform
#print axioms Carleman.dirichlet_allowed_commutator_uniform

#check @Carleman.weakFirstProduct_component_of_value
#print axioms Carleman.weakFirstProduct_component_of_value
#check @Carleman.BoundedMultiplier.map_map_comm
#print axioms Carleman.BoundedMultiplier.map_map_comm
#check @Carleman.weakGradientPairing_mul_twice
#print axioms Carleman.weakGradientPairing_mul_twice
#check @Carleman.weakGradientPairing_weighted_lower
#print axioms Carleman.weakGradientPairing_weighted_lower
#check @Carleman.weakGradientPairing_weighted_upper
#print axioms Carleman.weakGradientPairing_weighted_upper
#check @Carleman.dirichlet_scalarForm_eq
#print axioms Carleman.dirichlet_scalarForm_eq
#check @Carleman.dirichlet_scalarForm_canonical
#print axioms Carleman.dirichlet_scalarForm_canonical
#check @Carleman.allowed_weak_form_lower_uniform
#print axioms Carleman.allowed_weak_form_lower_uniform
#check @Carleman.dirichlet_allowed_form_lower_uniform
#print axioms Carleman.dirichlet_allowed_form_lower_uniform
#check @Carleman.dirichlet_allowed_form_upper
#print axioms Carleman.dirichlet_allowed_form_upper

#check @Carleman.dirichlet_domain_lower_sum
#print axioms Carleman.dirichlet_domain_lower_sum
#check @Carleman.dirichlet_allowed_data_uniform
#print axioms Carleman.dirichlet_allowed_data_uniform
#check @Carleman.dirichlet_allowed_family_uniform
#print axioms Carleman.dirichlet_allowed_family_uniform

#check @Carleman.integral_sq_sub_const
#print axioms Carleman.integral_sq_sub_const
#check @Carleman.integral_pairwise_sq
#print axioms Carleman.integral_pairwise_sq
#check @Carleman.mean_square_pairwise_identity
#print axioms Carleman.mean_square_pairwise_identity
#check @Carleman.integral_comp_scalar_affine
#print axioms Carleman.integral_comp_scalar_affine
#check @Carleman.integral_convex_segment_le
#print axioms Carleman.integral_convex_segment_le
#check @Carleman.smooth_segment_ftc
#print axioms Carleman.smooth_segment_ftc
#check @Carleman.smooth_segment_difference_sq
#print axioms Carleman.smooth_segment_difference_sq
#check @Carleman.convex_half_segment_integral_le
#print axioms Carleman.convex_half_segment_integral_le
#check @Carleman.convex_smooth_midpoint_error
#print axioms Carleman.convex_smooth_midpoint_error
#check @Carleman.convex_smooth_pairwise_bound
#print axioms Carleman.convex_smooth_pairwise_bound
#check @Carleman.convex_smooth_mean_poincare
#print axioms Carleman.convex_smooth_mean_poincare

#check @Carleman.l2_square_bound_of_ae_tendsto
#print axioms Carleman.l2_square_bound_of_ae_tendsto
#check @Carleman.pairwise_memLp
#print axioms Carleman.pairwise_memLp
#check @Carleman.pairwise_integral_congr_ae
#print axioms Carleman.pairwise_integral_congr_ae
#check @Carleman.pairwise_square_bound_of_ae_tendsto
#print axioms Carleman.pairwise_square_bound_of_ae_tendsto
#check @Carleman.l2_square_bound_on_exhaustion
#print axioms Carleman.l2_square_bound_on_exhaustion
#check @Carleman.spatialLinearMap_norm_sq
#print axioms Carleman.spatialLinearMap_norm_sq
#check @Carleman.mollified_gradient_energy_le
#print axioms Carleman.mollified_gradient_energy_le
#check @Carleman.convex_mollified_pairwise_bound
#print axioms Carleman.convex_mollified_pairwise_bound
#check @Carleman.shrinkingBump_rOut_tendsto
#print axioms Carleman.shrinkingBump_rOut_tendsto
#check @Carleman.compact_mollifier_eventually_inside
#print axioms Carleman.compact_mollifier_eventually_inside
#check @Carleman.interior_weak_pairwise_fullLp
#print axioms Carleman.interior_weak_pairwise_fullLp
#check @Carleman.interior_weak_pairwise
#print axioms Carleman.interior_weak_pairwise
#check @Carleman.interior_weak_mean_poincare
#print axioms Carleman.interior_weak_mean_poincare
#check @Carleman.convexInnerCompact
#print axioms Carleman.convexInnerCompact
#check @Carleman.convexInnerCompact_compact
#print axioms Carleman.convexInnerCompact_compact
#check @Carleman.convexInnerCompact_convex
#print axioms Carleman.convexInnerCompact_convex
#check @Carleman.convexInnerCompact_subset
#print axioms Carleman.convexInnerCompact_subset
#check @Carleman.convexInnerCompact_eventually_mem
#print axioms Carleman.convexInnerCompact_eventually_mem
#check @Carleman.convex_weak_pairwise_bound
#print axioms Carleman.convex_weak_pairwise_bound
#check @Carleman.convex_weak_mean_poincare
#print axioms Carleman.convex_weak_mean_poincare
#check @Carleman.convex_weakJet_mean_poincare
#print axioms Carleman.convex_weakJet_mean_poincare

#check @Carleman.scalarLp_norm_sq
#print axioms Carleman.scalarLp_norm_sq
#check @Carleman.scalarConstantLp
#print axioms Carleman.scalarConstantLp
#check @Carleman.scalarConstantLp_ae
#print axioms Carleman.scalarConstantLp_ae
#check @Carleman.norm_sub_scalarConstantLp_sq
#print axioms Carleman.norm_sub_scalarConstantLp_sq
#check @Carleman.boundedAffine_memLp
#print axioms Carleman.boundedAffine_memLp
#check @Carleman.boundedAffineLp
#print axioms Carleman.boundedAffineLp
#check @Carleman.boundedAffineLp_ae
#print axioms Carleman.boundedAffineLp_ae
#check @Carleman.boundedAffineLp_weak
#print axioms Carleman.boundedAffineLp_weak
#check @Carleman.IsWeakSpatialDerivative.sub
#print axioms Carleman.IsWeakSpatialDerivative.sub
#check @Carleman.coordinateFirstFields
#print axioms Carleman.coordinateFirstFields
#check @Carleman.coordinateFirstJet
#print axioms Carleman.coordinateFirstJet
#check @Carleman.coordinateFirstJet_value
#print axioms Carleman.coordinateFirstJet_value
#check @Carleman.coordinateFirstJet_gradient_norm_sq
#print axioms Carleman.coordinateFirstJet_gradient_norm_sq
#check @Carleman.coordinateFunctional
#print axioms Carleman.coordinateFunctional
#check @Carleman.coordinateFunctional_basis
#print axioms Carleman.coordinateFunctional_basis
#check @Carleman.meanAffinePolynomial
#print axioms Carleman.meanAffinePolynomial
#check @Carleman.meanAffinePolynomial_apply
#print axioms Carleman.meanAffinePolynomial_apply
#check @Carleman.meanAffinePolynomial_derivative
#print axioms Carleman.meanAffinePolynomial_derivative
#check @Carleman.meanAffinePolynomial_residual_ae
#print axioms Carleman.meanAffinePolynomial_residual_ae
#check @Carleman.meanAffinePolynomial_mean_residual
#print axioms Carleman.meanAffinePolynomial_mean_residual
#check @Carleman.weakGradientMean
#print axioms Carleman.weakGradientMean
#check @Carleman.h2_gradient_mean_bound
#print axioms Carleman.h2_gradient_mean_bound
#check @Carleman.h2MeanAffine
#print axioms Carleman.h2MeanAffine
#check @Carleman.h2AffineResidualCoordinates
#print axioms Carleman.h2AffineResidualCoordinates
#check @Carleman.h2AffineResidual_weak
#print axioms Carleman.h2AffineResidual_weak
#check @Carleman.h2AffineResidual
#print axioms Carleman.h2AffineResidual
#check @Carleman.h2AffineResidual_value
#print axioms Carleman.h2AffineResidual_value
#check @Carleman.h2AffineResidual_value_ae
#print axioms Carleman.h2AffineResidual_value_ae
#check @Carleman.h2AffineResidual_gradient_component
#print axioms Carleman.h2AffineResidual_gradient_component
#check @Carleman.h2AffineResidual_mean
#print axioms Carleman.h2AffineResidual_mean
#check @Carleman.h2AffineResidual_gradient_bound
#print axioms Carleman.h2AffineResidual_gradient_bound
#check @Carleman.h2AffineResidual_value_bound
#print axioms Carleman.h2AffineResidual_value_bound
#check @Carleman.h2AffineResidual_homogeneous_bound
#print axioms Carleman.h2AffineResidual_homogeneous_bound
#check @Carleman.exists_convex_h2_affine_approximation
#print axioms Carleman.exists_convex_h2_affine_approximation

#check @Carleman.HasWeakTimeDerivative.congr_value
#print axioms Carleman.HasWeakTimeDerivative.congr_value
#check @Carleman.HasWeakTimeDerivative.exists_continuous_representative
#print axioms Carleman.HasWeakTimeDerivative.exists_continuous_representative
#check @Carleman.TimeGrid.continuous_representative_unique
#print axioms Carleman.TimeGrid.continuous_representative_unique
#check @Carleman.TimeGrid.pathL2_injective
#print axioms Carleman.TimeGrid.pathL2_injective
#check @Carleman.TimeGrid.exists_tracePath
#print axioms Carleman.TimeGrid.exists_tracePath
#check @Carleman.TimeGrid.weakTracePath
#print axioms Carleman.TimeGrid.weakTracePath
#check @Carleman.TimeGrid.weakTracePath_value
#print axioms Carleman.TimeGrid.weakTracePath_value
#check @Carleman.TimeGrid.weakTracePath_ae
#print axioms Carleman.TimeGrid.weakTracePath_ae
#check @Carleman.TimeGrid.weakTracePath_weak
#print axioms Carleman.TimeGrid.weakTracePath_weak
#check @Carleman.TimeGrid.weakTracePath_point_bound
#print axioms Carleman.TimeGrid.weakTracePath_point_bound
#check @Carleman.TimeGrid.weakTracePath_norm_bound
#print axioms Carleman.TimeGrid.weakTracePath_norm_bound
#check @Carleman.TimeGrid.weakTracePathCLM
#print axioms Carleman.TimeGrid.weakTracePathCLM
#check @Carleman.TimeGrid.weakTracePathCLM_value
#print axioms Carleman.TimeGrid.weakTracePathCLM_value
#check @Carleman.TimeGrid.weakTracePathCLM_eq_of_representative
#print axioms Carleman.TimeGrid.weakTracePathCLM_eq_of_representative
#check @Carleman.TimeGrid.weakIntervalTrace
#print axioms Carleman.TimeGrid.weakIntervalTrace
#check @Carleman.TimeGrid.weakIntervalTrace_bound
#print axioms Carleman.TimeGrid.weakIntervalTrace_bound
#check @Carleman.TimeGrid.weakIntervalTrace_fundamental
#print axioms Carleman.TimeGrid.weakIntervalTrace_fundamental
#check @Carleman.TimeGrid.weakIntervalTrace_affine_green
#print axioms Carleman.TimeGrid.weakIntervalTrace_affine_green
#check @Carleman.TimeGrid.weakIntervalTrace_zero_formula
#print axioms Carleman.TimeGrid.weakIntervalTrace_zero_formula
#check @Carleman.TimeGrid.weakIntervalTrace_end_formula
#print axioms Carleman.TimeGrid.weakIntervalTrace_end_formula
#check @Carleman.fiberEndpointIntegral
#print axioms Carleman.fiberEndpointIntegral
#check @Carleman.fiberEndpointIntegral_congr
#print axioms Carleman.fiberEndpointIntegral_congr
#check @Carleman.fiberEndpointIntegral_memLp_bound
#print axioms Carleman.fiberEndpointIntegral_memLp_bound
#check @Carleman.fiberEndpointIntegral_eq_weak_trace
#print axioms Carleman.fiberEndpointIntegral_eq_weak_trace
#check @Carleman.weak_slices_actual_endpoint_traces
#print axioms Carleman.weak_slices_actual_endpoint_traces

#check @Carleman.ae_forall_continuous_zero_on
#print axioms Carleman.ae_forall_continuous_zero_on
#check @Carleman.scalar_weak_interval_iff
#print axioms Carleman.scalar_weak_interval_iff
#check @Carleman.ae_weak_interval_of_ae_tests
#print axioms Carleman.ae_weak_interval_of_ae_tests
#check @Carleman.SpatialTest.tensor_tsupport_subset
#print axioms Carleman.SpatialTest.tensor_tsupport_subset
#check @Carleman.SpatialTest.tensor
#print axioms Carleman.SpatialTest.tensor
#check @Carleman.SpatialTest.tensor_interval_derivative
#print axioms Carleman.SpatialTest.tensor_interval_derivative
#check @Carleman.product_weak_marginal
#print axioms Carleman.product_weak_marginal
#check @Carleman.intervalSliceLp
#print axioms Carleman.intervalSliceLp
#check @Carleman.intervalSliceLp_ae
#print axioms Carleman.intervalSliceLp_ae
#check @Carleman.scalar_interval_test_pairing
#print axioms Carleman.scalar_interval_test_pairing
#check @Carleman.product_weak_slices
#print axioms Carleman.product_weak_slices
#check @Carleman.product_weak_endpoint_representatives
#print axioms Carleman.product_weak_endpoint_representatives
#check @Carleman.fiberEndpointLp
#print axioms Carleman.fiberEndpointLp
#check @Carleman.fiberEndpointLp_ae
#print axioms Carleman.fiberEndpointLp_ae
#check @Carleman.fiberEndpointLp_norm_sq
#print axioms Carleman.fiberEndpointLp_norm_sq
#check @Carleman.product_weak_face_trace_representatives
#print axioms Carleman.product_weak_face_trace_representatives

#check @Carleman.coordinateSplitMeasurable
#print axioms Carleman.coordinateSplitMeasurable
#check @Carleman.coordinateSplitMeasurable_apply
#print axioms Carleman.coordinateSplitMeasurable_apply
#check @Carleman.coordinateSplitMeasurable_symm_apply
#print axioms Carleman.coordinateSplitMeasurable_symm_apply
#check @Carleman.coordinateSplit
#print axioms Carleman.coordinateSplit
#check @Carleman.coordinateSplit_apply
#print axioms Carleman.coordinateSplit_apply
#check @Carleman.coordinateSplit_measurePreserving
#print axioms Carleman.coordinateSplit_measurePreserving
#check @Carleman.coordinateSplit_basis
#print axioms Carleman.coordinateSplit_basis
#check @Carleman.affineSpatialChart
#print axioms Carleman.affineSpatialChart
#check @Carleman.affineSpatialChart_apply
#print axioms Carleman.affineSpatialChart_apply
#check @Carleman.affineSpatialChart_hasFDerivAt
#print axioms Carleman.affineSpatialChart_hasFDerivAt
#check @Carleman.SpatialTest.pullbackAffine
#print axioms Carleman.SpatialTest.pullbackAffine
#check @Carleman.SpatialTest.pullbackAffine_derivative
#print axioms Carleman.SpatialTest.pullbackAffine_derivative
#check @Carleman.affineTransportLp
#print axioms Carleman.affineTransportLp
#check @Carleman.affineTransportLp_ae
#print axioms Carleman.affineTransportLp_ae
#check @Carleman.affineTransportLp_norm
#print axioms Carleman.affineTransportLp_norm
#check @Carleman.integral_mul_affineTransportLp
#print axioms Carleman.integral_mul_affineTransportLp
#check @Carleman.IsWeakSpatialDerivative.affine_transport
#print axioms Carleman.IsWeakSpatialDerivative.affine_transport
#check @Carleman.openCoordinateBox
#print axioms Carleman.openCoordinateBox
#check @Carleman.openCoordinateBox_isOpen
#print axioms Carleman.openCoordinateBox_isOpen
#check @Carleman.openCoordinateBox_isBounded
#print axioms Carleman.openCoordinateBox_isBounded
#check @Carleman.openCoordinateBox_finite
#print axioms Carleman.openCoordinateBox_finite
#check @Carleman.coordinateBoxChart
#print axioms Carleman.coordinateBoxChart
#check @Carleman.coordinateBoxChart_apply
#print axioms Carleman.coordinateBoxChart_apply
#check @Carleman.coordinateBoxChart_symm_apply
#print axioms Carleman.coordinateBoxChart_symm_apply
#check @Carleman.coordinateBoxChart_preimage
#print axioms Carleman.coordinateBoxChart_preimage
#check @Carleman.coordinateBoxChart_image
#print axioms Carleman.coordinateBoxChart_image
#check @Carleman.coordinateBoxChart_measurePreserving
#print axioms Carleman.coordinateBoxChart_measurePreserving
#check @Carleman.coordinateBoxChart_restrict
#print axioms Carleman.coordinateBoxChart_restrict
#check @Carleman.coordinateBoxAxisGrid
#print axioms Carleman.coordinateBoxAxisGrid
#check @Carleman.coordinateBoxAxisGrid_period
#print axioms Carleman.coordinateBoxAxisGrid_period
#check @Carleman.coordinateBoxChart_timeMeasure
#print axioms Carleman.coordinateBoxChart_timeMeasure
#check @Carleman.coordinateBoxLp
#print axioms Carleman.coordinateBoxLp
#check @Carleman.coordinateBoxLp_norm
#print axioms Carleman.coordinateBoxLp_norm
#check @Carleman.coordinateBoxLp_ae
#print axioms Carleman.coordinateBoxLp_ae
#check @Carleman.coordinateBox_weak_transport
#print axioms Carleman.coordinateBox_weak_transport
#check @Carleman.coordinateBoxFaceTrace
#print axioms Carleman.coordinateBoxFaceTrace
#check @Carleman.coordinateBoxFaceTrace_norm_sq
#print axioms Carleman.coordinateBoxFaceTrace_norm_sq
#check @Carleman.coordinateBoxFaceTrace_representatives
#print axioms Carleman.coordinateBoxFaceTrace_representatives
#check @Carleman.coordinateBoxFaceTrace_eq_continuous
#print axioms Carleman.coordinateBoxFaceTrace_eq_continuous
#check @Carleman.weakJetBoxFaceTrace
#print axioms Carleman.weakJetBoxFaceTrace
#check @Carleman.weakJetBoxFaceTrace_norm_sq
#print axioms Carleman.weakJetBoxFaceTrace_norm_sq
#check @Carleman.weakJetBoxFaceTrace_eq_continuous
#print axioms Carleman.weakJetBoxFaceTrace_eq_continuous

#check @Carleman.fiberEndpoint_integrable_slices
#print axioms Carleman.fiberEndpoint_integrable_slices
#check @Carleman.fiberEndpointLp_add
#print axioms Carleman.fiberEndpointLp_add
#check @Carleman.fiberEndpointLp_smul
#print axioms Carleman.fiberEndpointLp_smul
#check @Carleman.fiberEndpointLinearMap
#print axioms Carleman.fiberEndpointLinearMap
#check @Carleman.finiteDimensional_kernel_correction
#print axioms Carleman.finiteDimensional_kernel_correction
#check @Carleman.finiteFamily_kernel_correction
#print axioms Carleman.finiteFamily_kernel_correction
#check @Carleman.coordinateBoxTransportLinearMap
#print axioms Carleman.coordinateBoxTransportLinearMap
#check @Carleman.coordinateBoxTransportLinearMap_apply
#print axioms Carleman.coordinateBoxTransportLinearMap_apply
#check @Carleman.coordinateBoxFaceLinearMap
#print axioms Carleman.coordinateBoxFaceLinearMap
#check @Carleman.coordinateBoxFaceLinearMap_apply
#print axioms Carleman.coordinateBoxFaceLinearMap_apply
#check @Carleman.weakJetBoxFaceLinearMap
#print axioms Carleman.weakJetBoxFaceLinearMap
#check @Carleman.weakJetBoxFaceLinearMap_apply
#print axioms Carleman.weakJetBoxFaceLinearMap_apply
#check @Carleman.AffineCoefficients
#print axioms Carleman.AffineCoefficients
#check @Carleman.affineCoefficientPolynomial
#print axioms Carleman.affineCoefficientPolynomial
#check @Carleman.affineCoefficientPolynomial_apply
#print axioms Carleman.affineCoefficientPolynomial_apply
#check @Carleman.affineBoxValueMap
#print axioms Carleman.affineBoxValueMap
#check @Carleman.affineBoxValueMap_ae
#print axioms Carleman.affineBoxValueMap_ae
#check @Carleman.affineBoxDerivativeMap
#print axioms Carleman.affineBoxDerivativeMap
#check @Carleman.affineBoxDerivativeMap_weak
#print axioms Carleman.affineBoxDerivativeMap_weak
#check @Carleman.affineBoxFaceMap
#print axioms Carleman.affineBoxFaceMap
#check @Carleman.affineBoxFaceMap_ae
#print axioms Carleman.affineBoxFaceMap_ae
#check @Carleman.closedCoordinateBox
#print axioms Carleman.closedCoordinateBox
#check @Carleman.closure_openCoordinateBox
#print axioms Carleman.closure_openCoordinateBox
#check @Carleman.coordinateFacePoint_continuous
#print axioms Carleman.coordinateFacePoint_continuous
#check @Carleman.coordinateClosedFace
#print axioms Carleman.coordinateClosedFace
#check @Carleman.coordinateClosedFace_eq_image
#print axioms Carleman.coordinateClosedFace_eq_image
#check @Carleman.affineBoxFaceMap_eq_zero_iff
#print axioms Carleman.affineBoxFaceMap_eq_zero_iff
#check @Carleman.affineBoxSelectedFaceMap
#print axioms Carleman.affineBoxSelectedFaceMap
#check @Carleman.affineBoxSelectedFaceMap_apply
#print axioms Carleman.affineBoxSelectedFaceMap_apply
#check @Carleman.affineBoxSelectedFaceMap_kernel
#print axioms Carleman.affineBoxSelectedFaceMap_kernel
#check @Carleman.affineBox_uniform_kernel_correction
#print axioms Carleman.affineBox_uniform_kernel_correction
#check @Carleman.affineBoxSelectedFaceMap_norm_le_rss
#print axioms Carleman.affineBoxSelectedFaceMap_norm_le_rss
#check @Carleman.affineCoefficientPolynomial_surjective
#print axioms Carleman.affineCoefficientPolynomial_surjective
#check @Carleman.affineBoxGradientMap
#print axioms Carleman.affineBoxGradientMap
#check @Carleman.affineBoxJet
#print axioms Carleman.affineBoxJet
#check @Carleman.affineBoxJet_value
#print axioms Carleman.affineBoxJet_value
#check @Carleman.affineBoxJet_gradient
#print axioms Carleman.affineBoxJet_gradient
#check @Carleman.affineBox_bulk_norm_bound
#print axioms Carleman.affineBox_bulk_norm_bound
#check @Carleman.affineBox_uniform_h1_correction
#print axioms Carleman.affineBox_uniform_h1_correction
#check @Carleman.affineBox_uniform_h1_correction_rss
#print axioms Carleman.affineBox_uniform_h1_correction_rss
#check @Carleman.unitCube_uniform_affine_correction
#print axioms Carleman.unitCube_uniform_affine_correction

#check @Carleman.openCoordinateBox_convex
#print axioms Carleman.openCoordinateBox_convex
#check @Carleman.openCoordinateBox_nonempty
#print axioms Carleman.openCoordinateBox_nonempty
#check @Carleman.openCoordinateBox_volume_pos
#print axioms Carleman.openCoordinateBox_volume_pos
#check @Carleman.unitCube_diameter_bound
#print axioms Carleman.unitCube_diameter_bound
#check @Carleman.affineBoxJetLinearMap
#print axioms Carleman.affineBoxJetLinearMap
#check @Carleman.affineBoxJetLinearMap_apply
#print axioms Carleman.affineBoxJetLinearMap_apply
#check @Carleman.weakJetBoxFaceLinearMap_affine
#print axioms Carleman.weakJetBoxFaceLinearMap_affine
#check @Carleman.unitCubeFace_norm_le
#print axioms Carleman.unitCubeFace_norm_le
#check @Carleman.h1_value_gradient_add_bound
#print axioms Carleman.h1_value_gradient_add_bound
#check @Carleman.h2AffineResidual_eq_jet_sub
#print axioms Carleman.h2AffineResidual_eq_jet_sub
#check @Carleman.unitCube_h2_affine_approximation
#print axioms Carleman.unitCube_h2_affine_approximation
#check @Carleman.unitCube_selected_affine_trace_bound
#print axioms Carleman.unitCube_selected_affine_trace_bound
#check @Carleman.unitCube_h1_boundary_correction
#print axioms Carleman.unitCube_h1_boundary_correction
#check @Carleman.unitCube_h2_boundary_affine
#print axioms Carleman.unitCube_h2_boundary_affine
#check @Carleman.unitCube_h2_boundary_affine_actual
#print axioms Carleman.unitCube_h2_boundary_affine_actual

#check @Carleman.coordinateDilation
#print axioms Carleman.coordinateDilation
#check @Carleman.coordinateDilation_apply
#print axioms Carleman.coordinateDilation_apply
#check @Carleman.coordinateDilation_symm_apply
#print axioms Carleman.coordinateDilation_symm_apply
#check @Carleman.coordinateDilation_basis
#print axioms Carleman.coordinateDilation_basis
#check @Carleman.coordinateDilation_norm_le
#print axioms Carleman.coordinateDilation_norm_le
#check @Carleman.coordinateDilation_symm_norm_le
#print axioms Carleman.coordinateDilation_symm_norm_le
#check @Carleman.coordinateDilation_jacobian
#print axioms Carleman.coordinateDilation_jacobian
#check @Carleman.physicalBoxChart
#print axioms Carleman.physicalBoxChart
#check @Carleman.physicalBoxChart_apply
#print axioms Carleman.physicalBoxChart_apply
#check @Carleman.physicalBoxChart_preimage_open
#print axioms Carleman.physicalBoxChart_preimage_open
#check @Carleman.physicalBoxChart_image_open
#print axioms Carleman.physicalBoxChart_image_open
#check @Carleman.physicalBoxChart_preimage_closed
#print axioms Carleman.physicalBoxChart_preimage_closed
#check @Carleman.physicalBoxChart_preimage_face
#print axioms Carleman.physicalBoxChart_preimage_face
#check @Carleman.physicalBoxChart_image_face
#print axioms Carleman.physicalBoxChart_image_face
#check @Carleman.physicalBoxChart_facePoint
#print axioms Carleman.physicalBoxChart_facePoint
#check @Carleman.integral_physicalBoxChart
#print axioms Carleman.integral_physicalBoxChart
#check @Carleman.physicalBoxChart_face_jacobian
#print axioms Carleman.physicalBoxChart_face_jacobian
#check @Carleman.affineCoefficientChange
#print axioms Carleman.affineCoefficientChange
#check @Carleman.affineCoefficientChange_apply
#print axioms Carleman.affineCoefficientChange_apply
#check @Carleman.affineBoxPullback
#print axioms Carleman.affineBoxPullback
#check @Carleman.affineBoxPullback_apply
#print axioms Carleman.affineBoxPullback_apply
#check @Carleman.affineBoxPullback_derivative
#print axioms Carleman.affineBoxPullback_derivative
#check @Carleman.affineBoxPullback_zero_face_iff
#print axioms Carleman.affineBoxPullback_zero_face_iff
#check @Carleman.affineBoxValueMap_norm_sq
#print axioms Carleman.affineBoxValueMap_norm_sq
#check @Carleman.affineBoxFaceMap_norm_sq
#print axioms Carleman.affineBoxFaceMap_norm_sq
#check @Carleman.affineBoxValueMap_scaling_sq
#print axioms Carleman.affineBoxValueMap_scaling_sq
#check @Carleman.affineBoxFaceMap_scaling_sq
#print axioms Carleman.affineBoxFaceMap_scaling_sq
#check @Carleman.affineBoxDerivativeMap_norm_sq
#print axioms Carleman.affineBoxDerivativeMap_norm_sq
#check @Carleman.coordinateBox_volume_scaling
#print axioms Carleman.coordinateBox_volume_scaling
#check @Carleman.affineBoxGradientMap_norm_sq
#print axioms Carleman.affineBoxGradientMap_norm_sq
#check @Carleman.affineBoxGradientMap_scaling_sq
#print axioms Carleman.affineBoxGradientMap_scaling_sq
#check @Carleman.affineBoxGradientMap_scaling_bound_sq
#print axioms Carleman.affineBoxGradientMap_scaling_bound_sq
#check @Carleman.affineBoxValueMap_scaling
#print axioms Carleman.affineBoxValueMap_scaling
#check @Carleman.affineBoxGradientMap_scaling_bound
#print axioms Carleman.affineBoxGradientMap_scaling_bound
#check @Carleman.affineBox_h1_scaling_bound
#print axioms Carleman.affineBox_h1_scaling_bound

#check @Carleman.physicalBox_weak_face_scaled_bound
#print axioms Carleman.physicalBox_weak_face_scaled_bound
#check @Carleman.physicalBox_weak_face_uniform_bound
#print axioms Carleman.physicalBox_weak_face_uniform_bound
#check @Carleman.physicalBox_affine_face_norm_scaling
#print axioms Carleman.physicalBox_affine_face_norm_scaling
#check @Carleman.physicalBox_selected_reference_trace_bound
#print axioms Carleman.physicalBox_selected_reference_trace_bound
#check @Carleman.h1_scaled_value_gradient_add_bound
#print axioms Carleman.h1_scaled_value_gradient_add_bound
#check @Carleman.physicalBox_h1_boundary_correction
#print axioms Carleman.physicalBox_h1_boundary_correction
#check @Carleman.physicalBox_diameter_bound
#print axioms Carleman.physicalBox_diameter_bound
#check @Carleman.physicalBox_h2_affine_approximation
#print axioms Carleman.physicalBox_h2_affine_approximation
#check @Carleman.unitCube_face_tangent_derivative_zero
#print axioms Carleman.unitCube_face_tangent_derivative_zero
#check @Carleman.unitCube_two_faces_affine_zero
#print axioms Carleman.unitCube_two_faces_affine_zero
#check @Carleman.physicalBox_two_faces_affine_zero
#print axioms Carleman.physicalBox_two_faces_affine_zero
#check @Carleman.physicalBox_h2_boundary_affine
#print axioms Carleman.physicalBox_h2_boundary_affine
#check @Carleman.physicalBox_h2_boundary_affine_actual
#print axioms Carleman.physicalBox_h2_boundary_affine_actual
#check @Carleman.physicalBox_h2_corner_bound
#print axioms Carleman.physicalBox_h2_corner_bound
#check @Carleman.OriginalForm.boundary_affine_lemma
#print axioms Carleman.OriginalForm.boundary_affine_lemma

#check @Carleman.subdomainLp_norm_le
#print axioms Carleman.subdomainLp_norm_le
#check @Carleman.subdomainLinearMap
#print axioms Carleman.subdomainLinearMap
#check @Carleman.subdomainCLM
#print axioms Carleman.subdomainCLM
#check @Carleman.WeakSobolevJet.restrictSubdomain_norm_le
#print axioms Carleman.WeakSobolevJet.restrictSubdomain_norm_le
#check @Carleman.WeakSobolevJet.restrictSubdomainLinearMap
#print axioms Carleman.WeakSobolevJet.restrictSubdomainLinearMap
#check @Carleman.WeakSobolevJet.restrictSubdomainCLM
#print axioms Carleman.WeakSobolevJet.restrictSubdomainCLM
#check @Carleman.WeakSobolevJet.restrictSubdomain_test_value_ae
#print axioms Carleman.WeakSobolevJet.restrictSubdomain_test_value_ae
#check @Carleman.weakJetBoxFace_bounded
#print axioms Carleman.weakJetBoxFace_bounded
#check @Carleman.weakJetBoxFaceCLM
#print axioms Carleman.weakJetBoxFaceCLM
#check @Carleman.weakJetBoxFaceCLM_apply
#print axioms Carleman.weakJetBoxFaceCLM_apply
#check @Carleman.subdomainBoxFaceCLM
#print axioms Carleman.subdomainBoxFaceCLM
#check @Carleman.subdomainBoxFaceCLM_apply
#print axioms Carleman.subdomainBoxFaceCLM_apply
#check @Carleman.subdomainBoxFace_test_zero
#print axioms Carleman.subdomainBoxFace_test_zero
#check @Carleman.dirichlet_subdomain_box_face_zero
#print axioms Carleman.dirichlet_subdomain_box_face_zero
#check @Carleman.WeakSobolevJet.restrictSubdomain_truncate
#print axioms Carleman.WeakSobolevJet.restrictSubdomain_truncate
#check @Carleman.dirichlet_h2_local_boundary_affine
#print axioms Carleman.dirichlet_h2_local_boundary_affine

#check @Carleman.BoundedMultiplier.onSubdomain
#print axioms Carleman.BoundedMultiplier.onSubdomain
#check @Carleman.BoundedMultiplier.onSubdomain_map
#print axioms Carleman.BoundedMultiplier.onSubdomain_map
#check @Carleman.BoundedMultiplier.onSubdomain_seminorm
#print axioms Carleman.BoundedMultiplier.onSubdomain_seminorm
#check @Carleman.BoundedMultiplier.seminorm_le_anchor
#print axioms Carleman.BoundedMultiplier.seminorm_le_anchor
#check @Carleman.BoundedMultiplier.norm_le_seminorm_anchor
#print axioms Carleman.BoundedMultiplier.norm_le_seminorm_anchor
#check @Carleman.weighted_dirichlet_h2_local_boundary_affine
#print axioms Carleman.weighted_dirichlet_h2_local_boundary_affine
#check @Carleman.coordinateBox_diameter_bound
#print axioms Carleman.coordinateBox_diameter_bound
#check @Carleman.allowedWeight_box_comparison
#print axioms Carleman.allowedWeight_box_comparison
#check @Carleman.allowed_weight_dirichlet_h2_local_boundary_affine
#print axioms Carleman.allowed_weight_dirichlet_h2_local_boundary_affine

#check @Carleman.finiteCoverMultiplicity
#print axioms Carleman.finiteCoverMultiplicity
#check @Carleman.sum_indicator_eq_multiplicity
#print axioms Carleman.sum_indicator_eq_multiplicity
#check @Carleman.bochnerL2Norm_sq_finite_overlap
#print axioms Carleman.bochnerL2Norm_sq_finite_overlap
#check @Carleman.bochnerL2Norm_sq_finite_cover
#print axioms Carleman.bochnerL2Norm_sq_finite_cover
#check @Carleman.subdomainLp_norm_eq_bochner
#print axioms Carleman.subdomainLp_norm_eq_bochner
#check @Carleman.subdomainLp_sq_finite_overlap
#print axioms Carleman.subdomainLp_sq_finite_overlap
#check @Carleman.subdomainLp_sq_finite_cover
#print axioms Carleman.subdomainLp_sq_finite_cover
#check @Carleman.cartesianPatch
#print axioms Carleman.cartesianPatch
#check @Carleman.cartesianPatch_isOpen
#print axioms Carleman.cartesianPatch_isOpen
#check @Carleman.cartesianPatch_index_bound
#print axioms Carleman.cartesianPatch_index_bound
#check @Carleman.cartesianPatch_window_card
#print axioms Carleman.cartesianPatch_window_card
#check @Carleman.cartesianPatch_multiplicity_le
#print axioms Carleman.cartesianPatch_multiplicity_le
#check @Carleman.cartesianPatch_permutation_multiplicity_le
#print axioms Carleman.cartesianPatch_permutation_multiplicity_le
#check @Carleman.finite_patch_h2_assembly
#print axioms Carleman.finite_patch_h2_assembly
#check @Carleman.weighted_finite_patch_h2_assembly
#print axioms Carleman.weighted_finite_patch_h2_assembly
#check @Carleman.weighted_cartesian_patch_h2_assembly
#print axioms Carleman.weighted_cartesian_patch_h2_assembly

#check @Carleman.coordinateStandardSimplex
#print axioms Carleman.coordinateStandardSimplex
#check @Carleman.kuhnPrefixMatrix
#print axioms Carleman.kuhnPrefixMatrix
#check @Carleman.kuhnPrefixMatrix_det
#print axioms Carleman.kuhnPrefixMatrix_det
#check @Carleman.kuhnPrefixEquiv
#print axioms Carleman.kuhnPrefixEquiv
#check @Carleman.kuhnPrefixEquiv_basis
#print axioms Carleman.kuhnPrefixEquiv_basis
#check @Carleman.kuhnReferenceSimplex
#print axioms Carleman.kuhnReferenceSimplex
#check @Carleman.kuhnReferenceSimplex_points
#print axioms Carleman.kuhnReferenceSimplex_points
#check @Carleman.coordinatePermutation
#print axioms Carleman.coordinatePermutation
#check @Carleman.coordinatePermutation_apply
#print axioms Carleman.coordinatePermutation_apply
#check @Carleman.cartesianKuhnSimplex
#print axioms Carleman.cartesianKuhnSimplex
#check @Carleman.cartesianKuhnSimplex_points
#print axioms Carleman.cartesianKuhnSimplex_points
#check @Carleman.cartesianKuhnSimplex_points_step
#print axioms Carleman.cartesianKuhnSimplex_points_step
#check @Carleman.closedCoordinateBox_convex
#print axioms Carleman.closedCoordinateBox_convex
#check @Carleman.cartesianKuhnSimplex_cell_subset_box
#print axioms Carleman.cartesianKuhnSimplex_cell_subset_box
#check @Carleman.cartesianKuhnSimplex_cell_subset_patch
#print axioms Carleman.cartesianKuhnSimplex_cell_subset_patch
#check @Carleman.cartesianKuhn_shared_vertex_index_bound
#print axioms Carleman.cartesianKuhn_shared_vertex_index_bound
#check @Carleman.cartesianKuhn_shared_vertex_cell_subset
#print axioms Carleman.cartesianKuhn_shared_vertex_cell_subset
#check @Carleman.cartesianKuhnStarPatch
#print axioms Carleman.cartesianKuhnStarPatch
#check @Carleman.cartesianKuhnStarPatch_subset_patch
#print axioms Carleman.cartesianKuhnStarPatch_subset_patch
#check @Carleman.cartesianKuhnStarPatch_multiplicity_le
#print axioms Carleman.cartesianKuhnStarPatch_multiplicity_le
#check @Carleman.cartesianKuhn_cell_subset_starPatch
#print axioms Carleman.cartesianKuhn_cell_subset_starPatch
#check @Carleman.cartesianKuhnStarPatch_eq_finite_union
#print axioms Carleman.cartesianKuhnStarPatch_eq_finite_union
#check @Carleman.cartesianKuhnStarPatch_compact
#print axioms Carleman.cartesianKuhnStarPatch_compact
#check @Carleman.cartesianKuhnStarPatch_measurable
#print axioms Carleman.cartesianKuhnStarPatch_measurable

#check @Carleman.kuhnExtendedCoordinate
#print axioms Carleman.kuhnExtendedCoordinate
#check @Carleman.kuhnExtendedCoordinate_zero
#print axioms Carleman.kuhnExtendedCoordinate_zero
#check @Carleman.kuhnExtendedCoordinate_last
#print axioms Carleman.kuhnExtendedCoordinate_last
#check @Carleman.kuhnExtendedCoordinate_inner
#print axioms Carleman.kuhnExtendedCoordinate_inner
#check @Carleman.kuhnBarycentricWeight
#print axioms Carleman.kuhnBarycentricWeight
#check @Carleman.kuhnBarycentricWeight_sum
#print axioms Carleman.kuhnBarycentricWeight_sum
#check @Carleman.kuhnBarycentricWeight_reconstruct
#print axioms Carleman.kuhnBarycentricWeight_reconstruct
#check @Carleman.kuhnBarycentricWeight_nonneg
#print axioms Carleman.kuhnBarycentricWeight_nonneg
#check @Carleman.kuhnReferenceSimplex_mem_of_ordered
#print axioms Carleman.kuhnReferenceSimplex_mem_of_ordered
#check @Carleman.kuhnOrderedCube
#print axioms Carleman.kuhnOrderedCube
#check @Carleman.kuhnOrderedCube_convex
#print axioms Carleman.kuhnOrderedCube_convex
#check @Carleman.kuhnReferenceSimplex_cell_eq_ordered
#print axioms Carleman.kuhnReferenceSimplex_cell_eq_ordered
#check @Carleman.cartesianKuhnChart
#print axioms Carleman.cartesianKuhnChart
#check @Carleman.cartesianKuhnChart_apply
#print axioms Carleman.cartesianKuhnChart_apply
#check @Carleman.cartesianKuhnChart_symm_apply
#print axioms Carleman.cartesianKuhnChart_symm_apply
#check @Carleman.cartesianKuhnSimplex_cell_eq_chart
#print axioms Carleman.cartesianKuhnSimplex_cell_eq_chart
#check @Carleman.cartesianKuhnSimplex_mem_iff
#print axioms Carleman.cartesianKuhnSimplex_mem_iff
#check @Carleman.cartesianKuhnSimplex_cover_box
#print axioms Carleman.cartesianKuhnSimplex_cover_box
#check @Carleman.CartesianCellIndex
#print axioms Carleman.CartesianCellIndex
#check @Carleman.cartesianCellLatticeIndex
#print axioms Carleman.cartesianCellLatticeIndex
#check @Carleman.cartesianCellLatticeIndex_injective
#print axioms Carleman.cartesianCellLatticeIndex_injective
#check @Carleman.cartesianCellIndex_card
#print axioms Carleman.cartesianCellIndex_card
#check @Carleman.cartesianFiniteSimplex
#print axioms Carleman.cartesianFiniteSimplex
#check @Carleman.cartesianFiniteSimplex_cover
#print axioms Carleman.cartesianFiniteSimplex_cover
#check @Carleman.cartesianFiniteSimplex_ae_cover
#print axioms Carleman.cartesianFiniteSimplex_ae_cover
#check @Carleman.cartesianFiniteStar_multiplicity_le
#print axioms Carleman.cartesianFiniteStar_multiplicity_le
#check @Carleman.linear_strict_of_mem_interior_le
#print axioms Carleman.linear_strict_of_mem_interior_le
#check @Carleman.cartesianKuhnSimplex_interior_box
#print axioms Carleman.cartesianKuhnSimplex_interior_box
#check @Carleman.cartesianKuhnSimplex_interior_strictAnti
#print axioms Carleman.cartesianKuhnSimplex_interior_strictAnti
#check @Carleman.cartesianKuhnSimplex_common_interior_origin
#print axioms Carleman.cartesianKuhnSimplex_common_interior_origin
#check @Carleman.strictAnti_permutation_unique
#print axioms Carleman.strictAnti_permutation_unique
#check @Carleman.cartesianKuhnSimplex_interiors_disjoint
#print axioms Carleman.cartesianKuhnSimplex_interiors_disjoint
#check @Carleman.cartesianFiniteSimplex_interiors_disjoint
#print axioms Carleman.cartesianFiniteSimplex_interiors_disjoint
#check @Carleman.cartesianFiniteSimplex_ae_partition
#print axioms Carleman.cartesianFiniteSimplex_ae_partition

#check @Carleman.integer_weighted_le_of_pos
#print axioms Carleman.integer_weighted_le_of_pos
#check @Carleman.simplexBarycentric_reconstruct
#print axioms Carleman.simplexBarycentric_reconstruct
#check @Carleman.simplex_mem_convexHull_positive_support
#print axioms Carleman.simplex_mem_convexHull_positive_support
#check @Carleman.simplex_integer_affine_le_of_pos
#print axioms Carleman.simplex_integer_affine_le_of_pos
#check @Carleman.cartesianGridPoint
#print axioms Carleman.cartesianGridPoint
#check @Carleman.cartesianGridCoordinate
#print axioms Carleman.cartesianGridCoordinate
#check @Carleman.cartesianGridCoordinate_apply
#print axioms Carleman.cartesianGridCoordinate_apply
#check @Carleman.cartesianGridCoordinate_point
#print axioms Carleman.cartesianGridCoordinate_point
#check @Carleman.kuhnVertexIndex
#print axioms Carleman.kuhnVertexIndex
#check @Carleman.cartesianKuhnSimplex_points_eq_gridPoint
#print axioms Carleman.cartesianKuhnSimplex_points_eq_gridPoint
#check @Carleman.cartesianGridCoordinate_vertex
#print axioms Carleman.cartesianGridCoordinate_vertex
#check @Carleman.kuhnVertexIndex_width
#print axioms Carleman.kuhnVertexIndex_width
#check @Carleman.kuhnVertexIndex_difference_width
#print axioms Carleman.kuhnVertexIndex_difference_width
#check @Carleman.cartesianKuhn_positive_vertex_upper
#print axioms Carleman.cartesianKuhn_positive_vertex_upper
#check @Carleman.cartesianKuhn_positive_vertex_lower
#print axioms Carleman.cartesianKuhn_positive_vertex_lower
#check @Carleman.cartesianKuhn_positive_vertex_difference
#print axioms Carleman.cartesianKuhn_positive_vertex_difference
#check @Carleman.cartesianKuhn_gridPoint_is_vertex
#print axioms Carleman.cartesianKuhn_gridPoint_is_vertex
#check @Carleman.cartesianKuhn_positive_vertex_mem_other
#print axioms Carleman.cartesianKuhn_positive_vertex_mem_other
#check @Carleman.cartesianKuhn_cells_common_face
#print axioms Carleman.cartesianKuhn_cells_common_face
#check @Carleman.cartesianKuhnPartition
#print axioms Carleman.cartesianKuhnPartition
#check @Carleman.cartesianKuhnPartition_faceMatching
#print axioms Carleman.cartesianKuhnPartition_faceMatching
#check @Carleman.simplex_affine_min_eq_of_pos
#print axioms Carleman.simplex_affine_min_eq_of_pos
#check @Carleman.simplex_coordinateBox_boundary_support
#print axioms Carleman.simplex_coordinateBox_boundary_support
#check @Carleman.cartesianKuhnPartition_boundaryFitted
#print axioms Carleman.cartesianKuhnPartition_boundaryFitted
#check @Carleman.cartesianKuhnHat
#print axioms Carleman.cartesianKuhnHat
#check @Carleman.cartesianKuhnHat_on_cell
#print axioms Carleman.cartesianKuhnHat_on_cell
#check @Carleman.cartesianKuhnHat_vertex
#print axioms Carleman.cartesianKuhnHat_vertex
#check @Carleman.cartesianKuhnHat_data_boundary
#print axioms Carleman.cartesianKuhnHat_data_boundary
#check @Carleman.cartesianKuhnHat_continuous
#print axioms Carleman.cartesianKuhnHat_continuous
#check @Carleman.cartesianKuhnHat_zero_compl
#print axioms Carleman.cartesianKuhnHat_zero_compl
#check @Carleman.cartesianKuhnHat_compact
#print axioms Carleman.cartesianKuhnHat_compact
#check @Carleman.cartesianKuhnHat_nonneg
#print axioms Carleman.cartesianKuhnHat_nonneg
#check @Carleman.cartesianKuhnHat_le_one
#print axioms Carleman.cartesianKuhnHat_le_one
#check @Carleman.cartesianKuhnHatLp
#print axioms Carleman.cartesianKuhnHatLp
#check @Carleman.cartesianKuhnHatLp_ae
#print axioms Carleman.cartesianKuhnHatLp_ae
#check @Carleman.cartesianKuhnHatLp_mem_dirichlet
#print axioms Carleman.cartesianKuhnHatLp_mem_dirichlet
#check @Carleman.cartesianKuhnHat_on_incidentCell
#print axioms Carleman.cartesianKuhnHat_on_incidentCell
#check @Carleman.cartesianKuhnHat_zero_on_nonincidentCell
#print axioms Carleman.cartesianKuhnHat_zero_on_nonincidentCell
#check @Carleman.cartesianFiniteNodeStar
#print axioms Carleman.cartesianFiniteNodeStar
#check @Carleman.cartesianFiniteNodeStar_compact
#print axioms Carleman.cartesianFiniteNodeStar_compact
#check @Carleman.cartesianKuhnHat_support_subset
#print axioms Carleman.cartesianKuhnHat_support_subset
#check @Carleman.cartesianKuhnHat_tsupport_subset
#print axioms Carleman.cartesianKuhnHat_tsupport_subset
#check @Carleman.cartesianKuhnHat_tsupport_subset_cellStar
#print axioms Carleman.cartesianKuhnHat_tsupport_subset_cellStar

#check @Carleman.simplex_cell_affine_relabel
#print axioms Carleman.simplex_cell_affine_relabel
#check @Carleman.simplexBarycentric_affine_relabel
#print axioms Carleman.simplexBarycentric_affine_relabel
#check @Carleman.kuhnReflectedOrigin
#print axioms Carleman.kuhnReflectedOrigin
#check @Carleman.kuhnReflectedPermutation
#print axioms Carleman.kuhnReflectedPermutation
#check @Carleman.kuhnVertexIndex_reflection
#print axioms Carleman.kuhnVertexIndex_reflection
#check @Carleman.cartesianKuhnSimplex_reflection_vertex
#print axioms Carleman.cartesianKuhnSimplex_reflection_vertex
#check @Carleman.cartesianKuhnSimplex_reflection_cell
#print axioms Carleman.cartesianKuhnSimplex_reflection_cell
#check @Carleman.cartesianKuhn_incident_finite_index
#print axioms Carleman.cartesianKuhn_incident_finite_index
#check @Carleman.cartesianFiniteSimplex_of_latticeIndex
#print axioms Carleman.cartesianFiniteSimplex_of_latticeIndex
#check @Carleman.cartesianFiniteSimplex_reflected_incident
#print axioms Carleman.cartesianFiniteSimplex_reflected_incident
#check @Carleman.cartesianKuhnHat_reflection_of_nonzero
#print axioms Carleman.cartesianKuhnHat_reflection_of_nonzero
#check @Carleman.cartesianKuhnHat_reflection
#print axioms Carleman.cartesianKuhnHat_reflection
#check @Carleman.cartesianKuhnHat_integrable
#print axioms Carleman.cartesianKuhnHat_integrable
#check @Carleman.cartesianKuhnHat_firstMoment_integrable
#print axioms Carleman.cartesianKuhnHat_firstMoment_integrable
#check @Carleman.cartesianKuhnHat_firstMoment_zero
#print axioms Carleman.cartesianKuhnHat_firstMoment_zero
#check @Carleman.cartesianKuhnHat_firstMoment_domain
#print axioms Carleman.cartesianKuhnHat_firstMoment_domain

#check @Carleman.openCoordinateBox_volume_real
#print axioms Carleman.openCoordinateBox_volume_real
#check @Carleman.cartesianKuhnSimplex_translation_vertex
#print axioms Carleman.cartesianKuhnSimplex_translation_vertex
#check @Carleman.cartesianKuhnSimplex_volume_translation
#print axioms Carleman.cartesianKuhnSimplex_volume_translation
#check @Carleman.cartesianKuhnSimplex_sum_permutation_volume
#print axioms Carleman.cartesianKuhnSimplex_sum_permutation_volume
#check @Carleman.cartesianKuhn_origin_eq_of_vertex_eq
#print axioms Carleman.cartesianKuhn_origin_eq_of_vertex_eq
#check @Carleman.cartesianFiniteSimplex_fixed_vertex_injective
#print axioms Carleman.cartesianFiniteSimplex_fixed_vertex_injective
#check @Carleman.cartesianKuhn_node_incidence_unique
#print axioms Carleman.cartesianKuhn_node_incidence_unique
#check @Carleman.cartesianKuhn_node_incidence_sum
#print axioms Carleman.cartesianKuhn_node_incidence_sum
#check @Carleman.integral_cartesianKuhnHat_cell
#print axioms Carleman.integral_cartesianKuhnHat_cell
#check @Carleman.cartesianKuhnHat_mass_domain
#print axioms Carleman.cartesianKuhnHat_mass_domain
#check @Carleman.cartesianKuhnHat_mass
#print axioms Carleman.cartesianKuhnHat_mass
#check @Carleman.cartesianKuhnHat_affine_integrable
#print axioms Carleman.cartesianKuhnHat_affine_integrable
#check @Carleman.cartesianKuhnHat_affine_integral
#print axioms Carleman.cartesianKuhnHat_affine_integral
#check @Carleman.cartesianKuhnHat_affine_integral_domain
#print axioms Carleman.cartesianKuhnHat_affine_integral_domain
#check @Carleman.cartesianKuhnHat_affine_moment
#print axioms Carleman.cartesianKuhnHat_affine_moment

#check @Carleman.simplexLoadPolynomial
#print axioms Carleman.simplexLoadPolynomial
#check @Carleman.simplexLoadPolynomial_continuous
#print axioms Carleman.simplexLoadPolynomial_continuous
#check @Carleman.integral_simplex_dual_barycentric
#print axioms Carleman.integral_simplex_dual_barycentric
#check @Carleman.integral_simplexLoadPolynomial_barycentric
#print axioms Carleman.integral_simplexLoadPolynomial_barycentric
#check @Carleman.cartesianKuhnLoadCoefficients
#print axioms Carleman.cartesianKuhnLoadCoefficients
#check @Carleman.cartesianKuhnLoad
#print axioms Carleman.cartesianKuhnLoad
#check @Carleman.cartesianKuhnLoad_on_cell
#print axioms Carleman.cartesianKuhnLoad_on_cell
#check @Carleman.cartesianKuhnLoad_memLp
#print axioms Carleman.cartesianKuhnLoad_memLp
#check @Carleman.cartesianKuhnLoad_integrable
#print axioms Carleman.cartesianKuhnLoad_integrable
#check @Carleman.cartesianKuhnLoad_mul_hat_integrable
#print axioms Carleman.cartesianKuhnLoad_mul_hat_integrable
#check @Carleman.integral_cartesianKuhnLoad_mul_hat_cell
#print axioms Carleman.integral_cartesianKuhnLoad_mul_hat_cell
#check @Carleman.cartesianKuhnLoad_hat_integral_domain
#print axioms Carleman.cartesianKuhnLoad_hat_integral_domain
#check @Carleman.cartesianKuhnLoad_moment_right_inverse
#print axioms Carleman.cartesianKuhnLoad_moment_right_inverse
#check @Carleman.CartesianInteriorIndex
#print axioms Carleman.CartesianInteriorIndex
#check @Carleman.cartesianInteriorLatticeIndex
#print axioms Carleman.cartesianInteriorLatticeIndex
#check @Carleman.cartesianInteriorPoint
#print axioms Carleman.cartesianInteriorPoint
#check @Carleman.cartesianInteriorPoint_mem
#print axioms Carleman.cartesianInteriorPoint_mem
#check @Carleman.cartesianInteriorPoint_injective
#print axioms Carleman.cartesianInteriorPoint_injective
#check @Carleman.cartesianInteriorData
#print axioms Carleman.cartesianInteriorData
#check @Carleman.cartesianInteriorData_at_node
#print axioms Carleman.cartesianInteriorData_at_node
#check @Carleman.cartesianKuhnLoadLift
#print axioms Carleman.cartesianKuhnLoadLift
#check @Carleman.cartesianKuhnLoadLift_memLp
#print axioms Carleman.cartesianKuhnLoadLift_memLp
#check @Carleman.cartesianKuhnLoadLiftLp
#print axioms Carleman.cartesianKuhnLoadLiftLp
#check @Carleman.cartesianKuhnLoadLiftLp_ae
#print axioms Carleman.cartesianKuhnLoadLiftLp_ae
#check @Carleman.cartesianKuhnMoment
#print axioms Carleman.cartesianKuhnMoment
#check @Carleman.cartesianKuhnMoment_integrable
#print axioms Carleman.cartesianKuhnMoment_integrable
#check @Carleman.cartesianKuhnLoadLiftLp_right_inverse
#print axioms Carleman.cartesianKuhnLoadLiftLp_right_inverse
#check @Carleman.cartesianKuhnMoment_surjective
#print axioms Carleman.cartesianKuhnMoment_surjective

#check @Carleman.cartesianKuhnReconstruction
#print axioms Carleman.cartesianKuhnReconstruction
#check @Carleman.cartesianKuhnReconstruction_on_cell
#print axioms Carleman.cartesianKuhnReconstruction_on_cell
#check @Carleman.cartesianKuhnReconstruction_continuous
#print axioms Carleman.cartesianKuhnReconstruction_continuous
#check @Carleman.cartesianKuhnReconstruction_compact
#print axioms Carleman.cartesianKuhnReconstruction_compact
#check @Carleman.cartesianKuhnReconstruction_memLp
#print axioms Carleman.cartesianKuhnReconstruction_memLp
#check @Carleman.cartesianKuhnReconstruction_sq_integrable
#print axioms Carleman.cartesianKuhnReconstruction_sq_integrable
#check @Carleman.integral_simplexLoadPolynomial
#print axioms Carleman.integral_simplexLoadPolynomial
#check @Carleman.integral_simplexLoadPolynomial_sq
#print axioms Carleman.integral_simplexLoadPolynomial_sq
#check @Carleman.integral_simplexLoadPolynomial_sq_le
#print axioms Carleman.integral_simplexLoadPolynomial_sq_le
#check @Carleman.cartesianInteriorData_sq
#print axioms Carleman.cartesianInteriorData_sq
#check @Carleman.cartesianInteriorData_zero_compl
#print axioms Carleman.cartesianInteriorData_zero_compl
#check @Carleman.cartesianKuhnLoadCoefficients_interiorData
#print axioms Carleman.cartesianKuhnLoadCoefficients_interiorData
#check @Carleman.cartesianKuhn_vertex_mass
#print axioms Carleman.cartesianKuhn_vertex_mass
#check @Carleman.cartesianKuhn_vertex_mass_assembly
#print axioms Carleman.cartesianKuhn_vertex_mass_assembly
#check @Carleman.cartesianKuhn_vertex_mass_sq_assembly
#print axioms Carleman.cartesianKuhn_vertex_mass_sq_assembly
#check @Carleman.cartesianKuhnReconstruction_cell_sq_bounds
#print axioms Carleman.cartesianKuhnReconstruction_cell_sq_bounds
#check @Carleman.cartesianKuhnReconstruction_sq_bounds
#print axioms Carleman.cartesianKuhnReconstruction_sq_bounds
#check @Carleman.cartesianKuhnLoadLift_cell_sq_bound
#print axioms Carleman.cartesianKuhnLoadLift_cell_sq_bound
#check @Carleman.cartesianKuhnLoadLift_sq_bound
#print axioms Carleman.cartesianKuhnLoadLift_sq_bound
#check @Carleman.cartesianKuhnReconstructionLp
#print axioms Carleman.cartesianKuhnReconstructionLp
#check @Carleman.cartesianKuhnReconstructionLp_ae
#print axioms Carleman.cartesianKuhnReconstructionLp_ae
#check @Carleman.cartesianKuhnReconstructionLp_norm_sq
#print axioms Carleman.cartesianKuhnReconstructionLp_norm_sq
#check @Carleman.cartesianKuhnReconstructionLp_norm_sq_bounds
#print axioms Carleman.cartesianKuhnReconstructionLp_norm_sq_bounds
#check @Carleman.cartesianKuhnLoadLiftLp_norm_sq_bound
#print axioms Carleman.cartesianKuhnLoadLiftLp_norm_sq_bound

#check @Carleman.simplex_continuous_memLp
#print axioms Carleman.simplex_continuous_memLp
#check @Carleman.simplex_continuous_weighted_integrable
#print axioms Carleman.simplex_continuous_weighted_integrable
#check @Carleman.simplex_weighted_sq_anchor
#print axioms Carleman.simplex_weighted_sq_anchor
#check @Carleman.weighted_coefficient_sq_anchor
#print axioms Carleman.weighted_coefficient_sq_anchor
#check @Carleman.simplexNodal_sq_lumped_bounds
#print axioms Carleman.simplexNodal_sq_lumped_bounds
#check @Carleman.simplex_weighted_reconstruction_bounds
#print axioms Carleman.simplex_weighted_reconstruction_bounds
#check @Carleman.simplex_weighted_load_bound
#print axioms Carleman.simplex_weighted_load_bound
#check @Carleman.closedCoordinateBox_diameter_bound
#print axioms Carleman.closedCoordinateBox_diameter_bound
#check @Carleman.cartesianKuhnSimplex_dist_le
#print axioms Carleman.cartesianKuhnSimplex_dist_le
#check @Carleman.cartesianKuhn_allowedWeight_comparison
#print axioms Carleman.cartesianKuhn_allowedWeight_comparison
#check @Carleman.cartesianInteriorData_weight
#print axioms Carleman.cartesianInteriorData_weight
#check @Carleman.cartesianKuhn_weighted_mass_assembly
#print axioms Carleman.cartesianKuhn_weighted_mass_assembly
#check @Carleman.BoundedMultiplier.integrable_scalar_density_ae
#print axioms Carleman.BoundedMultiplier.integrable_scalar_density_ae
#check @Carleman.BoundedMultiplier.seminorm_sq_scalar_ae
#print axioms Carleman.BoundedMultiplier.seminorm_sq_scalar_ae
#check @Carleman.cartesianKuhn_weighted_reconstruction_cell_bounds
#print axioms Carleman.cartesianKuhn_weighted_reconstruction_cell_bounds
#check @Carleman.cartesianKuhn_weighted_load_cell_bound
#print axioms Carleman.cartesianKuhn_weighted_load_cell_bound
#check @Carleman.cartesianKuhn_weighted_norm_bounds
#print axioms Carleman.cartesianKuhn_weighted_norm_bounds
#check @Carleman.allowed_weight_cartesianKuhn_stability
#print axioms Carleman.allowed_weight_cartesianKuhn_stability

#check @Carleman.cartesianKuhnMoment_local_integral
#print axioms Carleman.cartesianKuhnMoment_local_integral
#check @Carleman.cartesianKuhnMoment_local_sq_bound
#print axioms Carleman.cartesianKuhnMoment_local_sq_bound
#check @Carleman.cartesianKuhnMoment_local_congr
#print axioms Carleman.cartesianKuhnMoment_local_congr
#check @Carleman.cartesianKuhnProjection
#print axioms Carleman.cartesianKuhnProjection
#check @Carleman.cartesianKuhnProjectionLp
#print axioms Carleman.cartesianKuhnProjectionLp
#check @Carleman.cartesianKuhn_cell_volume_le
#print axioms Carleman.cartesianKuhn_cell_volume_le
#check @Carleman.cartesianKuhnProjection_local_sq_bound
#print axioms Carleman.cartesianKuhnProjection_local_sq_bound
#check @Carleman.cartesianKuhnProjection_local_congr
#print axioms Carleman.cartesianKuhnProjection_local_congr
#check @Carleman.cartesianKuhnProjection_local_norm_bound
#print axioms Carleman.cartesianKuhnProjection_local_norm_bound
#check @Carleman.cartesianClippedPatchLower
#print axioms Carleman.cartesianClippedPatchLower
#check @Carleman.cartesianClippedPatchUpper
#print axioms Carleman.cartesianClippedPatchUpper
#check @Carleman.cartesianClippedPatch
#print axioms Carleman.cartesianClippedPatch
#check @Carleman.cartesianClippedPatch_eq_box
#print axioms Carleman.cartesianClippedPatch_eq_box
#check @Carleman.cartesianClippedPatch_width_bounds
#print axioms Carleman.cartesianClippedPatch_width_bounds
#check @Carleman.cartesianClippedPatch_isOpen
#print axioms Carleman.cartesianClippedPatch_isOpen
#check @Carleman.cartesianClippedPatch_subset_domain
#print axioms Carleman.cartesianClippedPatch_subset_domain
#check @Carleman.cartesianClippedPatch_contains_cell
#print axioms Carleman.cartesianClippedPatch_contains_cell
#check @Carleman.cartesianClippedPatch_multiplicity_le
#print axioms Carleman.cartesianClippedPatch_multiplicity_le
#check @Carleman.cartesianKuhnHat_support_subset_clippedPatch
#print axioms Carleman.cartesianKuhnHat_support_subset_clippedPatch
#check @Carleman.cartesianKuhnProjection_patch_sq_bound
#print axioms Carleman.cartesianKuhnProjection_patch_sq_bound
#check @Carleman.cartesianKuhnProjection_patch_norm_bound
#print axioms Carleman.cartesianKuhnProjection_patch_norm_bound
#check @Carleman.cartesianKuhnProjection_patch_congr
#print axioms Carleman.cartesianKuhnProjection_patch_congr

#check @Carleman.cartesianGridPoint_interior_index
#print axioms Carleman.cartesianGridPoint_interior_index
#check @Carleman.cartesianFiniteSimplex_interior_vertex
#print axioms Carleman.cartesianFiniteSimplex_interior_vertex
#check @Carleman.cartesianKuhnMoment_affine
#print axioms Carleman.cartesianKuhnMoment_affine
#check @Carleman.cartesianKuhnProjection_affine_on_cell
#print axioms Carleman.cartesianKuhnProjection_affine_on_cell
#check @Carleman.cartesianKuhnMoment_sub
#print axioms Carleman.cartesianKuhnMoment_sub
#check @Carleman.cartesianKuhnProjection_sub
#print axioms Carleman.cartesianKuhnProjection_sub
#check @Carleman.cartesianFiniteSimplex_subset_closedPatch
#print axioms Carleman.cartesianFiniteSimplex_subset_closedPatch
#check @Carleman.cartesianClosedPatch_subset_closedDomain
#print axioms Carleman.cartesianClosedPatch_subset_closedDomain
#check @Carleman.cartesianClippedPhysicalFaces
#print axioms Carleman.cartesianClippedPhysicalFaces
#check @Carleman.cartesianClippedPhysicalFaces_frontier
#print axioms Carleman.cartesianClippedPhysicalFaces_frontier
#check @Carleman.cartesianCell_boundary_in_physicalFace
#print axioms Carleman.cartesianCell_boundary_in_physicalFace
#check @Carleman.cartesianPhysicalFace_zero_on_boundaryCell
#print axioms Carleman.cartesianPhysicalFace_zero_on_boundaryCell
#check @Carleman.cartesianKuhnProjection_physical_affine
#print axioms Carleman.cartesianKuhnProjection_physical_affine
#check @Carleman.cartesianKuhn_h2_local_reproduced_affine
#print axioms Carleman.cartesianKuhn_h2_local_reproduced_affine

#check @Carleman.coordinatePermutation_symm_norm
#print axioms Carleman.coordinatePermutation_symm_norm
#check @Carleman.cartesianKuhn_inverse_map_bound
#print axioms Carleman.cartesianKuhn_inverse_map_bound
#check @Carleman.cartesianKuhn_uniform_inverse
#print axioms Carleman.cartesianKuhn_uniform_inverse
#check @Carleman.cartesianFiniteSimplex_uniform_inverse
#print axioms Carleman.cartesianFiniteSimplex_uniform_inverse
#check @Carleman.cartesianKuhnReconstruction_eq_nodal
#print axioms Carleman.cartesianKuhnReconstruction_eq_nodal
#check @Carleman.cartesianKuhnReconstructionLp_eq_nodal
#print axioms Carleman.cartesianKuhnReconstructionLp_eq_nodal
#check @Carleman.cartesianKuhnReconstructionLp_mem_dirichlet
#print axioms Carleman.cartesianKuhnReconstructionLp_mem_dirichlet
#check @Carleman.cartesianKuhnReconstructionJet
#print axioms Carleman.cartesianKuhnReconstructionJet
#check @Carleman.cartesianKuhnReconstructionJet_value
#print axioms Carleman.cartesianKuhnReconstructionJet_value
#check @Carleman.cartesianKuhnReconstructionJet_mem_dirichlet
#print axioms Carleman.cartesianKuhnReconstructionJet_mem_dirichlet
#check @Carleman.cartesianKuhnReconstructionJet_gradient_on_cell
#print axioms Carleman.cartesianKuhnReconstructionJet_gradient_on_cell
#check @Carleman.cartesianKuhnReconstruction_cell_norm
#print axioms Carleman.cartesianKuhnReconstruction_cell_norm
#check @Carleman.cartesianKuhnReconstructionJet_cell_gradient_norm
#print axioms Carleman.cartesianKuhnReconstructionJet_cell_gradient_norm
#check @Carleman.cartesianKuhnReconstruction_weak_inverse
#print axioms Carleman.cartesianKuhnReconstruction_weak_inverse
#check @Carleman.cartesianKuhnProjectionJet
#print axioms Carleman.cartesianKuhnProjectionJet
#check @Carleman.cartesianKuhnProjectionJet_value
#print axioms Carleman.cartesianKuhnProjectionJet_value
#check @Carleman.cartesianKuhnProjection_local_gradient_bound
#print axioms Carleman.cartesianKuhnProjection_local_gradient_bound

#check @Carleman.WeakSobolevJet.restrictSubdomain_eq_of_value_ae
#print axioms Carleman.WeakSobolevJet.restrictSubdomain_eq_of_value_ae
#check @Carleman.SimplicialPartition.field_congr_on_cell
#print axioms Carleman.SimplicialPartition.field_congr_on_cell
#check @Carleman.bochnerL2Norm_mono_measure
#print axioms Carleman.bochnerL2Norm_mono_measure
#check @Carleman.bochnerL2Norm_lp_sub
#print axioms Carleman.bochnerL2Norm_lp_sub
#check @Carleman.cartesianClippedPatch_cell_measure
#print axioms Carleman.cartesianClippedPatch_cell_measure
#check @Carleman.cartesianKuhnProjectionJet_ae
#print axioms Carleman.cartesianKuhnProjectionJet_ae
#check @Carleman.cartesianKuhnProjectionJet_sub
#print axioms Carleman.cartesianKuhnProjectionJet_sub
#check @Carleman.cartesianKuhnErrorJet
#print axioms Carleman.cartesianKuhnErrorJet
#check @Carleman.cartesianKuhnErrorJet_sub
#print axioms Carleman.cartesianKuhnErrorJet_sub
#check @Carleman.cartesianKuhnErrorJet_value_local_invariant
#print axioms Carleman.cartesianKuhnErrorJet_value_local_invariant
#check @Carleman.cartesianKuhnErrorJet_field_local_invariant
#print axioms Carleman.cartesianKuhnErrorJet_field_local_invariant
#check @Carleman.cartesianKuhnErrorJet_local_stability
#print axioms Carleman.cartesianKuhnErrorJet_local_stability
#check @Carleman.cartesianKuhn_h2_local_error
#print axioms Carleman.cartesianKuhn_h2_local_error

#check @Carleman.BoundedMultiplier.bochner_map_restrict
#print axioms Carleman.BoundedMultiplier.bochner_map_restrict
#check @Carleman.BoundedMultiplier.bochner_map_le_anchor
#print axioms Carleman.BoundedMultiplier.bochner_map_le_anchor
#check @Carleman.BoundedMultiplier.bochner_le_map_anchor
#print axioms Carleman.BoundedMultiplier.bochner_le_map_anchor
#check @Carleman.cartesianKuhn_h2_weighted_local_error
#print axioms Carleman.cartesianKuhn_h2_weighted_local_error
#check @Carleman.cartesianKuhn_error_assembly
#print axioms Carleman.cartesianKuhn_error_assembly
#check @Carleman.allowed_weight_cartesianKuhn_h2_error
#print axioms Carleman.allowed_weight_cartesianKuhn_h2_error
#check @Carleman.allowed_weight_cartesianKuhn_approximation
#print axioms Carleman.allowed_weight_cartesianKuhn_approximation

#check @Carleman.cartesianKuhnNodalDerivative_basis
#print axioms Carleman.cartesianKuhnNodalDerivative_basis
#check @Carleman.derivativeOneFiber_inner
#print axioms Carleman.derivativeOneFiber_inner
#check @Carleman.cartesianKuhnNodalGradient_inner
#print axioms Carleman.cartesianKuhnNodalGradient_inner
#check @Carleman.cartesianKuhnNodalGradientLp_inner
#print axioms Carleman.cartesianKuhnNodalGradientLp_inner
#check @Carleman.cartesianKuhnCellDifference
#print axioms Carleman.cartesianKuhnCellDifference
#check @Carleman.cartesianKuhnReconstructionJet_coordinate_on_cell
#print axioms Carleman.cartesianKuhnReconstructionJet_coordinate_on_cell
#check @Carleman.cartesianKuhnReconstructionJet_cell_energy
#print axioms Carleman.cartesianKuhnReconstructionJet_cell_energy
#check @Carleman.cartesianKuhnReconstruction_weakGradientPairing_cells
#print axioms Carleman.cartesianKuhnReconstruction_weakGradientPairing_cells
#check @Carleman.cartesianKuhnReconstruction_scalarForm_cells
#print axioms Carleman.cartesianKuhnReconstruction_scalarForm_cells

#check @Carleman.finRotate_val_step
#print axioms Carleman.finRotate_val_step
#check @Carleman.cartesian_sum_face_zero_shift
#print axioms Carleman.cartesian_sum_face_zero_shift
#check @Carleman.cartesianLatticeData
#print axioms Carleman.cartesianLatticeData
#check @Carleman.cartesianLatticeData_zero_face
#print axioms Carleman.cartesianLatticeData_zero_face
#check @Carleman.cartesianLatticeSuccessor
#print axioms Carleman.cartesianLatticeSuccessor
#check @Carleman.cartesianAxisDifference
#print axioms Carleman.cartesianAxisDifference
#check @Carleman.cartesianAxisDifference_zero_transverse
#print axioms Carleman.cartesianAxisDifference_zero_transverse
#check @Carleman.kuhnVertexIndex_succ_eq_axis
#print axioms Carleman.kuhnVertexIndex_succ_eq_axis
#check @Carleman.cartesianKuhnCellDifference_eq_axis
#print axioms Carleman.cartesianKuhnCellDifference_eq_axis
#check @Carleman.cartesianKuhn_step_sum
#print axioms Carleman.cartesianKuhn_step_sum
#check @Carleman.cartesianKuhn_permutation_step_sum
#print axioms Carleman.cartesianKuhn_permutation_step_sum
#check @Carleman.cartesianKuhnReconstruction_weakGradientPairing_edges
#print axioms Carleman.cartesianKuhnReconstruction_weakGradientPairing_edges
#check @Carleman.cartesianKuhnReconstruction_scalarForm_edges
#print axioms Carleman.cartesianKuhnReconstruction_scalarForm_edges

#check @Carleman.cartesianInteriorToBox
#print axioms Carleman.cartesianInteriorToBox
#check @Carleman.cartesianInteriorToBox_injective
#print axioms Carleman.cartesianInteriorToBox_injective
#check @Carleman.cartesian_sum_zero_faces_to_interior
#print axioms Carleman.cartesian_sum_zero_faces_to_interior
#check @Carleman.cartesianLatticePredecessor
#print axioms Carleman.cartesianLatticePredecessor
#check @Carleman.cartesianLatticePredecessor_successor
#print axioms Carleman.cartesianLatticePredecessor_successor
#check @Carleman.cartesian_sum_axis_shift
#print axioms Carleman.cartesian_sum_axis_shift
#check @Carleman.cartesian_sum_axis_by_parts
#print axioms Carleman.cartesian_sum_axis_by_parts
#check @Carleman.cartesianPhysicalInner
#print axioms Carleman.cartesianPhysicalInner
#check @Carleman.cartesianFiniteDifferenceLaplacian
#print axioms Carleman.cartesianFiniteDifferenceLaplacian
#check @Carleman.cartesianLatticeData_at_interior
#print axioms Carleman.cartesianLatticeData_at_interior
#check @Carleman.cartesianAxisDifference_sum_by_parts
#print axioms Carleman.cartesianAxisDifference_sum_by_parts
#check @Carleman.cartesianFiniteDifferenceLaplacian_pairing_edges
#print axioms Carleman.cartesianFiniteDifferenceLaplacian_pairing_edges
#check @Carleman.cartesianFiniteDifferenceLaplacian_weak_stiffness
#print axioms Carleman.cartesianFiniteDifferenceLaplacian_weak_stiffness
#check @Carleman.cartesianFiniteDifferenceLaplacian_stiffness
#print axioms Carleman.cartesianFiniteDifferenceLaplacian_stiffness

#check @Carleman.cartesianNodalMultiplier
#print axioms Carleman.cartesianNodalMultiplier
#check @Carleman.cartesianSquaredWeightTest
#print axioms Carleman.cartesianSquaredWeightTest
#check @Carleman.cartesianWeightedNodeEnergy
#print axioms Carleman.cartesianWeightedNodeEnergy
#check @Carleman.cartesianNodalMultiplier_selfadjoint
#print axioms Carleman.cartesianNodalMultiplier_selfadjoint
#check @Carleman.cartesianSquaredWeightTest_pairing
#print axioms Carleman.cartesianSquaredWeightTest_pairing
#check @Carleman.cartesianWeightedNodeEnergy_nonneg
#print axioms Carleman.cartesianWeightedNodeEnergy_nonneg
#check @Carleman.cartesianWeightedNodeEnergy_eq_zero_iff
#print axioms Carleman.cartesianWeightedNodeEnergy_eq_zero_iff
#check @Carleman.cartesianSquaredWeightTest_positive
#print axioms Carleman.cartesianSquaredWeightTest_positive
#check @Carleman.cartesianSquaredWeightTest_inverse_energy
#print axioms Carleman.cartesianSquaredWeightTest_inverse_energy
#check @Carleman.cartesianInteriorData_multiplier
#print axioms Carleman.cartesianInteriorData_multiplier
#check @Carleman.cartesianKuhnReconstruction_multiplier_nodal
#print axioms Carleman.cartesianKuhnReconstruction_multiplier_nodal
#check @Carleman.cartesianKuhnReconstructionLp_multiplier_nodal
#print axioms Carleman.cartesianKuhnReconstructionLp_multiplier_nodal
#check @Carleman.cartesianSquaredWeightTest_reconstruction
#print axioms Carleman.cartesianSquaredWeightTest_reconstruction
#check @Carleman.cartesianSquaredWeightTest_residual
#print axioms Carleman.cartesianSquaredWeightTest_residual
#check @Carleman.allowed_weight_cartesian_test_norm
#print axioms Carleman.allowed_weight_cartesian_test_norm

#check @Carleman.finiteDiagonalOperatorFamily
#print axioms Carleman.finiteDiagonalOperatorFamily
#check @Carleman.finiteDiagonalOperatorFamily_apply
#print axioms Carleman.finiteDiagonalOperatorFamily_apply
#check @Carleman.finiteDiagonalOperatorFamily_hasDerivWithinAt
#print axioms Carleman.finiteDiagonalOperatorFamily_hasDerivWithinAt
#check @Carleman.cartesianPhysicalInner_diagonal_bound
#print axioms Carleman.cartesianPhysicalInner_diagonal_bound
#check @Carleman.cartesianAllowedTestOperator
#print axioms Carleman.cartesianAllowedTestOperator
#check @Carleman.cartesianAllowedTestDerivative
#print axioms Carleman.cartesianAllowedTestDerivative
#check @Carleman.cartesianAllowedTestOperator_apply
#print axioms Carleman.cartesianAllowedTestOperator_apply
#check @Carleman.cartesianAllowedTestOperator_hasDerivWithinAt
#print axioms Carleman.cartesianAllowedTestOperator_hasDerivWithinAt
#check @Carleman.cartesianAllowedTestOperator_endpoint
#print axioms Carleman.cartesianAllowedTestOperator_endpoint
#check @Carleman.cartesianAllowedTestDerivative_pairing_bound
#print axioms Carleman.cartesianAllowedTestDerivative_pairing_bound
#check @Carleman.cartesianAllowedTestOperator_periodic
#print axioms Carleman.cartesianAllowedTestOperator_periodic
#check @Carleman.allowed_weight_cartesian_test_time
#print axioms Carleman.allowed_weight_cartesian_test_time

#check @Carleman.simplex_exists_inball
#print axioms Carleman.simplex_exists_inball
#check @Carleman.affineSimplex_contains_ball
#print axioms Carleman.affineSimplex_contains_ball
#check @Carleman.cartesianKuhn_cellDiameter_le
#print axioms Carleman.cartesianKuhn_cellDiameter_le
#check @Carleman.cartesianKuhn_maxDiameter_le
#print axioms Carleman.cartesianKuhn_maxDiameter_le
#check @Carleman.cartesianKuhn_uniform_inballs
#print axioms Carleman.cartesianKuhn_uniform_inballs
#check @Carleman.SimplicialPartition.nodalLp_vertex_eq
#print axioms Carleman.SimplicialPartition.nodalLp_vertex_eq
#check @Carleman.SimplicialPartition.nodalLp_multiplier_congr
#print axioms Carleman.SimplicialPartition.nodalLp_multiplier_congr
#check @Carleman.cartesianKuhnReconstructionLp_mem_conforming
#print axioms Carleman.cartesianKuhnReconstructionLp_mem_conforming

#check @Carleman.allowed_prescribed_nodal_weak_norms
#print axioms Carleman.allowed_prescribed_nodal_weak_norms
#check @Carleman.WeakSobolevJet.weightedNorm_neg
#print axioms Carleman.WeakSobolevJet.weightedNorm_neg
#check @Carleman.heat_nodal_residual_norm_bound
#print axioms Carleman.heat_nodal_residual_norm_bound
#check @Carleman.allowed_prescribed_nodal_superapproximation
#print axioms Carleman.allowed_prescribed_nodal_superapproximation
#check @Carleman.allowed_weight_cartesian_test_superapproximation
#print axioms Carleman.allowed_weight_cartesian_test_superapproximation

#check @Carleman.cartesianObservedState
#print axioms Carleman.cartesianObservedState
#check @Carleman.cartesianObservedState_apply
#print axioms Carleman.cartesianObservedState_apply
#check @Carleman.cartesianKuhnHat_support_dist
#print axioms Carleman.cartesianKuhnHat_support_dist
#check @Carleman.cartesianKuhnReconstruction_observed_eq
#print axioms Carleman.cartesianKuhnReconstruction_observed_eq
#check @Carleman.CartesianObservationIndex
#print axioms Carleman.CartesianObservationIndex
#check @Carleman.cartesianControlRestriction
#print axioms Carleman.cartesianControlRestriction
#check @Carleman.cartesianControlExtension
#print axioms Carleman.cartesianControlExtension
#check @Carleman.cartesianControlPhysicalInner
#print axioms Carleman.cartesianControlPhysicalInner
#check @Carleman.cartesianControlWeightedSq
#print axioms Carleman.cartesianControlWeightedSq
#check @Carleman.cartesianControlRestriction_extension
#print axioms Carleman.cartesianControlRestriction_extension
#check @Carleman.cartesianControlExtension_restriction
#print axioms Carleman.cartesianControlExtension_restriction
#check @Carleman.cartesianControlExtension_pairing
#print axioms Carleman.cartesianControlExtension_pairing
#check @Carleman.cartesianObservedState_weighted_energy
#print axioms Carleman.cartesianObservedState_weighted_energy
#check @Carleman.cartesianKuhnReconstructionLp_observed_eq
#print axioms Carleman.cartesianKuhnReconstructionLp_observed_eq
#check @Carleman.allowed_weight_cartesian_observation
#print axioms Carleman.allowed_weight_cartesian_observation

#check @Carleman.PhysicalFiniteSpace
#print axioms Carleman.PhysicalFiniteSpace
#check @Carleman.PhysicalFiniteSpace.valuesEquiv
#print axioms Carleman.PhysicalFiniteSpace.valuesEquiv
#check @Carleman.PhysicalFiniteSpace.core
#print axioms Carleman.PhysicalFiniteSpace.core
#check @Carleman.PhysicalFiniteSpace.inner_eq
#print axioms Carleman.PhysicalFiniteSpace.inner_eq
#check @Carleman.PhysicalFiniteSpace.norm_sq
#print axioms Carleman.PhysicalFiniteSpace.norm_sq
#check @Carleman.PhysicalFiniteSpace.norm_eq
#print axioms Carleman.PhysicalFiniteSpace.norm_eq
#check @Carleman.PhysicalFiniteSpace.multiplier
#print axioms Carleman.PhysicalFiniteSpace.multiplier
#check @Carleman.PhysicalFiniteSpace.multiplier_apply
#print axioms Carleman.PhysicalFiniteSpace.multiplier_apply
#check @Carleman.PhysicalFiniteSpace.multiplier_norm_sq
#print axioms Carleman.PhysicalFiniteSpace.multiplier_norm_sq
#check @Carleman.CartesianPhysicalState
#print axioms Carleman.CartesianPhysicalState
#check @Carleman.CartesianPhysicalControl
#print axioms Carleman.CartesianPhysicalControl
#check @Carleman.cartesianPhysicalState_inner
#print axioms Carleman.cartesianPhysicalState_inner
#check @Carleman.cartesianPhysicalControl_inner
#print axioms Carleman.cartesianPhysicalControl_inner
#check @Carleman.cartesianPhysicalControlExtension
#print axioms Carleman.cartesianPhysicalControlExtension
#check @Carleman.cartesianPhysicalControlRestriction
#print axioms Carleman.cartesianPhysicalControlRestriction
#check @Carleman.cartesianPhysicalControlExtension_values
#print axioms Carleman.cartesianPhysicalControlExtension_values
#check @Carleman.cartesianPhysicalControlRestriction_values
#print axioms Carleman.cartesianPhysicalControlRestriction_values
#check @Carleman.cartesianPhysicalControl_adjoint
#print axioms Carleman.cartesianPhysicalControl_adjoint
#check @Carleman.cartesianPhysicalStateWeight
#print axioms Carleman.cartesianPhysicalStateWeight
#check @Carleman.cartesianPhysicalControlWeight
#print axioms Carleman.cartesianPhysicalControlWeight
#check @Carleman.cartesianPhysicalStateWeight_norm_sq
#print axioms Carleman.cartesianPhysicalStateWeight_norm_sq
#check @Carleman.cartesianPhysicalControlWeight_norm_sq
#print axioms Carleman.cartesianPhysicalControlWeight_norm_sq
#check @Carleman.allowed_weight_cartesian_hilbert_observation
#print axioms Carleman.allowed_weight_cartesian_hilbert_observation

#check @Carleman.cartesianKuhnReconstructionLp_eq_sum
#print axioms Carleman.cartesianKuhnReconstructionLp_eq_sum
#check @Carleman.cartesianPhysicalReconstructionLp
#print axioms Carleman.cartesianPhysicalReconstructionLp
#check @Carleman.cartesianPhysicalReconstructionLp_apply
#print axioms Carleman.cartesianPhysicalReconstructionLp_apply
#check @Carleman.cartesianPhysicalReconstructionLp_injective
#print axioms Carleman.cartesianPhysicalReconstructionLp_injective
#check @Carleman.cartesianKuhnMoment_eq_inner
#print axioms Carleman.cartesianKuhnMoment_eq_inner
#check @Carleman.cartesianKuhnMoment_pairing
#print axioms Carleman.cartesianKuhnMoment_pairing
#check @Carleman.cartesianPhysicalMoment
#print axioms Carleman.cartesianPhysicalMoment
#check @Carleman.cartesianPhysicalMoment_values
#print axioms Carleman.cartesianPhysicalMoment_values
#check @Carleman.cartesianPhysicalMoment_load_right_inverse
#print axioms Carleman.cartesianPhysicalMoment_load_right_inverse
#check @Carleman.cartesianReconstruction
#print axioms Carleman.cartesianReconstruction
#check @Carleman.cartesianReconstruction_RH
#print axioms Carleman.cartesianReconstruction_RH
#check @Carleman.cartesianReconstruction_J_values
#print axioms Carleman.cartesianReconstruction_J_values
#check @Carleman.cartesianReconstruction_QH
#print axioms Carleman.cartesianReconstruction_QH
#check @Carleman.cartesianReconstruction_G_values
#print axioms Carleman.cartesianReconstruction_G_values
#check @Carleman.cartesianReconstruction_injective
#print axioms Carleman.cartesianReconstruction_injective
#check @Carleman.cartesianLoadInterface
#print axioms Carleman.cartesianLoadInterface
#check @Carleman.cartesianLoadInterface_Γ
#print axioms Carleman.cartesianLoadInterface_Γ
#check @Carleman.cartesianLoadInterface_lift
#print axioms Carleman.cartesianLoadInterface_lift
#check @Carleman.cartesianLoadInterface_right_inverse
#print axioms Carleman.cartesianLoadInterface_right_inverse

#check @Carleman.PhysicalFiniteSpace.multiplierFamily
#print axioms Carleman.PhysicalFiniteSpace.multiplierFamily
#check @Carleman.PhysicalFiniteSpace.multiplierFamily_apply
#print axioms Carleman.PhysicalFiniteSpace.multiplierFamily_apply
#check @Carleman.PhysicalFiniteSpace.multiplierFamily_hasDerivWithinAt
#print axioms Carleman.PhysicalFiniteSpace.multiplierFamily_hasDerivWithinAt
#check @Carleman.cartesianPhysicalTest
#print axioms Carleman.cartesianPhysicalTest
#check @Carleman.cartesianPhysicalTestDerivative
#print axioms Carleman.cartesianPhysicalTestDerivative
#check @Carleman.cartesianPhysicalTest_values
#print axioms Carleman.cartesianPhysicalTest_values
#check @Carleman.cartesianPhysicalTestDerivative_values
#print axioms Carleman.cartesianPhysicalTestDerivative_values
#check @Carleman.cartesianPhysicalTest_hasDerivWithinAt
#print axioms Carleman.cartesianPhysicalTest_hasDerivWithinAt
#check @Carleman.cartesianPhysicalTest_pairing_hasDerivWithinAt
#print axioms Carleman.cartesianPhysicalTest_pairing_hasDerivWithinAt
#check @Carleman.cartesianPhysicalTest_endpoint
#print axioms Carleman.cartesianPhysicalTest_endpoint
#check @Carleman.cartesianPhysicalTest_symmetric
#print axioms Carleman.cartesianPhysicalTest_symmetric
#check @Carleman.cartesianPhysicalTest_pairing
#print axioms Carleman.cartesianPhysicalTest_pairing
#check @Carleman.cartesianPhysicalTest_nonneg
#print axioms Carleman.cartesianPhysicalTest_nonneg
#check @Carleman.cartesian_weightedTest_interface
#print axioms Carleman.cartesian_weightedTest_interface

#check @Carleman.cartesianInteriorData_add
#print axioms Carleman.cartesianInteriorData_add
#check @Carleman.cartesianInteriorData_smul
#print axioms Carleman.cartesianInteriorData_smul
#check @Carleman.cartesianPhysicalLaplacian
#print axioms Carleman.cartesianPhysicalLaplacian
#check @Carleman.cartesianPhysicalLaplacian_values
#print axioms Carleman.cartesianPhysicalLaplacian_values
#check @Carleman.cartesianPhysicalLaplacian_stiffness
#print axioms Carleman.cartesianPhysicalLaplacian_stiffness
#check @Carleman.cartesianPhysicalLaplacian_symmetric
#print axioms Carleman.cartesianPhysicalLaplacian_symmetric
#check @Carleman.cartesianPhysicalLaplacian_adjoint
#print axioms Carleman.cartesianPhysicalLaplacian_adjoint
#check @Carleman.cartesianPhysicalLaplacian_nonneg
#print axioms Carleman.cartesianPhysicalLaplacian_nonneg
#check @Carleman.cartesianStateSeminorm
#print axioms Carleman.cartesianStateSeminorm
#check @Carleman.cartesianControlSeminorm
#print axioms Carleman.cartesianControlSeminorm
#check @Carleman.cartesianStateSeminorm_apply
#print axioms Carleman.cartesianStateSeminorm_apply
#check @Carleman.cartesianControlSeminorm_apply
#print axioms Carleman.cartesianControlSeminorm_apply
#check @Carleman.cartesianStateSeminorm_definite
#print axioms Carleman.cartesianStateSeminorm_definite
#check @Carleman.cartesianControlSeminorm_definite
#print axioms Carleman.cartesianControlSeminorm_definite
#check @Carleman.cartesianStateSeminorm_weight_scale
#print axioms Carleman.cartesianStateSeminorm_weight_scale
#check @Carleman.cartesianControlSeminorm_weight_scale
#print axioms Carleman.cartesianControlSeminorm_weight_scale
#check @Carleman.cartesianPhysicalTest_positive
#print axioms Carleman.cartesianPhysicalTest_positive
#check @Carleman.cartesianReconstruction_norm_sq_bounds
#print axioms Carleman.cartesianReconstruction_norm_sq_bounds
#check @Carleman.allowed_weight_cartesian_physical_stability
#print axioms Carleman.allowed_weight_cartesian_physical_stability

#check @Carleman.cartesian_heat_error_from_b2
#print axioms Carleman.cartesian_heat_error_from_b2
#check @Carleman.cartesian_weightedApproximation_interface
#print axioms Carleman.cartesian_weightedApproximation_interface

#check @Carleman.cartesianErrorScales
#print axioms Carleman.cartesianErrorScales
#check @Carleman.cartesian_numericalData
#print axioms Carleman.cartesian_numericalData

#check @Carleman.full_p1_weightedTest_interface
#print axioms Carleman.full_p1_weightedTest_interface

#check @Carleman.smooth_first_taylor_integral
#print axioms Carleman.smooth_first_taylor_integral
#check @Carleman.integral_convex_segment_jacobian_le
#print axioms Carleman.integral_convex_segment_jacobian_le
#check @Carleman.convex_segment_norm_integral_sq
#print axioms Carleman.convex_segment_norm_integral_sq
#check @Carleman.convex_segment_lowdim_kernel_bound
#print axioms Carleman.convex_segment_lowdim_kernel_bound
#check @Carleman.integrableOn_unit_inv_sqrt
#print axioms Carleman.integrableOn_unit_inv_sqrt
#check @Carleman.integral_unit_inv_sqrt
#print axioms Carleman.integral_unit_inv_sqrt
#check @Carleman.convex_segment_lowdim_integral_bound
#print axioms Carleman.convex_segment_lowdim_integral_bound
#check @Carleman.smooth_first_taylor_contracted
#print axioms Carleman.smooth_first_taylor_contracted
#check @Carleman.smooth_taylor_remainder_norm_bound
#print axioms Carleman.smooth_taylor_remainder_norm_bound
#check @Carleman.convex_smooth_averaged_taylor_error
#print axioms Carleman.convex_smooth_averaged_taylor_error
#check @Carleman.averagedTaylorPolynomial
#print axioms Carleman.averagedTaylorPolynomial
#check @Carleman.averagedTaylorPolynomial_apply
#print axioms Carleman.averagedTaylorPolynomial_apply
#check @Carleman.averagedTaylorPolynomial_error
#print axioms Carleman.averagedTaylorPolynomial_error
#check @Carleman.simplexNodal_smooth_h2_value_error
#print axioms Carleman.simplexNodal_smooth_h2_value_error
#check @Carleman.simplexNodal_smooth_h2_value_integral
#print axioms Carleman.simplexNodal_smooth_h2_value_integral

#check @Carleman.derivativeOneFiber_norm_sq
#print axioms Carleman.derivativeOneFiber_norm_sq
#check @Carleman.smooth_directional_gradient_bound
#print axioms Carleman.smooth_directional_gradient_bound
#check @Carleman.averagedTaylorPolynomial_derivative
#print axioms Carleman.averagedTaylorPolynomial_derivative
#check @Carleman.averagedTaylorPolynomial_gradient_integral
#print axioms Carleman.averagedTaylorPolynomial_gradient_integral
#check @Carleman.simplexNodal_smooth_h2_gradient_integral
#print axioms Carleman.simplexNodal_smooth_h2_gradient_integral

#check @Carleman.tensorCoordinateBound
#print axioms Carleman.tensorCoordinateBound
#check @Carleman.tensorCoordinateBound_pos
#print axioms Carleman.tensorCoordinateBound_pos
#check @Carleman.tensor_norm_sq_le_coordinate_sum
#print axioms Carleman.tensor_norm_sq_le_coordinate_sum
#check @Carleman.SpatialTest.directionalKernel
#print axioms Carleman.SpatialTest.directionalKernel
#check @Carleman.SpatialTest.directionalKernel_support
#print axioms Carleman.SpatialTest.directionalKernel_support
#check @Carleman.IsWeakSpatialDerivative.mixed_fderiv_convolution_local
#print axioms Carleman.IsWeakSpatialDerivative.mixed_fderiv_convolution_local
#check @Carleman.IsWeakSpatialDerivative.second_tensor_convolution_local
#print axioms Carleman.IsWeakSpatialDerivative.second_tensor_convolution_local
#check @Carleman.mollified_hessian_energy_le
#print axioms Carleman.mollified_hessian_energy_le
#check @Carleman.WeakSobolevJet.mollified_hessian_energy_le
#print axioms Carleman.WeakSobolevJet.mollified_hessian_energy_le
#check @Carleman.WeakSobolevJet.mollified_nodal_value_integral
#print axioms Carleman.WeakSobolevJet.mollified_nodal_value_integral
#check @Carleman.WeakSobolevJet.mollified_nodal_gradient_integral
#print axioms Carleman.WeakSobolevJet.mollified_nodal_gradient_integral

#check @Carleman.l2_square_tendsto_zero_of_ae_of_energy_le
#print axioms Carleman.l2_square_tendsto_zero_of_ae_of_energy_le
#check @Carleman.spatialMollifier_square_error_tendsto
#print axioms Carleman.spatialMollifier_square_error_tendsto
#check @Carleman.spatialMollifier_L2_error_tendsto
#print axioms Carleman.spatialMollifier_L2_error_tendsto
#check @Carleman.spatialMollificationLp
#print axioms Carleman.spatialMollificationLp
#check @Carleman.spatialMollificationLp_ae
#print axioms Carleman.spatialMollificationLp_ae
#check @Carleman.spatialMollificationLp_tendsto
#print axioms Carleman.spatialMollificationLp_tendsto
#check @Carleman.spatialMollifier_L2_error_restrict_tendsto
#print axioms Carleman.spatialMollifier_L2_error_restrict_tendsto
#check @Carleman.IsWeakSpatialDerivative.local_mollification_strong_first
#print axioms Carleman.IsWeakSpatialDerivative.local_mollification_strong_first
#check @Carleman.IsWeakSpatialDerivative.local_mollification_strong_second
#print axioms Carleman.IsWeakSpatialDerivative.local_mollification_strong_second
#check @Carleman.WeakSobolevJet.local_mollification_strong_h2
#print axioms Carleman.WeakSobolevJet.local_mollification_strong_h2

#check @Carleman.continuous_memLp_compact
#print axioms Carleman.continuous_memLp_compact
#check @Carleman.compact_integral_norm_le_l2
#print axioms Carleman.compact_integral_norm_le_l2
#check @Carleman.convex_smooth_h2_point_bound
#print axioms Carleman.convex_smooth_h2_point_bound
#check @Carleman.tensor_norm_le_coordinate_sum
#print axioms Carleman.tensor_norm_le_coordinate_sum
#check @Carleman.tensor_L2_le_coordinate_sum
#print axioms Carleman.tensor_L2_le_coordinate_sum
#check @Carleman.convex_smooth_h2_coordinate_point_bound
#print axioms Carleman.convex_smooth_h2_coordinate_point_bound
#check @Carleman.coordinateDerivative_sub
#print axioms Carleman.coordinateDerivative_sub
#check @Carleman.bochnerL2Norm_sub_le_errors
#print axioms Carleman.bochnerL2Norm_sub_le_errors
#check @Carleman.convex_smooth_h2_uniform_limit
#print axioms Carleman.convex_smooth_h2_uniform_limit
#check @Carleman.coordinateDerivative_one
#print axioms Carleman.coordinateDerivative_one
#check @Carleman.coordinateDerivative_two
#print axioms Carleman.coordinateDerivative_two
#check @Carleman.WeakSobolevJet.exists_local_continuous_representative
#print axioms Carleman.WeakSobolevJet.exists_local_continuous_representative
#check @Carleman.WeakSobolevJet.exists_continuous_representative
#print axioms Carleman.WeakSobolevJet.exists_continuous_representative
#check @Carleman.WeakSobolevJet.continuous_representative_unique
#print axioms Carleman.WeakSobolevJet.continuous_representative_unique

#check @Carleman.scalarAffine_memLp
#print axioms Carleman.scalarAffine_memLp
#check @Carleman.integral_scalarAffine_univ
#print axioms Carleman.integral_scalarAffine_univ
#check @Carleman.scalarAffine_L2_sq
#print axioms Carleman.scalarAffine_L2_sq
#check @Carleman.inwardPullback
#print axioms Carleman.inwardPullback
#check @Carleman.inwardPullback_memLp
#print axioms Carleman.inwardPullback_memLp
#check @Carleman.inwardPullback_L2_le
#print axioms Carleman.inwardPullback_L2_le
#check @Carleman.inwardPoint_tendsto
#print axioms Carleman.inwardPoint_tendsto
#check @Carleman.l2_square_tendsto_zero_of_ae_of_energy_tendsto
#print axioms Carleman.l2_square_tendsto_zero_of_ae_of_energy_tendsto
#check @Carleman.l2_error_tendsto_of_ae_of_energy_tendsto
#print axioms Carleman.l2_error_tendsto_of_ae_of_energy_tendsto
#check @Carleman.inwardPullback_L2_error_tendsto_of_continuous
#print axioms Carleman.inwardPullback_L2_error_tendsto_of_continuous
#check @Carleman.inwardPullback_L2_error_tendsto
#print axioms Carleman.inwardPullback_L2_error_tendsto
#check @Carleman.scalarAffine_iteratedFDeriv
#print axioms Carleman.scalarAffine_iteratedFDeriv
#check @Carleman.inwardPullback_contDiff
#print axioms Carleman.inwardPullback_contDiff
#check @Carleman.coordinateDerivative_inwardPullback
#print axioms Carleman.coordinateDerivative_inwardPullback
#check @Carleman.inwardPullback_L2_error_tendsto_diagonal
#print axioms Carleman.inwardPullback_L2_error_tendsto_diagonal
#check @Carleman.l2_scaled_error_tendsto
#print axioms Carleman.l2_scaled_error_tendsto
#check @Carleman.inwardPullback_scaled_L2_error_tendsto
#print axioms Carleman.inwardPullback_scaled_L2_error_tendsto

#check @Carleman.exists_inward_mollifier_sequence
#print axioms Carleman.exists_inward_mollifier_sequence
#check @Carleman.inwardMollification
#print axioms Carleman.inwardMollification
#check @Carleman.inwardMollification_smooth
#print axioms Carleman.inwardMollification_smooth
#check @Carleman.inwardMollification_scaled_L2_error_tendsto
#print axioms Carleman.inwardMollification_scaled_L2_error_tendsto
#check @Carleman.IsWeakSpatialDerivative.coordinate_one_inwardMollification
#print axioms Carleman.IsWeakSpatialDerivative.coordinate_one_inwardMollification
#check @Carleman.IsWeakSpatialDerivative.coordinate_two_inwardMollification
#print axioms Carleman.IsWeakSpatialDerivative.coordinate_two_inwardMollification
#check @Carleman.WeakSobolevJet.inward_mollification_strong_h2
#print axioms Carleman.WeakSobolevJet.inward_mollification_strong_h2
#check @Carleman.continuousOn_memLp_compact
#print axioms Carleman.continuousOn_memLp_compact
#check @Carleman.l2_limit_ae_eq_of_ae_tendsto
#print axioms Carleman.l2_limit_ae_eq_of_ae_tendsto
#check @Carleman.WeakSobolevJet.inward_mollification_uniform_limit
#print axioms Carleman.WeakSobolevJet.inward_mollification_uniform_limit
#check @Carleman.WeakSobolevJet.exists_closure_continuous_representative
#print axioms Carleman.WeakSobolevJet.exists_closure_continuous_representative
#check @Carleman.WeakSobolevJet.closure_continuous_representative_unique
#print axioms Carleman.WeakSobolevJet.closure_continuous_representative_unique

#check @Carleman.bochnerL2Norm_reverse_triangle
#print axioms Carleman.bochnerL2Norm_reverse_triangle
#check @Carleman.bochnerL2Norm_tendsto_of_error
#print axioms Carleman.bochnerL2Norm_tendsto_of_error
#check @Carleman.l2_square_integral_tendsto_of_error
#print axioms Carleman.l2_square_integral_tendsto_of_error
#check @Carleman.l2_square_bound_of_ae_of_bound_tendsto
#print axioms Carleman.l2_square_bound_of_ae_of_bound_tendsto
#check @Carleman.smooth_hessian_integral_le_coordinate_sum
#print axioms Carleman.smooth_hessian_integral_le_coordinate_sum
#check @Carleman.hessian_coordinate_energy_tendsto
#print axioms Carleman.hessian_coordinate_energy_tendsto
#check @Carleman.simplexNodalInterpolant_tendsto
#print axioms Carleman.simplexNodalInterpolant_tendsto
#check @Carleman.simplexNodal_h2_value_integral_of_limit
#print axioms Carleman.simplexNodal_h2_value_integral_of_limit
#check @Carleman.WeakSobolevJet.exists_smooth_h2_pointwise_approximation
#print axioms Carleman.WeakSobolevJet.exists_smooth_h2_pointwise_approximation
#check @Carleman.derivativeComponent_local_integral_le
#print axioms Carleman.derivativeComponent_local_integral_le
#check @Carleman.WeakSobolevJet.simplex_nodal_value_integral
#print axioms Carleman.WeakSobolevJet.simplex_nodal_value_integral
#check @Carleman.WeakSobolevJet.exists_nodal_value_representative
#print axioms Carleman.WeakSobolevJet.exists_nodal_value_representative

#check @Carleman.l2_error_sub_constant_tendsto
#print axioms Carleman.l2_error_sub_constant_tendsto
#check @Carleman.simplexNodal_affineDerivative_eq
#print axioms Carleman.simplexNodal_affineDerivative_eq
#check @Carleman.simplexNodalDerivative_tendsto
#print axioms Carleman.simplexNodalDerivative_tendsto
#check @Carleman.firstDerivativeFiber_norm_sq
#print axioms Carleman.firstDerivativeFiber_norm_sq
#check @Carleman.firstDerivativeFiber_sub_norm_sq
#print axioms Carleman.firstDerivativeFiber_sub_norm_sq
#check @Carleman.simplexNodal_h2_gradient_integral_of_limit
#print axioms Carleman.simplexNodal_h2_gradient_integral_of_limit
#check @Carleman.derivativeOneFiber_local_sub_integral_eq
#print axioms Carleman.derivativeOneFiber_local_sub_integral_eq
#check @Carleman.WeakSobolevJet.simplex_nodal_gradient_integral
#print axioms Carleman.WeakSobolevJet.simplex_nodal_gradient_integral
#check @Carleman.WeakSobolevJet.exists_nodal_h2_representative
#print axioms Carleman.WeakSobolevJet.exists_nodal_h2_representative

#check @Carleman.memLp_mul_of_ae_bound
#print axioms Carleman.memLp_mul_of_ae_bound
#check @Carleman.bochnerL2Norm_mul_le_of_ae_bound
#print axioms Carleman.bochnerL2Norm_mul_le_of_ae_bound
#check @Carleman.l2_bounded_multiplier_zero_tendsto
#print axioms Carleman.l2_bounded_multiplier_zero_tendsto
#check @Carleman.l2_bounded_multiplier_strong_tendsto
#print axioms Carleman.l2_bounded_multiplier_strong_tendsto
#check @Carleman.memLp_toLp_tendsto_of_L2_error
#print axioms Carleman.memLp_toLp_tendsto_of_L2_error
#check @Carleman.IsWeakSpatialDerivative.of_strong_function_limits
#print axioms Carleman.IsWeakSpatialDerivative.of_strong_function_limits
#check @Carleman.weakSpatialDerivative_of_contDiff
#print axioms Carleman.weakSpatialDerivative_of_contDiff
#check @Carleman.l2_lipschitz_comp_error_tendsto
#print axioms Carleman.l2_lipschitz_comp_error_tendsto
#check @Carleman.IsWeakSpatialDerivative.scalar_chain_rule
#print axioms Carleman.IsWeakSpatialDerivative.scalar_chain_rule

#check @Carleman.exists_smooth_gap_cutoff
#print axioms Carleman.exists_smooth_gap_cutoff
#check @Carleman.weak_zero_gradient_ae_constant
#print axioms Carleman.weak_zero_gradient_ae_constant
#check @Carleman.weak_scalar_gap_on_convex
#print axioms Carleman.weak_scalar_gap_on_convex
#check @Carleman.dirichlet_continuous_zero_on_frontier
#print axioms Carleman.dirichlet_continuous_zero_on_frontier
#check @Carleman.WeakSobolevJet.exists_dirichlet_closure_representative
#print axioms Carleman.WeakSobolevJet.exists_dirichlet_closure_representative

#check @Carleman.SimplicialPartition.nodalSobolevJet_mem_dirichlet
#print axioms Carleman.SimplicialPartition.nodalSobolevJet_mem_dirichlet
#check @Carleman.SimplicialPartition.nodalH2ErrorJet
#print axioms Carleman.SimplicialPartition.nodalH2ErrorJet
#check @Carleman.SimplicialPartition.nodalH2ErrorJet_value
#print axioms Carleman.SimplicialPartition.nodalH2ErrorJet_value
#check @Carleman.SimplicialPartition.nodalH2ErrorJet_mem_dirichlet
#print axioms Carleman.SimplicialPartition.nodalH2ErrorJet_mem_dirichlet
#check @Carleman.SimplicialPartition.nodalH2ErrorJet_value_on_cell
#print axioms Carleman.SimplicialPartition.nodalH2ErrorJet_value_on_cell
#check @Carleman.SimplicialPartition.nodalH2ErrorJet_gradient_on_cell
#print axioms Carleman.SimplicialPartition.nodalH2ErrorJet_gradient_on_cell
#check @Carleman.SimplicialPartition.nodalH2ErrorJet_cell_integral_bounds
#print axioms Carleman.SimplicialPartition.nodalH2ErrorJet_cell_integral_bounds
#check @Carleman.SimplicialPartition.exists_weak_h2_conforming_nodal_error
#print axioms Carleman.SimplicialPartition.exists_weak_h2_conforming_nodal_error

#check @Carleman.BoundedMultiplier.integral_transfer
#print axioms Carleman.BoundedMultiplier.integral_transfer
#check @Carleman.BoundedMultiplier.integral_transfer_memLp
#print axioms Carleman.BoundedMultiplier.integral_transfer_memLp
#check @Carleman.SimplicialPartition.cellWeight
#print axioms Carleman.SimplicialPartition.cellWeight
#check @Carleman.SimplicialPartition.cellWeight_on_cell
#print axioms Carleman.SimplicialPartition.cellWeight_on_cell
#check @Carleman.SimplicialPartition.cellWeight_sq_sum
#print axioms Carleman.SimplicialPartition.cellWeight_sq_sum
#check @Carleman.SimplicialPartition.cellWeight_seminorm_le
#print axioms Carleman.SimplicialPartition.cellWeight_seminorm_le
#check @Carleman.SimplicialPartition.weighted_cell_errors_sum
#print axioms Carleman.SimplicialPartition.weighted_cell_errors_sum
#check @Carleman.SimplicialPartition.weighted_cell_inverse_errors_sum
#print axioms Carleman.SimplicialPartition.weighted_cell_inverse_errors_sum
#check @Carleman.weak_h2_weighted_nodal_approximation
#print axioms Carleman.weak_h2_weighted_nodal_approximation
#check @Carleman.weak_h2_allowed_nodal_approximation
#print axioms Carleman.weak_h2_allowed_nodal_approximation

#check @Carleman.SimplicialPartition.cellWeight_mesh_power_le
#print axioms Carleman.SimplicialPartition.cellWeight_mesh_power_le
#check @Carleman.weak_h2_allowed_projection_approximation
#print axioms Carleman.weak_h2_allowed_projection_approximation
#check @Carleman.full_p1_weightedApproximation_interface
#print axioms Carleman.full_p1_weightedApproximation_interface

#check @Carleman.Physical.restrictRegion_weighted_sq
#print axioms Carleman.Physical.restrictRegion_weighted_sq
#check @Carleman.Physical.conforming_region_weighted_observation
#print axioms Carleman.Physical.conforming_region_weighted_observation
#check @Carleman.Physical.galerkinRegionNumericalData
#print axioms Carleman.Physical.galerkinRegionNumericalData
#check @Carleman.p1ErrorScales
#print axioms Carleman.p1ErrorScales
#check @Carleman.full_p1_numericalData
#print axioms Carleman.full_p1_numericalData

#check @Carleman.exists_inner_of_bounded_test_functional
#print axioms Carleman.exists_inner_of_bounded_test_functional
#check @Carleman.exists_weakSpatialDerivative_of_test_bound
#print axioms Carleman.exists_weakSpatialDerivative_of_test_bound
#check @Carleman.exists_weakSpatialDerivative_iff_test_bound
#print axioms Carleman.exists_weakSpatialDerivative_iff_test_bound
#check @Carleman.exists_weakSpatialDerivative_of_test_limits
#print axioms Carleman.exists_weakSpatialDerivative_of_test_limits
#check @Carleman.exists_weakSpatialDerivative_of_strong_limit_bounded
#print axioms Carleman.exists_weakSpatialDerivative_of_strong_limit_bounded

#check @Carleman.SpatialTest.derivativeTest
#print axioms Carleman.SpatialTest.derivativeTest
#check @Carleman.SpatialTest.derivativeTest_toLp
#print axioms Carleman.SpatialTest.derivativeTest_toLp
#check @Carleman.SpatialTest.derivativeTest_derivativeLp_commute
#print axioms Carleman.SpatialTest.derivativeTest_derivativeLp_commute
#check @Carleman.IsWeakSpatialDerivative.mixed_commute
#print axioms Carleman.IsWeakSpatialDerivative.mixed_commute
#check @Carleman.derivativeFiberInjection
#print axioms Carleman.derivativeFiberInjection
#check @Carleman.derivativeFiberInjection_component
#print axioms Carleman.derivativeFiberInjection_component
#check @Carleman.derivativeFieldAssembly
#print axioms Carleman.derivativeFieldAssembly
#check @Carleman.derivativeFieldAssembly_component
#print axioms Carleman.derivativeFieldAssembly_component
#check @Carleman.derivativeFieldAssembly_norm_sq
#print axioms Carleman.derivativeFieldAssembly_norm_sq
#check @Carleman.secondOrderFields
#print axioms Carleman.secondOrderFields
#check @Carleman.secondOrderJet
#print axioms Carleman.secondOrderJet
#check @Carleman.secondOrderJet_truncate
#print axioms Carleman.secondOrderJet_truncate
#check @Carleman.secondOrderJet_hessian
#print axioms Carleman.secondOrderJet_hessian
#check @Carleman.exists_weakH2_of_gradient_test_bounds
#print axioms Carleman.exists_weakH2_of_gradient_test_bounds
#check @Carleman.exists_weakH2_of_gradient_test_limits
#print axioms Carleman.exists_weakH2_of_gradient_test_limits
#check @Carleman.exists_weakH2_of_strong_H1_limit_bounded
#print axioms Carleman.exists_weakH2_of_strong_H1_limit_bounded

#check @Carleman.exists_hilbert_weak_subsequence
#print axioms Carleman.exists_hilbert_weak_subsequence
#check @Carleman.exists_hilbert_weak_subsequence_in_subspace
#print axioms Carleman.exists_hilbert_weak_subsequence_in_subspace
#check @Carleman.hilbert_weak_tendsto_map
#print axioms Carleman.hilbert_weak_tendsto_map
#check @Carleman.exists_dirichlet_weak_subsequence
#print axioms Carleman.exists_dirichlet_weak_subsequence
#check @Carleman.IsWeakNegativeLaplacian.unique_rhs
#print axioms Carleman.IsWeakNegativeLaplacian.unique_rhs
#check @Carleman.IsWeakNegativeLaplacian.of_weak_gradient_limit
#print axioms Carleman.IsWeakNegativeLaplacian.of_weak_gradient_limit
#check @Carleman.exists_dirichlet_H2_of_bounded_approximants
#print axioms Carleman.exists_dirichlet_H2_of_bounded_approximants

#check @Carleman.SpatialTest.zeroExtendDirichlet_value_ae
#print axioms Carleman.SpatialTest.zeroExtendDirichlet_value_ae
#check @Carleman.WeakSobolevJet.zeroExtendDirichlet_tendsto
#print axioms Carleman.WeakSobolevJet.zeroExtendDirichlet_tendsto
#check @Carleman.WeakSobolevJet.extendDirichlet
#print axioms Carleman.WeakSobolevJet.extendDirichlet
#check @Carleman.WeakSobolevJet.extendDirichlet_value
#print axioms Carleman.WeakSobolevJet.extendDirichlet_value
#check @Carleman.WeakSobolevJet.extendDirichlet_field_norm_le
#print axioms Carleman.WeakSobolevJet.extendDirichlet_field_norm_le
#check @Carleman.WeakSobolevJet.extendDirichlet_test
#print axioms Carleman.WeakSobolevJet.extendDirichlet_test
#check @Carleman.WeakSobolevJet.extendDirichlet_mem
#print axioms Carleman.WeakSobolevJet.extendDirichlet_mem

#check @Carleman.subdomainZeroExtend
#print axioms Carleman.subdomainZeroExtend
#check @Carleman.subdomainZeroExtend_ae
#print axioms Carleman.subdomainZeroExtend_ae
#check @Carleman.subdomainLp_zeroExtend
#print axioms Carleman.subdomainLp_zeroExtend
#check @Carleman.subdomainZeroExtend_norm
#print axioms Carleman.subdomainZeroExtend_norm
#check @Carleman.subdomainZeroExtend_inner
#print axioms Carleman.subdomainZeroExtend_inner
#check @Carleman.SpatialTest.restrictSubdomain_mono
#print axioms Carleman.SpatialTest.restrictSubdomain_mono
#check @Carleman.WeakSobolevJet.extendDirichlet_field
#print axioms Carleman.WeakSobolevJet.extendDirichlet_field
#check @Carleman.WeakSobolevJet.extendDirichlet_field_norm
#print axioms Carleman.WeakSobolevJet.extendDirichlet_field_norm
#check @Carleman.WeakSobolevJet.extendDirichlet_pairing
#print axioms Carleman.WeakSobolevJet.extendDirichlet_pairing
#check @Carleman.WeakSobolevJet.extendDirichlet_poisson_test
#print axioms Carleman.WeakSobolevJet.extendDirichlet_poisson_test
#check @Carleman.subdomainZeroExtend_test_inner
#print axioms Carleman.subdomainZeroExtend_test_inner
#check @Carleman.subdomainZeroExtend_derivativeTest_inner
#print axioms Carleman.subdomainZeroExtend_derivativeTest_inner
#check @Carleman.derivativeComponent_subdomainZeroExtend
#print axioms Carleman.derivativeComponent_subdomainZeroExtend
#check @Carleman.WeakSobolevJet.extendDirichlet_hessian_test
#print axioms Carleman.WeakSobolevJet.extendDirichlet_hessian_test
#check @Carleman.exists_dirichlet_weak_solution
#print axioms Carleman.exists_dirichlet_weak_solution
#check @Carleman.dirichlet_weak_solution_gradient_bound
#print axioms Carleman.dirichlet_weak_solution_gradient_bound
#check @Carleman.dirichlet_weak_solution_energy_bound
#print axioms Carleman.dirichlet_weak_solution_energy_bound
#check @Carleman.dirichlet_subdomain_energy_bound
#print axioms Carleman.dirichlet_subdomain_energy_bound
#check @Carleman.exists_uniform_dirichlet_subdomain_solutions
#print axioms Carleman.exists_uniform_dirichlet_subdomain_solutions
#check @Carleman.SpatialTest.eventually_support_subset
#print axioms Carleman.SpatialTest.eventually_support_subset
#check @Carleman.exists_dirichlet_H2_of_exhaustion
#print axioms Carleman.exists_dirichlet_H2_of_exhaustion

#check @Carleman.SpatialTest.mixed_derivative_norm_sq
#print axioms Carleman.SpatialTest.mixed_derivative_norm_sq
#check @Carleman.SpatialTest.hessian_energy_eq_laplacian
#print axioms Carleman.SpatialTest.hessian_energy_eq_laplacian
#check @Carleman.SpatialTest.hessian_component_norm_le_laplacian
#print axioms Carleman.SpatialTest.hessian_component_norm_le_laplacian
#check @Carleman.SpatialTest.laplacianLp
#print axioms Carleman.SpatialTest.laplacianLp
#check @Carleman.SpatialTest.exists_H2_jet
#print axioms Carleman.SpatialTest.exists_H2_jet
#check @Carleman.IsWeakSpatialDerivative.mixed_convolution_first
#print axioms Carleman.IsWeakSpatialDerivative.mixed_convolution_first
#check @Carleman.IsWeakNegativeLaplacian.integral_test
#print axioms Carleman.IsWeakNegativeLaplacian.integral_test
#check @Carleman.IsWeakNegativeLaplacian.convolution_identity
#print axioms Carleman.IsWeakNegativeLaplacian.convolution_identity
#check @Carleman.IsWeakNegativeLaplacian.mollified_laplacian
#print axioms Carleman.IsWeakNegativeLaplacian.mollified_laplacian

#check @Carleman.spatialLaplacian
#print axioms Carleman.spatialLaplacian
#check @Carleman.smooth_directional_mul
#print axioms Carleman.smooth_directional_mul
#check @Carleman.smooth_second_directional_mul
#print axioms Carleman.smooth_second_directional_mul
#check @Carleman.spatialLaplacian_mul
#print axioms Carleman.spatialLaplacian_mul
#check @Carleman.SpatialTest.mulSmooth
#print axioms Carleman.SpatialTest.mulSmooth
#check @Carleman.SpatialTest.laplacianLp_ae
#print axioms Carleman.SpatialTest.laplacianLp_ae
#check @Carleman.spatialLaplacian_smooth
#print axioms Carleman.spatialLaplacian_smooth
#check @Carleman.SpatialTest.laplacian_eq_zero_of_notMem_tsupport
#print axioms Carleman.SpatialTest.laplacian_eq_zero_of_notMem_tsupport
#check @Carleman.IsWeakNegativeLaplacian.cutoff_convolution
#print axioms Carleman.IsWeakNegativeLaplacian.cutoff_convolution
#check @Carleman.SpatialTest.exists_laplacian_multiplier_bound
#print axioms Carleman.SpatialTest.exists_laplacian_multiplier_bound
#check @Carleman.IsWeakNegativeLaplacian.cutoff_laplacian_bound
#print axioms Carleman.IsWeakNegativeLaplacian.cutoff_laplacian_bound
#check @Carleman.exists_uniform_cutoff_H2
#print axioms Carleman.exists_uniform_cutoff_H2

#check @Carleman.exists_spatialTest_eq_one_on_compact
#print axioms Carleman.exists_spatialTest_eq_one_on_compact
#check @Carleman.cutoff_fderiv_eq
#print axioms Carleman.cutoff_fderiv_eq
#check @Carleman.cutoff_mollifier_gradient_tendsto
#print axioms Carleman.cutoff_mollifier_gradient_tendsto
#check @Carleman.IsWeakNegativeLaplacian.restrictSubdomain
#print axioms Carleman.IsWeakNegativeLaplacian.restrictSubdomain
#check @Carleman.exists_interior_H2_of_cutoff
#print axioms Carleman.exists_interior_H2_of_cutoff
#check @Carleman.exists_interior_H2_bound
#print axioms Carleman.exists_interior_H2_bound

#check @Carleman.SimplicialPartition.maxDiameter_pos
#print axioms Carleman.SimplicialPartition.maxDiameter_pos
#check @Carleman.SimplicialPartition.inverseWeight_const_bound
#print axioms Carleman.SimplicialPartition.inverseWeight_const_bound
#check @Carleman.conforming_uniform_inverse
#print axioms Carleman.conforming_uniform_inverse
#check @Carleman.Physical.filterRayleigh_le_of_energy_bound
#print axioms Carleman.Physical.filterRayleigh_le_of_energy_bound
#check @Carleman.Physical.nestedConformingFilter
#print axioms Carleman.Physical.nestedConformingFilter
#check @Carleman.Physical.dirichlet_galerkin_energy
#print axioms Carleman.Physical.dirichlet_galerkin_energy
#check @Carleman.Physical.nested_p1_filter_rayleigh
#print axioms Carleman.Physical.nested_p1_filter_rayleigh
#check @Carleman.Physical.p1_coarse_filter_rayleigh
#print axioms Carleman.Physical.p1_coarse_filter_rayleigh

#check @Carleman.linearRefinementValue
#print axioms Carleman.linearRefinementValue
#check @Carleman.linearRefinementMass
#print axioms Carleman.linearRefinementMass
#check @Carleman.linearRefinementEnergy
#print axioms Carleman.linearRefinementEnergy
#check @Carleman.sum_affine_sq
#print axioms Carleman.sum_affine_sq
#check @Carleman.linearRefinementMass_eq
#print axioms Carleman.linearRefinementMass_eq
#check @Carleman.linearRefinementEnergy_eq
#print axioms Carleman.linearRefinementEnergy_eq
#check @Carleman.linearRefinement_inverse
#print axioms Carleman.linearRefinement_inverse
#check @Carleman.uniformLinearProlongation
#print axioms Carleman.uniformLinearProlongation
#check @Carleman.linearRefinementValue_zero
#print axioms Carleman.linearRefinementValue_zero
#check @Carleman.linearRefinementValue_end
#print axioms Carleman.linearRefinementValue_end
#check @Carleman.uniformLinearProlongation_node
#print axioms Carleman.uniformLinearProlongation_node
#check @Carleman.uniformLinearProlongation_cell
#print axioms Carleman.uniformLinearProlongation_cell
#check @Carleman.sum_uniform_blocks
#print axioms Carleman.sum_uniform_blocks
#check @Carleman.uniformLinearProlongation_energy_cells
#print axioms Carleman.uniformLinearProlongation_energy_cells
#check @Carleman.uniformLinearProlongation_mass_cells
#print axioms Carleman.uniformLinearProlongation_mass_cells
#check @Carleman.trapezoid_square_sum
#print axioms Carleman.trapezoid_square_sum
#check @Carleman.uniformLinearProlongation_inverse
#print axioms Carleman.uniformLinearProlongation_inverse
#check @Carleman.uniformLinearProlongation_physical_inverse
#print axioms Carleman.uniformLinearProlongation_physical_inverse

#check @Carleman.linearRefinementBasis
#print axioms Carleman.linearRefinementBasis
#check @Carleman.tensorLinearProlongation
#print axioms Carleman.tensorLinearProlongation
#check @Carleman.linearRefinementBasis_node
#print axioms Carleman.linearRefinementBasis_node
#check @Carleman.uniformLinearProlongation_sum
#print axioms Carleman.uniformLinearProlongation_sum
#check @Carleman.uniformLinearProlongation_const_mul
#print axioms Carleman.uniformLinearProlongation_const_mul
#check @Carleman.tensorLinearProlongation_zero_face
#print axioms Carleman.tensorLinearProlongation_zero_face
#check @Carleman.tensorLinearProlongation_node
#print axioms Carleman.tensorLinearProlongation_node
#check @Carleman.tensorLinearProlongation_slice
#print axioms Carleman.tensorLinearProlongation_slice
#check @Carleman.cartesianAxisFill
#print axioms Carleman.cartesianAxisFill
#check @Carleman.cartesianAxisFill_self
#print axioms Carleman.cartesianAxisFill_self
#check @Carleman.cartesianAxisFill_update
#print axioms Carleman.cartesianAxisFill_update
#check @Carleman.cartesian_sum_axis
#print axioms Carleman.cartesian_sum_axis
#check @Carleman.tensorLinearProlongation_line_inverse
#print axioms Carleman.tensorLinearProlongation_line_inverse
#check @Carleman.tensorLinearProlongation_direction_inverse
#print axioms Carleman.tensorLinearProlongation_direction_inverse
#check @Carleman.tensorLinearProlongation_inverse
#print axioms Carleman.tensorLinearProlongation_inverse
#check @Carleman.cartesianLatticeData_of_box_values
#print axioms Carleman.cartesianLatticeData_of_box_values
#check @Carleman.cartesian_sum_box_values
#print axioms Carleman.cartesian_sum_box_values
#check @Carleman.cartesianLatticeSuccessor_nat
#print axioms Carleman.cartesianLatticeSuccessor_nat
#check @Carleman.cartesianCoarseProlongation
#print axioms Carleman.cartesianCoarseProlongation
#check @Carleman.cartesianCoarseProlongation_values
#print axioms Carleman.cartesianCoarseProlongation_values
#check @Carleman.cartesianCoarseProlongation_mass
#print axioms Carleman.cartesianCoarseProlongation_mass
#check @Carleman.cartesianCoarseProlongation_axis
#print axioms Carleman.cartesianCoarseProlongation_axis
#check @Carleman.cartesianCoarseProlongation_energy
#print axioms Carleman.cartesianCoarseProlongation_energy
#check @Carleman.Physical.cartesianCoarseFilter
#print axioms Carleman.Physical.cartesianCoarseFilter
#check @Carleman.Physical.cartesian_coarse_energy_bound
#print axioms Carleman.Physical.cartesian_coarse_energy_bound
#check @Carleman.Physical.fd_coarse_filter_rayleigh
#print axioms Carleman.Physical.fd_coarse_filter_rayleigh
#check @Carleman.Physical.fd_dividing_filter_rayleigh
#print axioms Carleman.Physical.fd_dividing_filter_rayleigh

#check @Carleman.inward_fderiv_tendsto_of_contDiffAt
#print axioms Carleman.inward_fderiv_tendsto_of_contDiffAt
#check @Carleman.compactLipschitz_inward_tendsto_H1
#print axioms Carleman.compactLipschitz_inward_tendsto_H1
#check @Carleman.piecewiseSmooth_mem_dirichletJetSpace
#print axioms Carleman.piecewiseSmooth_mem_dirichletJetSpace
#check @Carleman.zeroBoundary_indicator_lipschitz
#print axioms Carleman.zeroBoundary_indicator_lipschitz
#check @Carleman.indicator_tsupport_subset_closure
#print axioms Carleman.indicator_tsupport_subset_closure
#check @Carleman.indicator_hasCompactSupport
#print axioms Carleman.indicator_hasCompactSupport
#check @Carleman.indicator_contDiffAt_off_frontier
#print axioms Carleman.indicator_contDiffAt_off_frontier
#check @Carleman.indicator_contDiffAt_ae
#print axioms Carleman.indicator_contDiffAt_ae
#check @Carleman.smooth_boundary_zero_mem_dirichletJetSpace
#print axioms Carleman.smooth_boundary_zero_mem_dirichletJetSpace
#check @Carleman.smooth_boundary_test_mem_dirichletJetSpace
#print axioms Carleman.smooth_boundary_test_mem_dirichletJetSpace

#check @Carleman.coordinateSignFlip
#print axioms Carleman.coordinateSignFlip
#check @Carleman.coordinateSignFlip_apply
#print axioms Carleman.coordinateSignFlip_apply
#check @Carleman.coordinateReflection
#print axioms Carleman.coordinateReflection
#check @Carleman.coordinateReflection_apply
#print axioms Carleman.coordinateReflection_apply
#check @Carleman.coordinateReflection_involutive
#print axioms Carleman.coordinateReflection_involutive
#check @Carleman.coordinateReflection_symm
#print axioms Carleman.coordinateReflection_symm
#check @Carleman.coordinateReflection_measurePreserving
#print axioms Carleman.coordinateReflection_measurePreserving
#check @Carleman.coordinateReflectionSign
#print axioms Carleman.coordinateReflectionSign
#check @Carleman.coordinateReflectionSign_sq
#print axioms Carleman.coordinateReflectionSign_sq
#check @Carleman.coordinateSignFlip_basis
#print axioms Carleman.coordinateSignFlip_basis
#check @Carleman.firstComponentFields
#print axioms Carleman.firstComponentFields
#check @Carleman.firstComponentJet
#print axioms Carleman.firstComponentJet
#check @Carleman.firstComponentJet_value
#print axioms Carleman.firstComponentJet_value
#check @Carleman.firstComponentJet_gradient
#print axioms Carleman.firstComponentJet_gradient
#check @Carleman.firstGradientAssembly_norm_sq
#print axioms Carleman.firstGradientAssembly_norm_sq
#check @Carleman.coordinateReflectionLp
#print axioms Carleman.coordinateReflectionLp
#check @Carleman.coordinateReflectionLp_ae
#print axioms Carleman.coordinateReflectionLp_ae
#check @Carleman.coordinateReflectionLp_norm
#print axioms Carleman.coordinateReflectionLp_norm
#check @Carleman.integral_mul_coordinateReflectionLp
#print axioms Carleman.integral_mul_coordinateReflectionLp
#check @Carleman.coordinateReflectionLp_inner
#print axioms Carleman.coordinateReflectionLp_inner
#check @Carleman.coordinateReflectionLp_involutive
#print axioms Carleman.coordinateReflectionLp_involutive
#check @Carleman.coordinateReflectionLp_inner_both
#print axioms Carleman.coordinateReflectionLp_inner_both
#check @Carleman.IsWeakSpatialDerivative.coordinate_reflection
#print axioms Carleman.IsWeakSpatialDerivative.coordinate_reflection
#check @Carleman.WeakSobolevJet.reflectCoordinate
#print axioms Carleman.WeakSobolevJet.reflectCoordinate
#check @Carleman.WeakSobolevJet.reflectCoordinate_value
#print axioms Carleman.WeakSobolevJet.reflectCoordinate_value
#check @Carleman.WeakSobolevJet.reflectCoordinate_gradient
#print axioms Carleman.WeakSobolevJet.reflectCoordinate_gradient
#check @Carleman.WeakSobolevJet.reflectCoordinate_involutive
#print axioms Carleman.WeakSobolevJet.reflectCoordinate_involutive
#check @Carleman.WeakSobolevJet.reflectCoordinate_value_norm
#print axioms Carleman.WeakSobolevJet.reflectCoordinate_value_norm
#check @Carleman.WeakSobolevJet.reflectCoordinate_gradient_pairing
#print axioms Carleman.WeakSobolevJet.reflectCoordinate_gradient_pairing
#check @Carleman.WeakSobolevJet.reflectCoordinate_gradient_norm
#print axioms Carleman.WeakSobolevJet.reflectCoordinate_gradient_norm
#check @Carleman.WeakSobolevJet.reflectCoordinate_gradient_adjoint
#print axioms Carleman.WeakSobolevJet.reflectCoordinate_gradient_adjoint

#check @Carleman.SpatialTest.fullJet
#print axioms Carleman.SpatialTest.fullJet
#check @Carleman.SpatialTest.fullJet_value_ae
#print axioms Carleman.SpatialTest.fullJet_value_ae
#check @Carleman.SpatialTest.fullJet_restrict
#print axioms Carleman.SpatialTest.fullJet_restrict
#check @Carleman.SpatialTest.reflectCoordinate
#print axioms Carleman.SpatialTest.reflectCoordinate
#check @Carleman.SpatialTest.reflectCoordinate_value
#print axioms Carleman.SpatialTest.reflectCoordinate_value
#check @Carleman.SpatialTest.reflectCoordinate_fullJet
#print axioms Carleman.SpatialTest.reflectCoordinate_fullJet
#check @Carleman.SpatialTest.oddReflectionTest
#print axioms Carleman.SpatialTest.oddReflectionTest
#check @Carleman.SpatialTest.oddReflectionTest_value
#print axioms Carleman.SpatialTest.oddReflectionTest_value
#check @Carleman.SpatialTest.oddReflectionTest_fullJet
#print axioms Carleman.SpatialTest.oddReflectionTest_fullJet
#check @Carleman.zeroExtendLp_inner
#print axioms Carleman.zeroExtendLp_inner
#check @Carleman.WeakSobolevJet.zeroExtendDirichlet_pairing
#print axioms Carleman.WeakSobolevJet.zeroExtendDirichlet_pairing
#check @Carleman.SpatialTest.fullJet_eq_zeroExtend
#print axioms Carleman.SpatialTest.fullJet_eq_zeroExtend
#check @Carleman.SpatialTest.fullJet_pairing
#print axioms Carleman.SpatialTest.fullJet_pairing
#check @Carleman.SpatialTest.fullJet_inner
#print axioms Carleman.SpatialTest.fullJet_inner
#check @Carleman.SpatialTest.fullJet_boundary_mem
#print axioms Carleman.SpatialTest.fullJet_boundary_mem
#check @Carleman.WeakSobolevJet.oddExtend
#print axioms Carleman.WeakSobolevJet.oddExtend
#check @Carleman.oddExtendLp
#print axioms Carleman.oddExtendLp
#check @Carleman.oddExtend_poisson_full_test
#print axioms Carleman.oddExtend_poisson_full_test
#check @Carleman.oddExtend_isWeakNegativeLaplacian
#print axioms Carleman.oddExtend_isWeakNegativeLaplacian
#check @Carleman.coordinateReflectionLp_continuous
#print axioms Carleman.coordinateReflectionLp_continuous
#check @Carleman.WeakSobolevJet.reflectCoordinate_tendsto
#print axioms Carleman.WeakSobolevJet.reflectCoordinate_tendsto
#check @Carleman.SpatialTest.oddReflectionInto
#print axioms Carleman.SpatialTest.oddReflectionInto
#check @Carleman.SpatialTest.oddReflectionInto_value
#print axioms Carleman.SpatialTest.oddReflectionInto_value
#check @Carleman.SpatialTest.oddExtend_test
#print axioms Carleman.SpatialTest.oddExtend_test
#check @Carleman.WeakSobolevJet.oddExtend_tendsto
#print axioms Carleman.WeakSobolevJet.oddExtend_tendsto
#check @Carleman.WeakSobolevJet.oddExtend_mem
#print axioms Carleman.WeakSobolevJet.oddExtend_mem
#check @Carleman.lowerReflectedBox
#print axioms Carleman.lowerReflectedBox
#check @Carleman.coordinateReflection_fixed_plane
#print axioms Carleman.coordinateReflection_fixed_plane
#check @Carleman.lowerReflectedBox_boundary_exclusion
#print axioms Carleman.lowerReflectedBox_boundary_exclusion
#check @Carleman.lowerReflectedBox_no_original_overlap
#print axioms Carleman.lowerReflectedBox_no_original_overlap
#check @Carleman.lowerReflectedBox_contains_original
#print axioms Carleman.lowerReflectedBox_contains_original
#check @Carleman.lowerReflectedBox_contains_reflection
#print axioms Carleman.lowerReflectedBox_contains_reflection
#check @Carleman.lowerReflectedBox_test_boundary
#print axioms Carleman.lowerReflectedBox_test_boundary
#check @Carleman.lower_box_odd_poisson
#print axioms Carleman.lower_box_odd_poisson
#check @Carleman.oddExtend_restrict_original
#print axioms Carleman.oddExtend_restrict_original
#check @Carleman.lower_box_odd_restrict
#print axioms Carleman.lower_box_odd_restrict
#check @Carleman.lower_box_odd_dirichlet
#print axioms Carleman.lower_box_odd_dirichlet
#check @Carleman.oddExtendLp_norm_le
#print axioms Carleman.oddExtendLp_norm_le
#check @Carleman.WeakSobolevJet.oddExtend_value_norm_le
#print axioms Carleman.WeakSobolevJet.oddExtend_value_norm_le
#check @Carleman.WeakSobolevJet.oddExtend_gradient_norm_le
#print axioms Carleman.WeakSobolevJet.oddExtend_gradient_norm_le

#check @Carleman.upperReflectedBox
#print axioms Carleman.upperReflectedBox
#check @Carleman.upperReflectedBox_boundary_exclusion
#print axioms Carleman.upperReflectedBox_boundary_exclusion
#check @Carleman.upperReflectedBox_no_original_overlap
#print axioms Carleman.upperReflectedBox_no_original_overlap
#check @Carleman.upperReflectedBox_contains_original
#print axioms Carleman.upperReflectedBox_contains_original
#check @Carleman.upperReflectedBox_contains_reflection
#print axioms Carleman.upperReflectedBox_contains_reflection
#check @Carleman.upperReflectedBox_test_boundary
#print axioms Carleman.upperReflectedBox_test_boundary
#check @Carleman.upper_box_odd_poisson
#print axioms Carleman.upper_box_odd_poisson
#check @Carleman.upper_box_odd_restrict
#print axioms Carleman.upper_box_odd_restrict
#check @Carleman.upper_box_odd_dirichlet
#print axioms Carleman.upper_box_odd_dirichlet
#check @Carleman.subdomainLp_trans
#print axioms Carleman.subdomainLp_trans
#check @Carleman.subdomainLp_self
#print axioms Carleman.subdomainLp_self
#check @Carleman.subdomainLp_restrictRegion
#print axioms Carleman.subdomainLp_restrictRegion
#check @Carleman.WeakSobolevJet.restrictSubdomain_trans
#print axioms Carleman.WeakSobolevJet.restrictSubdomain_trans
#check @Carleman.WeakSobolevJet.restrictSubdomain_self
#print axioms Carleman.WeakSobolevJet.restrictSubdomain_self
#check @Carleman.WeakSobolevJet.restrictSubdomain_restrictDomain
#print axioms Carleman.WeakSobolevJet.restrictSubdomain_restrictDomain
#check @Carleman.IsPoissonExtension
#print axioms Carleman.IsPoissonExtension
#check @Carleman.exists_odd_dirichlet_extension
#print axioms Carleman.exists_odd_dirichlet_extension
#check @Carleman.exists_lower_box_extension
#print axioms Carleman.exists_lower_box_extension
#check @Carleman.exists_upper_box_extension
#print axioms Carleman.exists_upper_box_extension
#check @Carleman.expandedBoxLower
#print axioms Carleman.expandedBoxLower
#check @Carleman.expandedBoxUpper
#print axioms Carleman.expandedBoxUpper
#check @Carleman.expandedBox_positive
#print axioms Carleman.expandedBox_positive
#check @Carleman.expandedBox_contains
#print axioms Carleman.expandedBox_contains
#check @Carleman.expandedBoxLower_insert
#print axioms Carleman.expandedBoxLower_insert
#check @Carleman.expandedBoxUpper_insert
#print axioms Carleman.expandedBoxUpper_insert
#check @Carleman.expandedBox_closure_inside
#print axioms Carleman.expandedBox_closure_inside
#check @Carleman.IsPoissonExtension.refl
#print axioms Carleman.IsPoissonExtension.refl
#check @Carleman.IsPoissonExtension.trans
#print axioms Carleman.IsPoissonExtension.trans
#check @Carleman.exists_finite_box_extension
#print axioms Carleman.exists_finite_box_extension
#check @Carleman.derivativeComponent_norm_le_field
#print axioms Carleman.derivativeComponent_norm_le_field
#check @Carleman.exists_box_dirichlet_H2_bound
#print axioms Carleman.exists_box_dirichlet_H2_bound
#check @Carleman.box_dirichlet_domain_le_h2
#print axioms Carleman.box_dirichlet_domain_le_h2
#check @Carleman.box_dirichlet_domain_eq_h2
#print axioms Carleman.box_dirichlet_domain_eq_h2
#check @Carleman.exists_box_dirichlet_H2_estimate
#print axioms Carleman.exists_box_dirichlet_H2_estimate

#check @Carleman.cartesian_numericalData_of_box
#print axioms Carleman.cartesian_numericalData_of_box

#check @Carleman.cartesian_full_weight_interface
#print axioms Carleman.cartesian_full_weight_interface

#check @Carleman.box_dirichlet_graph_estimate
#print axioms Carleman.box_dirichlet_graph_estimate
#check @Carleman.box_analytic_data_uniform
#print axioms Carleman.box_analytic_data_uniform
#check @Carleman.box_analytic_realization
#print axioms Carleman.box_analytic_realization

#check @Carleman.shearDirectionCoordinates
#print axioms Carleman.shearDirectionCoordinates
#check @Carleman.shearDirectionCoordinates_direction
#print axioms Carleman.shearDirectionCoordinates_direction
#check @Carleman.exists_directional_coordinates
#print axioms Carleman.exists_directional_coordinates
#check @Carleman.finite_linear_max_lipschitz
#print axioms Carleman.finite_linear_max_lipschitz
#check @Carleman.finite_halfspace_graph_charts
#print axioms Carleman.finite_halfspace_graph_charts
#check @Carleman.finite_halfspace_bounded_lipschitz
#print axioms Carleman.finite_halfspace_bounded_lipschitz
#check @Carleman.openCoordinateBox_bounded_lipschitz
#print axioms Carleman.openCoordinateBox_bounded_lipschitz
#check @Carleman.box_section3
#print axioms Carleman.box_section3

#check @Carleman.interiorQuadratic
#print axioms Carleman.interiorQuadratic
#check @Carleman.interiorGaussian
#print axioms Carleman.interiorGaussian
#check @Carleman.interiorCarlemanProfile
#print axioms Carleman.interiorCarlemanProfile
#check @Carleman.interiorQuadratic_contDiff
#print axioms Carleman.interiorQuadratic_contDiff
#check @Carleman.interiorGaussian_contDiff
#print axioms Carleman.interiorGaussian_contDiff
#check @Carleman.interiorCarlemanProfile_contDiff
#print axioms Carleman.interiorCarlemanProfile_contDiff
#check @Carleman.interiorQuadratic_hasFDerivAt
#print axioms Carleman.interiorQuadratic_hasFDerivAt
#check @Carleman.interiorGaussian_hasFDerivAt
#print axioms Carleman.interiorGaussian_hasFDerivAt
#check @Carleman.interiorCarlemanProfile_hasFDerivAt
#print axioms Carleman.interiorCarlemanProfile_hasFDerivAt
#check @Carleman.interiorGaussian_fderiv_apply
#print axioms Carleman.interiorGaussian_fderiv_apply
#check @Carleman.interiorCarlemanProfile_fderiv_apply
#print axioms Carleman.interiorCarlemanProfile_fderiv_apply
#check @Carleman.interiorGaussian_pos
#print axioms Carleman.interiorGaussian_pos
#check @Carleman.interiorGaussian_le_one
#print axioms Carleman.interiorGaussian_le_one
#check @Carleman.interiorCarlemanProfile_bounds
#print axioms Carleman.interiorCarlemanProfile_bounds
#check @Carleman.interiorCarlemanProfile_hessian
#print axioms Carleman.interiorCarlemanProfile_hessian
#check @Carleman.interiorCarlemanProfile_smoothOnClosure
#print axioms Carleman.interiorCarlemanProfile_smoothOnClosure
#check @Carleman.interiorSpatialProfile
#print axioms Carleman.interiorSpatialProfile
#check @Carleman.interiorSpatialProfile_value
#print axioms Carleman.interiorSpatialProfile_value
#check @Carleman.interiorQuadratic_gradient
#print axioms Carleman.interiorQuadratic_gradient
#check @Carleman.interiorQuadratic_gradient_norm_sq
#print axioms Carleman.interiorQuadratic_gradient_norm_sq
#check @Carleman.interiorQuadratic_gradient_outside_ball
#print axioms Carleman.interiorQuadratic_gradient_outside_ball
#check @Carleman.exists_interiorGaussian_gradient_threshold
#print axioms Carleman.exists_interiorGaussian_gradient_threshold
#check @Carleman.interiorGaussian_lower_bound
#print axioms Carleman.interiorGaussian_lower_bound
#check @Carleman.interiorGaussian_supporting_normal
#print axioms Carleman.interiorGaussian_supporting_normal
#check @Carleman.interiorGaussian_face_flux_nonpos
#print axioms Carleman.interiorGaussian_face_flux_nonpos
#check @Carleman.interiorHeatPsi
#print axioms Carleman.interiorHeatPsi
#check @Carleman.interiorHeatMatrix
#print axioms Carleman.interiorHeatMatrix
#check @Carleman.interiorCarlemanProfile_scaled_hessian
#print axioms Carleman.interiorCarlemanProfile_scaled_hessian
#check @Carleman.interiorHeatMatrix_formula
#print axioms Carleman.interiorHeatMatrix_formula
#check @Carleman.interiorHeatMatrix_coercive
#print axioms Carleman.interiorHeatMatrix_coercive
#check @Carleman.interiorHeatMatrix_uniform_coercive
#print axioms Carleman.interiorHeatMatrix_uniform_coercive
#check @Carleman.exists_interior_heat_weight
#print axioms Carleman.exists_interior_heat_weight

#check @Carleman.smoothD
#print axioms Carleman.smoothD
#check @Carleman.smoothD_contDiff
#print axioms Carleman.smoothD_contDiff
#check @Carleman.smoothD_add
#print axioms Carleman.smoothD_add
#check @Carleman.smoothD_sub
#print axioms Carleman.smoothD_sub
#check @Carleman.smoothD_neg
#print axioms Carleman.smoothD_neg
#check @Carleman.smoothD_mul
#print axioms Carleman.smoothD_mul
#check @Carleman.smoothD_const_mul
#print axioms Carleman.smoothD_const_mul
#check @Carleman.smoothD_sq
#print axioms Carleman.smoothD_sq
#check @Carleman.smoothD_sum
#print axioms Carleman.smoothD_sum
#check @Carleman.smoothD_comm
#print axioms Carleman.smoothD_comm
#check @Carleman.directionalLap
#print axioms Carleman.directionalLap
#check @Carleman.directionalPair
#print axioms Carleman.directionalPair
#check @Carleman.directionalEnergy
#print axioms Carleman.directionalEnergy
#check @Carleman.directionalHessianForm
#print axioms Carleman.directionalHessianForm
#check @Carleman.directionalLap_contDiff
#print axioms Carleman.directionalLap_contDiff
#check @Carleman.directionalPair_contDiff
#print axioms Carleman.directionalPair_contDiff
#check @Carleman.directionalEnergy_contDiff
#print axioms Carleman.directionalEnergy_contDiff
#check @Carleman.smoothD_directionalPair
#print axioms Carleman.smoothD_directionalPair
#check @Carleman.smoothD_directionalEnergy
#print axioms Carleman.smoothD_directionalEnergy
#check @Carleman.directional_transport_cancellation
#print axioms Carleman.directional_transport_cancellation
#check @Carleman.directionalPair_comm
#print axioms Carleman.directionalPair_comm
#check @Carleman.directionalPair_mul_left
#print axioms Carleman.directionalPair_mul_left
#check @Carleman.directionalPair_sq_left
#print axioms Carleman.directionalPair_sq_left
#check @Carleman.directionalPair_self
#print axioms Carleman.directionalPair_self
#check @Carleman.directional_div_product
#print axioms Carleman.directional_div_product
#check @Carleman.smoothD_directionalEnergy_time
#print axioms Carleman.smoothD_directionalEnergy_time
#check @Carleman.directionalLap_mul
#print axioms Carleman.directionalLap_mul
#check @Carleman.pointwiseHeatFlux
#print axioms Carleman.pointwiseHeatFlux
#check @Carleman.pointwiseHeatTimeFlux
#print axioms Carleman.pointwiseHeatTimeFlux
#check @Carleman.pointwiseHeatB
#print axioms Carleman.pointwiseHeatB
#check @Carleman.pointwiseHeatMatrixEnergy
#print axioms Carleman.pointwiseHeatMatrixEnergy
#check @Carleman.pointwiseHeatFlux_divergence
#print axioms Carleman.pointwiseHeatFlux_divergence
#check @Carleman.pointwise_heat_identity
#print axioms Carleman.pointwise_heat_identity
#check @Carleman.smoothD_exp
#print axioms Carleman.smoothD_exp
#check @Carleman.smoothD_exp_neg
#print axioms Carleman.smoothD_exp_neg
#check @Carleman.directionalLap_exp_neg
#print axioms Carleman.directionalLap_exp_neg
#check @Carleman.directionalPair_exp_neg
#print axioms Carleman.directionalPair_exp_neg
#check @Carleman.heatConjugationK
#print axioms Carleman.heatConjugationK
#check @Carleman.heatCarlemanA
#print axioms Carleman.heatCarlemanA
#check @Carleman.heatConjugationK_eq
#print axioms Carleman.heatConjugationK_eq
#check @Carleman.heatConjugationK_contDiff
#print axioms Carleman.heatConjugationK_contDiff
#check @Carleman.pointwiseHeatB_original_formula
#print axioms Carleman.pointwiseHeatB_original_formula
#check @Carleman.pointwise_heat_conjugation
#print axioms Carleman.pointwise_heat_conjugation
#check @Carleman.pointwise_heat_carleman_identity
#print axioms Carleman.pointwise_heat_carleman_identity
#check @Carleman.pointwise_heat_carleman_inequality
#print axioms Carleman.pointwise_heat_carleman_inequality
#check @Carleman.spaceTimeSpatialDirection
#print axioms Carleman.spaceTimeSpatialDirection
#check @Carleman.spaceTimeHeat
#print axioms Carleman.spaceTimeHeat
#check @Carleman.spaceTime_timeD
#print axioms Carleman.spaceTime_timeD
#check @Carleman.spaceTime_spatialD
#print axioms Carleman.spaceTime_spatialD
#check @Carleman.spaceTime_directionalLap
#print axioms Carleman.spaceTime_directionalLap
#check @Carleman.spaceTime_heat_directional
#print axioms Carleman.spaceTime_heat_directional
#check @Carleman.spacetime_heat_carleman_identity
#print axioms Carleman.spacetime_heat_carleman_identity
#check @Carleman.spacetime_heat_carleman_inequality
#print axioms Carleman.spacetime_heat_carleman_inequality

#check @Carleman.smoothD_periodic
#print axioms Carleman.smoothD_periodic
#check @Carleman.directionalLap_periodic
#print axioms Carleman.directionalLap_periodic
#check @Carleman.directionalEnergy_periodic
#print axioms Carleman.directionalEnergy_periodic
#check @Carleman.heatConjugationK_periodic
#print axioms Carleman.heatConjugationK_periodic
#check @Carleman.pointwiseHeatTimeFlux_contDiff
#print axioms Carleman.pointwiseHeatTimeFlux_contDiff
#check @Carleman.pointwiseHeatTimeFlux_periodic
#print axioms Carleman.pointwiseHeatTimeFlux_periodic
#check @Carleman.spacetime_periodic_derivative_integral
#print axioms Carleman.spacetime_periodic_derivative_integral
#check @Carleman.spacetime_heat_time_flux_integral
#print axioms Carleman.spacetime_heat_time_flux_integral
#check @Carleman.smooth_plane_tangent_derivative
#print axioms Carleman.smooth_plane_tangent_derivative
#check @Carleman.smooth_plane_normal_derivative
#print axioms Carleman.smooth_plane_normal_derivative
#check @Carleman.spacetime_plane_zero_derivatives
#print axioms Carleman.spacetime_plane_zero_derivatives
#check @Carleman.spacetime_directional_normal_sum
#print axioms Carleman.spacetime_directional_normal_sum
#check @Carleman.pointwiseHeatFlux_normal_eq
#print axioms Carleman.pointwiseHeatFlux_normal_eq
#check @Carleman.smooth_plane_heat_flux
#print axioms Carleman.smooth_plane_heat_flux
#check @Carleman.gaussian_plane_heat_flux_nonpos
#print axioms Carleman.gaussian_plane_heat_flux_nonpos

#check @Carleman.finite_halfspace_mem_closure
#print axioms Carleman.finite_halfspace_mem_closure
#check @Carleman.finite_halfspace_closure_iff
#print axioms Carleman.finite_halfspace_closure_iff
#check @Carleman.finite_halfspace_face_neighborhood
#print axioms Carleman.finite_halfspace_face_neighborhood
#check @Carleman.finite_halfspace_face_mem_closure
#print axioms Carleman.finite_halfspace_face_mem_closure
#check @Carleman.halfspaceOutwardNormal
#print axioms Carleman.halfspaceOutwardNormal
#check @Carleman.halfspaceOutwardNormal_norm
#print axioms Carleman.halfspaceOutwardNormal_norm
#check @Carleman.halfspaceOutwardNormal_eval
#print axioms Carleman.halfspaceOutwardNormal_eval
#check @Carleman.halfspaceOutwardNormal_plane
#print axioms Carleman.halfspaceOutwardNormal_plane
#check @Carleman.halfspaceOutwardNormal_support
#print axioms Carleman.halfspaceOutwardNormal_support
#check @Carleman.pointwiseHeatFlux_contDiff
#print axioms Carleman.pointwiseHeatFlux_contDiff
#check @Carleman.finite_halfspace_gaussian_heat_flux
#print axioms Carleman.finite_halfspace_gaussian_heat_flux
#check @Carleman.finite_halfspace_closed_face_gaussian_heat_flux
#print axioms Carleman.finite_halfspace_closed_face_gaussian_heat_flux

#check @Carleman.coordinateBoxFunctional
#print axioms Carleman.coordinateBoxFunctional
#check @Carleman.coordinateBoxThreshold
#print axioms Carleman.coordinateBoxThreshold
#check @Carleman.coordinateBoxFunctional_apply
#print axioms Carleman.coordinateBoxFunctional_apply
#check @Carleman.openCoordinateBox_halfspaces
#print axioms Carleman.openCoordinateBox_halfspaces
#check @Carleman.closedCoordinateBox_halfspaces
#print axioms Carleman.closedCoordinateBox_halfspaces
#check @Carleman.coordinateBoxFunctional_normal
#print axioms Carleman.coordinateBoxFunctional_normal
#check @Carleman.coordinateBox_face_witness
#print axioms Carleman.coordinateBox_face_witness
#check @Carleman.box_face_gaussian_heat_flux
#print axioms Carleman.box_face_gaussian_heat_flux
#check @Carleman.coordinateDivergence
#print axioms Carleman.coordinateDivergence
#check @Carleman.coordinateDivergence_contDiff
#print axioms Carleman.coordinateDivergence_contDiff
#check @Carleman.smooth_closed_box_divergence
#print axioms Carleman.smooth_closed_box_divergence
#check @Carleman.openCoordinateBox_ae_closed
#print axioms Carleman.openCoordinateBox_ae_closed
#check @Carleman.smooth_open_box_divergence
#print axioms Carleman.smooth_open_box_divergence
#check @Carleman.coordinateFacePoint_mem_closed
#print axioms Carleman.coordinateFacePoint_mem_closed
#check @Carleman.box_gaussian_heat_flux_integral
#print axioms Carleman.box_gaussian_heat_flux_integral

#check @Carleman.boxTimeIntegral
#print axioms Carleman.boxTimeIntegral
#check @Carleman.continuous_box_time_integrable
#print axioms Carleman.continuous_box_time_integrable
#check @Carleman.boxTimeIntegral_eq_iterated
#print axioms Carleman.boxTimeIntegral_eq_iterated
#check @Carleman.boxTimeIntegral_add
#print axioms Carleman.boxTimeIntegral_add
#check @Carleman.boxTimeIntegral_mono
#print axioms Carleman.boxTimeIntegral_mono
#check @Carleman.boxTimeIntegral_nonpos_of_spatial
#print axioms Carleman.boxTimeIntegral_nonpos_of_spatial
#check @Carleman.boxTimeIntegral_periodic_derivative
#print axioms Carleman.boxTimeIntegral_periodic_derivative
#check @Carleman.directionalHessianForm_contDiff
#print axioms Carleman.directionalHessianForm_contDiff
#check @Carleman.pointwiseHeatMatrixEnergy_contDiff
#print axioms Carleman.pointwiseHeatMatrixEnergy_contDiff
#check @Carleman.pointwiseHeatB_contDiff
#print axioms Carleman.pointwiseHeatB_contDiff
#check @Carleman.heatCarlemanBulk
#print axioms Carleman.heatCarlemanBulk
#check @Carleman.heatCarlemanBulk_contDiff
#print axioms Carleman.heatCarlemanBulk_contDiff
#check @Carleman.pointwiseHeatDivergence_contDiff
#print axioms Carleman.pointwiseHeatDivergence_contDiff
#check @Carleman.spaceTimeHeat_contDiff
#print axioms Carleman.spaceTimeHeat_contDiff
#check @Carleman.box_smooth_heat_carleman_inequality
#print axioms Carleman.box_smooth_heat_carleman_inequality

#check @Carleman.interiorCarlemanProfile_laplacian
#print axioms Carleman.interiorCarlemanProfile_laplacian
#check @Carleman.interiorCarlemanProfile_energy
#print axioms Carleman.interiorCarlemanProfile_energy
#check @Carleman.interiorCarlemanProfile_energy_fderiv
#print axioms Carleman.interiorCarlemanProfile_energy_fderiv
#check @Carleman.interiorCarlemanProfile_laplacian_fderiv
#print axioms Carleman.interiorCarlemanProfile_laplacian_fderiv
#check @Carleman.interiorCarlemanProfile_energy_pair
#print axioms Carleman.interiorCarlemanProfile_energy_pair
#check @Carleman.interiorCarlemanProfile_gaussian_pair
#print axioms Carleman.interiorCarlemanProfile_gaussian_pair
#check @Carleman.separableHeatPhase
#print axioms Carleman.separableHeatPhase
#check @Carleman.separableHeatPhase_contDiff
#print axioms Carleman.separableHeatPhase_contDiff
#check @Carleman.separableHeatPhase_timeD
#print axioms Carleman.separableHeatPhase_timeD
#check @Carleman.separableHeatPhase_spatialD
#print axioms Carleman.separableHeatPhase_spatialD
#check @Carleman.separableHeatPhase_lap
#print axioms Carleman.separableHeatPhase_lap
#check @Carleman.separableHeatPhase_energy
#print axioms Carleman.separableHeatPhase_energy
#check @Carleman.separableHeatPhase_pair
#print axioms Carleman.separableHeatPhase_pair
#check @Carleman.directionalPair_add_left
#print axioms Carleman.directionalPair_add_left
#check @Carleman.directionalPair_const_mul_left
#print axioms Carleman.directionalPair_const_mul_left
#check @Carleman.interiorGaussianHeatPhase
#print axioms Carleman.interiorGaussianHeatPhase
#check @Carleman.interiorGaussianHeatPsi
#print axioms Carleman.interiorGaussianHeatPsi
#check @Carleman.interiorGaussianHeatPhase_contDiff
#print axioms Carleman.interiorGaussianHeatPhase_contDiff
#check @Carleman.interiorGaussianHeatPsi_contDiff
#print axioms Carleman.interiorGaussianHeatPsi_contDiff
#check @Carleman.interiorGaussianHeatPhase_periodic
#print axioms Carleman.interiorGaussianHeatPhase_periodic
#check @Carleman.interiorGaussianHeatPsi_periodic
#print axioms Carleman.interiorGaussianHeatPsi_periodic
#check @Carleman.interiorGaussianHeatPsi_formula
#print axioms Carleman.interiorGaussianHeatPsi_formula
#check @Carleman.interiorGaussianHeatPsi_eq_spatial
#print axioms Carleman.interiorGaussianHeatPsi_eq_spatial
#check @Carleman.interiorGaussianHeatK_formula
#print axioms Carleman.interiorGaussianHeatK_formula
#check @Carleman.interiorGaussianHeatK_explicit
#print axioms Carleman.interiorGaussianHeatK_explicit
#check @Carleman.interiorGaussianHeatPsi_spatialD
#print axioms Carleman.interiorGaussianHeatPsi_spatialD
#check @Carleman.interiorGaussianHeatPsi_energy
#print axioms Carleman.interiorGaussianHeatPsi_energy
#check @Carleman.pointwiseHeatB_lap_cancel
#print axioms Carleman.pointwiseHeatB_lap_cancel
#check @Carleman.interiorGaussianHeatK_timeD
#print axioms Carleman.interiorGaussianHeatK_timeD
#check @Carleman.interiorGaussianHeatK_pair
#print axioms Carleman.interiorGaussianHeatK_pair
#check @Carleman.interiorGaussianHeatB_formula
#print axioms Carleman.interiorGaussianHeatB_formula
#check @Carleman.interiorGaussianHeatB_leading
#print axioms Carleman.interiorGaussianHeatB_leading

#check @Carleman.interiorGaussianHeatPhase_second_spatialD
#print axioms Carleman.interiorGaussianHeatPhase_second_spatialD
#check @Carleman.interiorGaussianHeatMatrixEnergy_formula
#print axioms Carleman.interiorGaussianHeatMatrixEnergy_formula
#check @Carleman.interiorGaussianHeatMatrixEnergy_coercive
#print axioms Carleman.interiorGaussianHeatMatrixEnergy_coercive
#check @Carleman.heat_remainder_bound
#print axioms Carleman.heat_remainder_bound
#check @Carleman.interiorHeatLeadingCoefficient
#print axioms Carleman.interiorHeatLeadingCoefficient
#check @Carleman.interiorGaussianHeatB_uniform_lower_bound
#print axioms Carleman.interiorGaussianHeatB_uniform_lower_bound
#check @Carleman.directionalEnergy_nonneg
#print axioms Carleman.directionalEnergy_nonneg
#check @Carleman.directionalPair_young
#print axioms Carleman.directionalPair_young
#check @Carleman.interiorGaussianHeatPsi_uniform_energy_bound
#print axioms Carleman.interiorGaussianHeatPsi_uniform_energy_bound
#check @Carleman.interiorGaussianHeat_mixed_term_bound
#print axioms Carleman.interiorGaussianHeat_mixed_term_bound
#check @Carleman.interiorGaussianHeat_bulk_lower_bound
#print axioms Carleman.interiorGaussianHeat_bulk_lower_bound
#check @Carleman.boxTimeIntegral_const_mul
#print axioms Carleman.boxTimeIntegral_const_mul
#check @Carleman.boxTimeIntegral_mono_on
#print axioms Carleman.boxTimeIntegral_mono_on
#check @Carleman.interiorHeatLeadingCoefficient_continuous
#print axioms Carleman.interiorHeatLeadingCoefficient_continuous
#check @Carleman.box_smooth_gaussian_heat_cross
#print axioms Carleman.box_smooth_gaussian_heat_cross

#check @Carleman.exists_heat_absorption_parameters
#print axioms Carleman.exists_heat_absorption_parameters
#check @Carleman.interiorHeatPotential
#print axioms Carleman.interiorHeatPotential
#check @Carleman.interiorHeatPotential_continuous
#print axioms Carleman.interiorHeatPotential_continuous
#check @Carleman.interiorHeatPotential_positive_outside
#print axioms Carleman.interiorHeatPotential_positive_outside
#check @Carleman.exists_interior_heat_observation_coefficients
#print axioms Carleman.exists_interior_heat_observation_coefficients
#check @Carleman.interiorHeat_observation_absorption
#print axioms Carleman.interiorHeat_observation_absorption
#check @Carleman.continuous_box_observation_integrable
#print axioms Carleman.continuous_box_observation_integrable
#check @Carleman.boxTimeIntegral_observation
#print axioms Carleman.boxTimeIntegral_observation
#check @Carleman.boxTimeIntegral_mono_on_integrable
#print axioms Carleman.boxTimeIntegral_mono_on_integrable
#check @Carleman.boxTimeIntegral_add_integrable
#print axioms Carleman.boxTimeIntegral_add_integrable
#check @Carleman.boxTimeIntegral_nonneg_on
#print axioms Carleman.boxTimeIntegral_nonneg_on
#check @Carleman.box_smooth_gaussian_heat_observation
#print axioms Carleman.box_smooth_gaussian_heat_observation
#check @Carleman.heat_gradient_return
#print axioms Carleman.heat_gradient_return
#check @Carleman.spatial_directionalEnergy_gradient
#print axioms Carleman.spatial_directionalEnergy_gradient
#check @Carleman.spaceTime_directionalEnergy_gradient
#print axioms Carleman.spaceTime_directionalEnergy_gradient
#check @Carleman.interiorGaussianHeatPhase_uniform_energy
#print axioms Carleman.interiorGaussianHeatPhase_uniform_energy
#check @Carleman.interiorGaussianHeat_return_bound
#print axioms Carleman.interiorGaussianHeat_return_bound
#check @Carleman.box_smooth_gaussian_heat_estimate
#print axioms Carleman.box_smooth_gaussian_heat_estimate

#check @Carleman.heatTimeReflection
#print axioms Carleman.heatTimeReflection
#check @Carleman.heatTimeReflection_contDiff
#print axioms Carleman.heatTimeReflection_contDiff
#check @Carleman.heatTimeReflection_involutive
#print axioms Carleman.heatTimeReflection_involutive
#check @Carleman.time_reflection_mem_interval
#print axioms Carleman.time_reflection_mem_interval
#check @Carleman.heatTimeReflection_periodic
#print axioms Carleman.heatTimeReflection_periodic
#check @Carleman.time_reflection_measurePreserving
#print axioms Carleman.time_reflection_measurePreserving
#check @Carleman.heatTimeReflection_measurePreserving
#print axioms Carleman.heatTimeReflection_measurePreserving
#check @Carleman.boxTimeIntegral_reflection
#print axioms Carleman.boxTimeIntegral_reflection
#check @Carleman.deriv_time_reflection
#print axioms Carleman.deriv_time_reflection
#check @Carleman.deriv_deriv_time_reflection
#print axioms Carleman.deriv_deriv_time_reflection
#check @Carleman.spaceTimeHeat_time_reflection
#print axioms Carleman.spaceTimeHeat_time_reflection
#check @Carleman.spaceTimeOrientedHeat
#print axioms Carleman.spaceTimeOrientedHeat
#check @Carleman.spaceTimeHeat_time_reflection_eq
#print axioms Carleman.spaceTimeHeat_time_reflection_eq
#check @Carleman.box_smooth_gaussian_heat_both_signs
#print axioms Carleman.box_smooth_gaussian_heat_both_signs

#check @Carleman.temporalBump
#print axioms Carleman.temporalBump
#check @Carleman.temporalMollification
#print axioms Carleman.temporalMollification
#check @Carleman.temporalMollification_smooth
#print axioms Carleman.temporalMollification_smooth
#check @Carleman.temporalMollification_periodic
#print axioms Carleman.temporalMollification_periodic
#check @Carleman.temporalMollification_bounds
#print axioms Carleman.temporalMollification_bounds
#check @Carleman.temporalBump_radius_tendsto
#print axioms Carleman.temporalBump_radius_tendsto
#check @Carleman.temporalMollification_tendsto
#print axioms Carleman.temporalMollification_tendsto
#check @Carleman.continuous_periodic_bounded
#print axioms Carleman.continuous_periodic_bounded
#check @Carleman.temporalMollification_hasDerivAt
#print axioms Carleman.temporalMollification_hasDerivAt
#check @Carleman.temporalMollification_deriv_periodic
#print axioms Carleman.temporalMollification_deriv_periodic
#check @Carleman.temporalMollification_second_deriv_periodic
#print axioms Carleman.temporalMollification_second_deriv_periodic
#check @Carleman.temporal_derivative_difference
#print axioms Carleman.temporal_derivative_difference
#check @Carleman.temporalMollification_uniform_error
#print axioms Carleman.temporalMollification_uniform_error
#check @Carleman.temporalMollification_local_norm_bound
#print axioms Carleman.temporalMollification_local_norm_bound
#check @Carleman.temporalMollification_support_comparison
#print axioms Carleman.temporalMollification_support_comparison
#check @Carleman.periodic_time_weight_bounds_global
#print axioms Carleman.periodic_time_weight_bounds_global
#check @Carleman.temporalMollification_qclass
#print axioms Carleman.temporalMollification_qclass
#check @Carleman.exists_periodic_C2_smooth_qclass
#print axioms Carleman.exists_periodic_C2_smooth_qclass
#check @Carleman.exists_periodic_C2_smooth_qclass_exact
#print axioms Carleman.exists_periodic_C2_smooth_qclass_exact

#check @Carleman.boxTimeIntegral_tendsto_parameter
#print axioms Carleman.boxTimeIntegral_tendsto_parameter
#check @Carleman.boxTimeIntegral_observation_tendsto_parameter
#print axioms Carleman.boxTimeIntegral_observation_tendsto_parameter
#check @Carleman.box_C2_gaussian_heat_both_signs
#print axioms Carleman.box_C2_gaussian_heat_both_signs

#check @Carleman.exists_continuous_periodic_extension
#print axioms Carleman.exists_continuous_periodic_extension
#check @Carleman.periodic_primitive_of_interval
#print axioms Carleman.periodic_primitive_of_interval
#check @Carleman.exists_periodic_C2_extension
#print axioms Carleman.exists_periodic_C2_extension
#check @Carleman.boxTimeIntegral_congr_on
#print axioms Carleman.boxTimeIntegral_congr_on
#check @Carleman.box_interval_C2_gaussian_heat_both_signs
#print axioms Carleman.box_interval_C2_gaussian_heat_both_signs

#check @Carleman.coordinateReflection_zero
#print axioms Carleman.coordinateReflection_zero
#check @Carleman.coordinateSignFlip_involutive
#print axioms Carleman.coordinateSignFlip_involutive
#check @Carleman.coordinateReflection_sub_fixed
#print axioms Carleman.coordinateReflection_sub_fixed
#check @Carleman.convolution_zero_of_local_odd
#print axioms Carleman.convolution_zero_of_local_odd
#check @Carleman.coordinateSignFlip_commute
#print axioms Carleman.coordinateSignFlip_commute
#check @Carleman.SpatialTest.evenCoordinate
#print axioms Carleman.SpatialTest.evenCoordinate
#check @Carleman.SpatialTest.evenCoordinate_value
#print axioms Carleman.SpatialTest.evenCoordinate_value
#check @Carleman.SpatialTest.evenCoordinate_invariant
#print axioms Carleman.SpatialTest.evenCoordinate_invariant
#check @Carleman.SpatialTest.evenCoordinate_preserves_invariant
#print axioms Carleman.SpatialTest.evenCoordinate_preserves_invariant
#check @Carleman.SpatialTest.evenCoordinate_nonneg
#print axioms Carleman.SpatialTest.evenCoordinate_nonneg
#check @Carleman.SpatialTest.evenCoordinate_integral
#print axioms Carleman.SpatialTest.evenCoordinate_integral
#check @Carleman.SpatialTest.evenCoordinate_support
#print axioms Carleman.SpatialTest.evenCoordinate_support
#check @Carleman.SpatialTest.evenCoordinates
#print axioms Carleman.SpatialTest.evenCoordinates
#check @Carleman.SpatialTest.evenCoordinates_invariant
#print axioms Carleman.SpatialTest.evenCoordinates_invariant
#check @Carleman.SpatialTest.evenCoordinates_nonneg
#print axioms Carleman.SpatialTest.evenCoordinates_nonneg
#check @Carleman.SpatialTest.evenCoordinates_integral
#print axioms Carleman.SpatialTest.evenCoordinates_integral
#check @Carleman.SpatialTest.evenCoordinates_support
#print axioms Carleman.SpatialTest.evenCoordinates_support
#check @Carleman.evenSpatialMollifier
#print axioms Carleman.evenSpatialMollifier
#check @Carleman.evenSpatialMollifier_invariant
#print axioms Carleman.evenSpatialMollifier_invariant
#check @Carleman.evenSpatialMollifier_nonneg
#print axioms Carleman.evenSpatialMollifier_nonneg
#check @Carleman.evenSpatialMollifier_integral
#print axioms Carleman.evenSpatialMollifier_integral
#check @Carleman.evenSpatialMollifier_support
#print axioms Carleman.evenSpatialMollifier_support
#check @Carleman.evenSpatialMollifier_convolution_zero
#print axioms Carleman.evenSpatialMollifier_convolution_zero
#check @Carleman.SpatialTest.reflected_kernel_convolution
#print axioms Carleman.SpatialTest.reflected_kernel_convolution
#check @Carleman.SpatialTest.evenCoordinate_convolution
#print axioms Carleman.SpatialTest.evenCoordinate_convolution
#check @Carleman.SpatialTest.evenCoordinates_converges
#print axioms Carleman.SpatialTest.evenCoordinates_converges
#check @Carleman.evenSpatialMollifier_converges
#print axioms Carleman.evenSpatialMollifier_converges
#check @Carleman.evenSpatialMollifier_square_error_tendsto
#print axioms Carleman.evenSpatialMollifier_square_error_tendsto
#check @Carleman.evenSpatialMollifier_L2_error_tendsto
#print axioms Carleman.evenSpatialMollifier_L2_error_tendsto

#check @Carleman.evenSpatialMollifier_tsupport_subset
#print axioms Carleman.evenSpatialMollifier_tsupport_subset
#check @Carleman.evenSpatialMollifier_L2_error_restrict_tendsto
#print axioms Carleman.evenSpatialMollifier_L2_error_restrict_tendsto
#check @Carleman.IsWeakSpatialDerivative.local_even_mollification_strong_first
#print axioms Carleman.IsWeakSpatialDerivative.local_even_mollification_strong_first
#check @Carleman.IsWeakSpatialDerivative.local_even_mollification_strong_second
#print axioms Carleman.IsWeakSpatialDerivative.local_even_mollification_strong_second
#check @Carleman.coordinateReflection_commute
#print axioms Carleman.coordinateReflection_commute
#check @Carleman.coordinateOddPart
#print axioms Carleman.coordinateOddPart
#check @Carleman.coordinateOddPart_ae
#print axioms Carleman.coordinateOddPart_ae
#check @Carleman.IsOddInSlab
#print axioms Carleman.IsOddInSlab
#check @Carleman.coordinateOddPart_odd
#print axioms Carleman.coordinateOddPart_odd
#check @Carleman.IsOddInSlab.oddPart_other
#print axioms Carleman.IsOddInSlab.oddPart_other
#check @Carleman.IsZeroOutsideSlab
#print axioms Carleman.IsZeroOutsideSlab
#check @Carleman.zeroExtend_box_zero_outside_slab
#print axioms Carleman.zeroExtend_box_zero_outside_slab
#check @Carleman.IsZeroOutsideSlab.lower_oddPart
#print axioms Carleman.IsZeroOutsideSlab.lower_oddPart
#check @Carleman.IsZeroOutsideSlab.double_oddPart_lower
#print axioms Carleman.IsZeroOutsideSlab.double_oddPart_lower
#check @Carleman.double_oddPart_both_faces
#print axioms Carleman.double_oddPart_both_faces
#check @Carleman.zeroExtend_restrict_of_zero_outside
#print axioms Carleman.zeroExtend_restrict_of_zero_outside
#check @Carleman.oddExtendLp_zero_outside
#print axioms Carleman.oddExtendLp_zero_outside
#check @Carleman.exists_odd_dirichlet_extension_value
#print axioms Carleman.exists_odd_dirichlet_extension_value
#check @Carleman.exists_lower_box_extension_value
#print axioms Carleman.exists_lower_box_extension_value
#check @Carleman.exists_upper_box_extension_value
#print axioms Carleman.exists_upper_box_extension_value
#check @Carleman.exists_finite_odd_box_extension
#print axioms Carleman.exists_finite_odd_box_extension
#check @Carleman.IsOddInSlab.even_mollification_zero
#print axioms Carleman.IsOddInSlab.even_mollification_zero
#check @Carleman.frontier_box_has_coordinate_face
#print axioms Carleman.frontier_box_has_coordinate_face
#check @Carleman.even_mollification_eventually_zero_boundary
#print axioms Carleman.even_mollification_eventually_zero_boundary
#check @Carleman.exists_box_poisson_extension_smooth_boundary
#print axioms Carleman.exists_box_poisson_extension_smooth_boundary

#check @Carleman.WeakSobolevJet.local_even_mollification_strong_h2
#print axioms Carleman.WeakSobolevJet.local_even_mollification_strong_h2
#check @Carleman.local_L2_error_restrict_tendsto
#print axioms Carleman.local_L2_error_restrict_tendsto
#check @Carleman.WeakSobolevJet.restrictSubdomain_component_ae
#print axioms Carleman.WeakSobolevJet.restrictSubdomain_component_ae
#check @Carleman.exists_box_dirichlet_smooth_h2_approximation
#print axioms Carleman.exists_box_dirichlet_smooth_h2_approximation

#check @Carleman.coordinateDerivative_eqOn_of_eqOn
#print axioms Carleman.coordinateDerivative_eqOn_of_eqOn
#check @Carleman.exists_box_dirichlet_compact_h2_approximation
#print axioms Carleman.exists_box_dirichlet_compact_h2_approximation
#check @Carleman.lp_tendsto_of_representative_L2_error
#print axioms Carleman.lp_tendsto_of_representative_L2_error
#check @Carleman.coordinateDerivative_two_diagonal
#print axioms Carleman.coordinateDerivative_two_diagonal
#check @Carleman.SpatialTest.laplacianOnLp
#print axioms Carleman.SpatialTest.laplacianOnLp
#check @Carleman.SpatialTest.laplacianOnLp_ae
#print axioms Carleman.SpatialTest.laplacianOnLp_ae
#check @Carleman.SpatialTest.laplacianOnLp_tendsto
#print axioms Carleman.SpatialTest.laplacianOnLp_tendsto
#check @Carleman.SpatialTest.laplacianOnLp_eq_subdomain
#print axioms Carleman.SpatialTest.laplacianOnLp_eq_subdomain
#check @Carleman.SpatialTest.exists_dirichlet_domain_of_boundary
#print axioms Carleman.SpatialTest.exists_dirichlet_domain_of_boundary
#check @Carleman.exists_box_smooth_operator_graph_approximation
#print axioms Carleman.exists_box_smooth_operator_graph_approximation

#check @Carleman.CoerciveForm.harmonicGraph
#print axioms Carleman.CoerciveForm.harmonicGraph
#check @Carleman.CoerciveForm.harmonicGraph_trace
#print axioms Carleman.CoerciveForm.harmonicGraph_trace
#check @Carleman.CoerciveForm.harmonicGraphLinear
#print axioms Carleman.CoerciveForm.harmonicGraphLinear
#check @Carleman.CoerciveForm.harmonicGraph_continuous
#print axioms Carleman.CoerciveForm.harmonicGraph_continuous
#check @Carleman.CoerciveForm.harmonicGraphCLM
#print axioms Carleman.CoerciveForm.harmonicGraphCLM
#check @Carleman.CoerciveForm.harmonicGraph_mem_core
#print axioms Carleman.CoerciveForm.harmonicGraph_mem_core
#check @Carleman.CoerciveForm.harmonicStateSpan
#print axioms Carleman.CoerciveForm.harmonicStateSpan
#check @Carleman.CoerciveForm.harmonicStateSpan_le_core
#print axioms Carleman.CoerciveForm.harmonicStateSpan_le_core
#check @Carleman.CoerciveForm.frequencyGraph_mem_harmonicStateSpan
#print axioms Carleman.CoerciveForm.frequencyGraph_mem_harmonicStateSpan
#check @Carleman.CoerciveForm.constantSolve_harmonic_mem
#print axioms Carleman.CoerciveForm.constantSolve_harmonic_mem
#check @Carleman.CoerciveForm.harmonicStateSpan_dense
#print axioms Carleman.CoerciveForm.harmonicStateSpan_dense
#check @Carleman.CoerciveForm.dense_of_harmonic_approximation
#print axioms Carleman.CoerciveForm.dense_of_harmonic_approximation
#check @Carleman.smoothDirichletTimeCore
#print axioms Carleman.smoothDirichletTimeCore
#check @Carleman.harmonicGraph_mem_smoothDirichletTimeCore
#print axioms Carleman.harmonicGraph_mem_smoothDirichletTimeCore
#check @Carleman.box_smoothDirichletTimeCore_dense
#print axioms Carleman.box_smoothDirichletTimeCore_dense
#check @Carleman.exists_box_smooth_periodic_graph_approximation
#print axioms Carleman.exists_box_smooth_periodic_graph_approximation

#check @Carleman.directionalLap_add
#print axioms Carleman.directionalLap_add
#check @Carleman.directionalLap_const_mul
#print axioms Carleman.directionalLap_const_mul
#check @Carleman.directionalLap_zero
#print axioms Carleman.directionalLap_zero
#check @Carleman.spatialLaplacian_add
#print axioms Carleman.spatialLaplacian_add
#check @Carleman.spatialLaplacian_const_mul
#print axioms Carleman.spatialLaplacian_const_mul
#check @Carleman.smooth_harmonic_time_derivative
#print axioms Carleman.smooth_harmonic_time_derivative
#check @Carleman.smooth_harmonic_spatial_laplacian
#print axioms Carleman.smooth_harmonic_spatial_laplacian
#check @Carleman.CoerciveForm.harmonicGraph_derivative_ae
#print axioms Carleman.CoerciveForm.harmonicGraph_derivative_ae
#check @Carleman.CoerciveForm.harmonicGraph_operator_ae
#print axioms Carleman.CoerciveForm.harmonicGraph_operator_ae
#check @Carleman.classicalDirichletTimeCore
#print axioms Carleman.classicalDirichletTimeCore
#check @Carleman.harmonicGraph_mem_classicalDirichletTimeCore
#print axioms Carleman.harmonicGraph_mem_classicalDirichletTimeCore
#check @Carleman.box_classicalDirichletTimeCore_dense
#print axioms Carleman.box_classicalDirichletTimeCore_dense
#check @Carleman.exists_box_classical_periodic_graph_approximation
#print axioms Carleman.exists_box_classical_periodic_graph_approximation

#check @Carleman.SpatialProfile.weightedTimeCLM
#print axioms Carleman.SpatialProfile.weightedTimeCLM
#check @Carleman.SpatialProfile.timeSq_eq_weightedTimeCLM_norm_sq
#print axioms Carleman.SpatialProfile.timeSq_eq_weightedTimeCLM_norm_sq
#check @Carleman.SpatialProfile.continuous_timeSq
#print axioms Carleman.SpatialProfile.continuous_timeSq
#check @Carleman.CoerciveForm.periodicEnergy
#print axioms Carleman.CoerciveForm.periodicEnergy
#check @Carleman.CoerciveForm.periodicEnergy_eq
#print axioms Carleman.CoerciveForm.periodicEnergy_eq
#check @Carleman.CoerciveForm.periodicEnergy_embed
#print axioms Carleman.CoerciveForm.periodicEnergy_embed
#check @Carleman.CoerciveForm.periodicEnergy_embed_ae
#print axioms Carleman.CoerciveForm.periodicEnergy_embed_ae
#check @Carleman.SpatialTest.sobolevJet_component_ae
#print axioms Carleman.SpatialTest.sobolevJet_component_ae
#check @Carleman.WeakSobolevJet.component_eq_smooth_derivative
#print axioms Carleman.WeakSobolevJet.component_eq_smooth_derivative
#check @Carleman.WeakSobolevJet.gradient_norm_sq_eq_smooth
#print axioms Carleman.WeakSobolevJet.gradient_norm_sq_eq_smooth
#check @Carleman.dirichletPeriodicGradient
#print axioms Carleman.dirichletPeriodicGradient
#check @Carleman.dirichletPeriodicGradient_ae
#print axioms Carleman.dirichletPeriodicGradient_ae
#check @Carleman.dirichletPeriodicGradient_smooth_norm
#print axioms Carleman.dirichletPeriodicGradient_smooth_norm
#check @Carleman.dirichletHeatLeft
#print axioms Carleman.dirichletHeatLeft
#check @Carleman.dirichletHeatRight
#print axioms Carleman.dirichletHeatRight
#check @Carleman.continuous_dirichletHeatLeft
#print axioms Carleman.continuous_dirichletHeatLeft
#check @Carleman.continuous_dirichletHeatRight
#print axioms Carleman.continuous_dirichletHeatRight
#check @Carleman.box_dirichletHeat_le_of_classical
#print axioms Carleman.box_dirichletHeat_le_of_classical

#check @Carleman.weighted_box_density_integrable
#print axioms Carleman.weighted_box_density_integrable
#check @Carleman.timeSq_eq_boxTimeIntegral_of_norm_sq
#print axioms Carleman.timeSq_eq_boxTimeIntegral_of_norm_sq
#check @Carleman.timeSq_eq_boxTimeIntegral_of_continuous
#print axioms Carleman.timeSq_eq_boxTimeIntegral_of_continuous
#check @Carleman.timeSq_eq_boxTimeIntegral_of_indicator
#print axioms Carleman.timeSq_eq_boxTimeIntegral_of_indicator
#check @Carleman.periodicGraph_value_classical_ae
#print axioms Carleman.periodicGraph_value_classical_ae
#check @Carleman.periodicGraph_residual_classical_ae
#print axioms Carleman.periodicGraph_residual_classical_ae
#check @Carleman.periodicGraph_observation_classical_ae
#print axioms Carleman.periodicGraph_observation_classical_ae
#check @Carleman.smooth_spatial_gradient_sq_continuous
#print axioms Carleman.smooth_spatial_gradient_sq_continuous
#check @Carleman.smooth_oriented_heat_continuous
#print axioms Carleman.smooth_oriented_heat_continuous
#check @Carleman.dirichletHeatLeft_eq_boxIntegral
#print axioms Carleman.dirichletHeatLeft_eq_boxIntegral
#check @Carleman.dirichletHeatRight_eq_boxIntegral
#print axioms Carleman.dirichletHeatRight_eq_boxIntegral
#check @Carleman.box_weak_C2_gaussian_heat_both_signs
#print axioms Carleman.box_weak_C2_gaussian_heat_both_signs

#check @Carleman.exists_timeWeight_eqOn_interval
#print axioms Carleman.exists_timeWeight_eqOn_interval
#check @Carleman.eqOn_interval_within_derivatives
#print axioms Carleman.eqOn_interval_within_derivatives
#check @Carleman.SpatialProfile.zero_multiplier_seminorm_eq_exp
#print axioms Carleman.SpatialProfile.zero_multiplier_seminorm_eq_exp
#check @Carleman.SpatialProfile.timeSq_eq_exp_of_eqOn
#print axioms Carleman.SpatialProfile.timeSq_eq_exp_of_eqOn
#check @Carleman.dirichletIntervalHeatLeft
#print axioms Carleman.dirichletIntervalHeatLeft
#check @Carleman.dirichletIntervalHeatRight
#print axioms Carleman.dirichletIntervalHeatRight
#check @Carleman.dirichletHeatLeft_eq_interval
#print axioms Carleman.dirichletHeatLeft_eq_interval
#check @Carleman.dirichletHeatRight_eq_interval
#print axioms Carleman.dirichletHeatRight_eq_interval
#check @Carleman.box_weak_interval_C2_gaussian_heat_both_signs
#print axioms Carleman.box_weak_interval_C2_gaussian_heat_both_signs
#check @Carleman.dirichletTrajectory_gradient_ae
#print axioms Carleman.dirichletTrajectory_gradient_ae
#check @Carleman.dirichletTrajectory_gradient_memLp
#print axioms Carleman.dirichletTrajectory_gradient_memLp
#check @Carleman.dirichletIntervalHeatLeft_trajectory
#print axioms Carleman.dirichletIntervalHeatLeft_trajectory
#check @Carleman.dirichletIntervalHeatRight_trajectory
#print axioms Carleman.dirichletIntervalHeatRight_trajectory
#check @Carleman.box_original_weak_C2_heat_both_signs
#print axioms Carleman.box_original_weak_C2_heat_both_signs

#check @Carleman.heatGradientExpression
#print axioms Carleman.heatGradientExpression
#check @Carleman.heatGradientExpression_apply
#print axioms Carleman.heatGradientExpression_apply
#check @Carleman.heatDifferentialFamily
#print axioms Carleman.heatDifferentialFamily
#check @Carleman.conforming_heat_expression
#print axioms Carleman.conforming_heat_expression
#check @Carleman.dirichlet_conforming_gradient
#print axioms Carleman.dirichlet_conforming_gradient
#check @Carleman.dirichletHeatGeometry_energy
#print axioms Carleman.dirichletHeatGeometry_energy
#check @Carleman.dirichletHeatGeometry_residual
#print axioms Carleman.dirichletHeatGeometry_residual
#check @Carleman.dirichletHeatGeometry_observation
#print axioms Carleman.dirichletHeatGeometry_observation
#check @Carleman.IntervalQClass
#print axioms Carleman.IntervalQClass
#check @Carleman.IntervalQClass.toRegularity
#print axioms Carleman.IntervalQClass.toRegularity
#check @Carleman.box_heat_continuous_data
#print axioms Carleman.box_heat_continuous_data

#check @Carleman.cartesianLoadInterfaceOn
#print axioms Carleman.cartesianLoadInterfaceOn
#check @Carleman.cartesianLoadInterfaceOn_Γ
#print axioms Carleman.cartesianLoadInterfaceOn_Γ
#check @Carleman.cartesianHeatState_definite
#print axioms Carleman.cartesianHeatState_definite
#check @Carleman.cartesianHeatControl_definite
#print axioms Carleman.cartesianHeatControl_definite
#check @Carleman.cartesianHeatGeometry
#print axioms Carleman.cartesianHeatGeometry
#check @Carleman.cartesian_numericalData_on
#print axioms Carleman.cartesian_numericalData_on
#check @Carleman.box_cartesian_heat_estimate
#print axioms Carleman.box_cartesian_heat_estimate

#check @Carleman.PhysicalFiniteSpace.finiteMemLp
#print axioms Carleman.PhysicalFiniteSpace.finiteMemLp
#check @Carleman.PhysicalFiniteSpace.toCountLp
#print axioms Carleman.PhysicalFiniteSpace.toCountLp
#check @Carleman.PhysicalFiniteSpace.toCountLp_apply
#print axioms Carleman.PhysicalFiniteSpace.toCountLp_apply
#check @Carleman.PhysicalFiniteSpace.toCountLpLinear
#print axioms Carleman.PhysicalFiniteSpace.toCountLpLinear
#check @Carleman.PhysicalFiniteSpace.toCountLp_norm
#print axioms Carleman.PhysicalFiniteSpace.toCountLp_norm
#check @Carleman.PhysicalFiniteSpace.countLpEquiv
#print axioms Carleman.PhysicalFiniteSpace.countLpEquiv
#check @Carleman.PhysicalFiniteSpace.countLpEquiv_apply
#print axioms Carleman.PhysicalFiniteSpace.countLpEquiv_apply
#check @Carleman.BoundedMultiplier.ofFinite
#print axioms Carleman.BoundedMultiplier.ofFinite
#check @Carleman.SpatialProfile.ofFinite
#print axioms Carleman.SpatialProfile.ofFinite
#check @Carleman.PhysicalFiniteSpace.countLpEquiv_multiplier
#print axioms Carleman.PhysicalFiniteSpace.countLpEquiv_multiplier
#check @Carleman.PhysicalFiniteSpace.countLpEquiv_weighted_norm
#print axioms Carleman.PhysicalFiniteSpace.countLpEquiv_weighted_norm
#check @Carleman.PhysicalFiniteSpace.countLpEquiv_symm_map
#print axioms Carleman.PhysicalFiniteSpace.countLpEquiv_symm_map
#check @Carleman.PhysicalFiniteSpace.multiplier_symmetric
#print axioms Carleman.PhysicalFiniteSpace.multiplier_symmetric
#check @Carleman.PhysicalFiniteSpace.multiplier_opNorm_le
#print axioms Carleman.PhysicalFiniteSpace.multiplier_opNorm_le
#check @Carleman.smooth_interval_derivatives
#print axioms Carleman.smooth_interval_derivatives
#check @Carleman.Physical.PhysicalQClass.toInterval
#print axioms Carleman.Physical.PhysicalQClass.toInterval


-- T169: actual Cartesian physical load estimate.
#check @Carleman.cartesianPhysicalControl_adjoint_extension
#print axioms Carleman.cartesianPhysicalControl_adjoint_extension
#check @Carleman.cartesianPhysicalControlExtension_norm
#print axioms Carleman.cartesianPhysicalControlExtension_norm
#check @Carleman.cartesianPhysicalControlExtension_weight
#print axioms Carleman.cartesianPhysicalControlExtension_weight
#check @Carleman.cartesianPhysicalControlExtension_seminorm
#print axioms Carleman.cartesianPhysicalControlExtension_seminorm
#check @Carleman.cartesianCountLpEquiv
#print axioms Carleman.cartesianCountLpEquiv
#check @Carleman.cartesianCountObservation
#print axioms Carleman.cartesianCountObservation
#check @Carleman.cartesianCountObservation_norm
#print axioms Carleman.cartesianCountObservation_norm
#check @Carleman.cartesianCountProfile
#print axioms Carleman.cartesianCountProfile
#check @Carleman.cartesianCountProfile_seminorm
#print axioms Carleman.cartesianCountProfile_seminorm
#check @Carleman.cartesianCountProfile_observation
#print axioms Carleman.cartesianCountProfile_observation
#check @Carleman.cartesianInteriorCountProfile
#print axioms Carleman.cartesianInteriorCountProfile
#check @Carleman.cartesianInteriorCountProfile_negative
#print axioms Carleman.cartesianInteriorCountProfile_negative
#check @Carleman.box_cartesian_physical_load_carleman
#print axioms Carleman.box_cartesian_physical_load_carleman


-- T170: actual Cartesian physical observation and control.
#check @Carleman.Physical.physical_observation_uniform_profiles
#print axioms Carleman.Physical.physical_observation_uniform_profiles
#check @Carleman.Physical.box_cartesian_physical_observability
#print axioms Carleman.Physical.box_cartesian_physical_observability
#check @Carleman.Physical.box_cartesian_physical_control
#print axioms Carleman.Physical.box_cartesian_physical_control


-- T171: original terminal filtering and actual Cartesian observation.
#check @Carleman.Physical.filter_condition_budget
#print axioms Carleman.Physical.filter_condition_budget
#check @Carleman.Physical.filtered_observation_of_relaxed
#print axioms Carleman.Physical.filtered_observation_of_relaxed
#check @Carleman.Physical.box_cartesian_filtered_observability
#print axioms Carleman.Physical.box_cartesian_filtered_observability

-- T172: actual complementary HUM and full Cartesian filtered controls.
#check @Carleman.Physical.complementaryHumOperator
#print axioms Carleman.Physical.complementaryHumOperator
#check @Carleman.Physical.complementaryHumOperator_pairing
#print axioms Carleman.Physical.complementaryHumOperator_pairing
#check @Carleman.Physical.complementaryHumOperator_bijective
#print axioms Carleman.Physical.complementaryHumOperator_bijective
#check @Carleman.Physical.complementary_hum_optimality
#print axioms Carleman.Physical.complementary_hum_optimality
#check @Carleman.Physical.complementary_hum_control
#print axioms Carleman.Physical.complementary_hum_control
#check @Carleman.Physical.complementaryPenalty
#print axioms Carleman.Physical.complementaryPenalty
#check @Carleman.Physical.complementaryPenalty_sq
#print axioms Carleman.Physical.complementaryPenalty_sq
#check @Carleman.Physical.complementaryPenalty_pos
#print axioms Carleman.Physical.complementaryPenalty_pos
#check @Carleman.Physical.complementary_terminal_bound
#print axioms Carleman.Physical.complementary_terminal_bound
#check @Carleman.Physical.complementary_observation_of_relaxed
#print axioms Carleman.Physical.complementary_observation_of_relaxed
#check @Carleman.Physical.physical_complementary_hum_control
#print axioms Carleman.Physical.physical_complementary_hum_control
#check @Carleman.Physical.filtered_control_of_relaxed
#print axioms Carleman.Physical.filtered_control_of_relaxed
#check @Carleman.Physical.filterTerminalFactor
#print axioms Carleman.Physical.filterTerminalFactor
#check @Carleman.Physical.filterTerminalFactor_nonneg
#print axioms Carleman.Physical.filterTerminalFactor_nonneg
#check @Carleman.Physical.filter_terminal_constant_budget
#print axioms Carleman.Physical.filter_terminal_constant_budget
#check @Carleman.Physical.filterRayleigh_nonneg
#print axioms Carleman.Physical.filterRayleigh_nonneg
#check @Carleman.Physical.filterConstant_ge_one
#print axioms Carleman.Physical.filterConstant_ge_one
#check @Carleman.Physical.complementaryPenalty_le
#print axioms Carleman.Physical.complementaryPenalty_le
#check @Carleman.Physical.filter_penalty_decay
#print axioms Carleman.Physical.filter_penalty_decay
#check @Carleman.Physical.box_cartesian_filtered_control
#print axioms Carleman.Physical.box_cartesian_filtered_control

-- T173: full consistent-mass P1 physical load estimate on boxes.
#check @Carleman.Physical.box_p1_physical_load_carleman
#print axioms Carleman.Physical.box_p1_physical_load_carleman

-- T174: full P1 physical and terminal-filtered regional control.
#check @Carleman.Physical.PhysicalObservationControl
#print axioms Carleman.Physical.PhysicalObservationControl
#check @Carleman.Physical.PhysicalFilteredObservationControl
#print axioms Carleman.Physical.PhysicalFilteredObservationControl
#check @Carleman.Physical.box_p1_physical_observation_control
#print axioms Carleman.Physical.box_p1_physical_observation_control
#check @Carleman.Physical.box_p1_filtered_observation_control
#print axioms Carleman.Physical.box_p1_filtered_observation_control

-- T175: actual dual-cell isometry, control pairing and cell averaging.
#check @Carleman.cartesianDualCell
#print axioms Carleman.cartesianDualCell
#check @Carleman.cartesianDualCell_measurable
#print axioms Carleman.cartesianDualCell_measurable
#check @Carleman.cartesianDualCell_subset
#print axioms Carleman.cartesianDualCell_subset
#check @Carleman.cartesianDualCell_disjoint
#print axioms Carleman.cartesianDualCell_disjoint
#check @Carleman.cartesianDualCell_volume
#print axioms Carleman.cartesianDualCell_volume
#check @Carleman.cartesianDualCell_restrict_volume
#print axioms Carleman.cartesianDualCell_restrict_volume
#check @Carleman.finiteCellLinear
#print axioms Carleman.finiteCellLinear
#check @Carleman.finiteCellLinear_ae
#print axioms Carleman.finiteCellLinear_ae
#check @Carleman.finiteCellLinear_inner
#print axioms Carleman.finiteCellLinear_inner
#check @Carleman.finiteCellIsometry
#print axioms Carleman.finiteCellIsometry
#check @Carleman.finiteCellLinear_pairing
#print axioms Carleman.finiteCellLinear_pairing
#check @Carleman.finiteCellIsometry_adjoint
#print axioms Carleman.finiteCellIsometry_adjoint
#check @Carleman.finiteCellIsometry_average_norm
#print axioms Carleman.finiteCellIsometry_average_norm
#check @Carleman.cartesianCellIsometry
#print axioms Carleman.cartesianCellIsometry
#check @Carleman.cartesianCellIsometry_ae
#print axioms Carleman.cartesianCellIsometry_ae
#check @Carleman.cartesianCellIsometry_inner
#print axioms Carleman.cartesianCellIsometry_inner
#check @Carleman.cartesianCellControl
#print axioms Carleman.cartesianCellControl
#check @Carleman.cartesianCellControl_norm
#print axioms Carleman.cartesianCellControl_norm
#check @Carleman.cartesianCellControl_pairing
#print axioms Carleman.cartesianCellControl_pairing
#check @Carleman.cartesianCellIsometry_adjoint_average
#print axioms Carleman.cartesianCellIsometry_adjoint_average
#check @Carleman.cartesianCellIsometry_average_norm
#print axioms Carleman.cartesianCellIsometry_average_norm

#check @Carleman.BoundedMultiplier.ofMeasureLE
#print axioms Carleman.BoundedMultiplier.ofMeasureLE
#check @Carleman.BoundedMultiplier.ofMeasureLE_bound
#print axioms Carleman.BoundedMultiplier.ofMeasureLE_bound
#check @Carleman.BoundedMultiplier.integrable
#print axioms Carleman.BoundedMultiplier.integrable
#check @Carleman.BoundedMultiplier.averageFirst
#print axioms Carleman.BoundedMultiplier.averageFirst
#check @Carleman.BoundedMultiplier.averageFirst_bound
#print axioms Carleman.BoundedMultiplier.averageFirst_bound
#check @Carleman.BoundedMultiplier.averageFirst_congr
#print axioms Carleman.BoundedMultiplier.averageFirst_congr
#check @Carleman.BoundedMultiplier.setAverage_bound
#print axioms Carleman.BoundedMultiplier.setAverage_bound
#check @Carleman.BoundedMultiplier.averageFirst_setIntegral
#print axioms Carleman.BoundedMultiplier.averageFirst_setIntegral
#check @Carleman.TimeGrid.physicalTimeCell
#print axioms Carleman.TimeGrid.physicalTimeCell
#check @Carleman.TimeGrid.physicalTimeCell_finite
#print axioms Carleman.TimeGrid.physicalTimeCell_finite
#check @Carleman.TimeGrid.physicalTimeCell_subset
#print axioms Carleman.TimeGrid.physicalTimeCell_subset
#check @Carleman.TimeGrid.physicalTimeCell_volume
#print axioms Carleman.TimeGrid.physicalTimeCell_volume
#check @Carleman.TimeGrid.physicalTimeCell_restrict_le
#print axioms Carleman.TimeGrid.physicalTimeCell_restrict_le
#check @Carleman.timeCellPotential
#print axioms Carleman.timeCellPotential
#check @Carleman.timeCellPotential_value
#print axioms Carleman.timeCellPotential_value
#check @Carleman.timeCellPotential_bound
#print axioms Carleman.timeCellPotential_bound
#check @Carleman.timeCellPotential_congr
#print axioms Carleman.timeCellPotential_congr
#check @Carleman.timeCellPotential_setIntegral
#print axioms Carleman.timeCellPotential_setIntegral
#check @Carleman.cartesianAveragedPotential
#print axioms Carleman.cartesianAveragedPotential
#check @Carleman.cartesianAveragedPotential_formula
#print axioms Carleman.cartesianAveragedPotential_formula
#check @Carleman.cartesianAveragedPotential_bound
#print axioms Carleman.cartesianAveragedPotential_bound
#check @Carleman.cartesianAveragedPotentialMultiplier
#print axioms Carleman.cartesianAveragedPotentialMultiplier
#check @Carleman.cartesianAveragedPotential_congr
#print axioms Carleman.cartesianAveragedPotential_congr
#check @Carleman.cartesianAveragedPotential_operator_norm
#print axioms Carleman.cartesianAveragedPotential_operator_norm
#check @Carleman.cartesianAveragedPotential_operator_symmetric
#print axioms Carleman.cartesianAveragedPotential_operator_symmetric

#check @Carleman.TimeGrid.physicalTimeCell_disjoint
#print axioms Carleman.TimeGrid.physicalTimeCell_disjoint
#check @Carleman.TimeGrid.physicalTimeCell_restrict_volume
#print axioms Carleman.TimeGrid.physicalTimeCell_restrict_volume
#check @Carleman.timeCellReconstruction
#print axioms Carleman.timeCellReconstruction
#check @Carleman.timeCellReconstruction_ae
#print axioms Carleman.timeCellReconstruction_ae
#check @Carleman.timeCellReconstruction_inner
#print axioms Carleman.timeCellReconstruction_inner
#check @Carleman.timeCellReconstruction_norm
#print axioms Carleman.timeCellReconstruction_norm
#check @Carleman.timeCellReconstruction_on_cell
#print axioms Carleman.timeCellReconstruction_on_cell
#check @Carleman.reconstructedControl
#print axioms Carleman.reconstructedControl
#check @Carleman.reconstructedControl_norm
#print axioms Carleman.reconstructedControl_norm
#check @Carleman.reconstructedControl_on_cell
#print axioms Carleman.reconstructedControl_on_cell
#check @Carleman.reconstructed_controls_weak_subsequence
#print axioms Carleman.reconstructed_controls_weak_subsequence
#check @Carleman.Physical.conformingTimeControl_norm
#print axioms Carleman.Physical.conformingTimeControl_norm
#check @Carleman.Physical.conformingTimeControl_on_cell
#print axioms Carleman.Physical.conformingTimeControl_on_cell
#check @Carleman.Physical.conformingTimeControl_pairing
#print axioms Carleman.Physical.conformingTimeControl_pairing
#check @Carleman.cartesianTimeControl_norm
#print axioms Carleman.cartesianTimeControl_norm
#check @Carleman.cartesianTimeControl_pairing
#print axioms Carleman.cartesianTimeControl_pairing

#check @Carleman.cartesianDualCell_dist_le
#print axioms Carleman.cartesianDualCell_dist_le
#check @Carleman.cartesianDualCell_subset_region
#print axioms Carleman.cartesianDualCell_subset_region
#check @Carleman.cartesianCellControl_zero_outside
#print axioms Carleman.cartesianCellControl_zero_outside
#check @Carleman.cartesianCellControl_support_small_mesh
#print axioms Carleman.cartesianCellControl_support_small_mesh
#check @Carleman.Physical.supportedRegionSpace
#print axioms Carleman.Physical.supportedRegionSpace
#check @Carleman.Physical.supportedRegionSpace_closed
#print axioms Carleman.Physical.supportedRegionSpace_closed
#check @Carleman.Physical.mem_supportedRegionSpace_iff
#print axioms Carleman.Physical.mem_supportedRegionSpace_iff
#check @Carleman.Physical.zeroExtend_restrict_of_supported
#print axioms Carleman.Physical.zeroExtend_restrict_of_supported
#check @Carleman.bochnerKernelSpace
#print axioms Carleman.bochnerKernelSpace
#check @Carleman.bochnerKernelSpace_closed
#print axioms Carleman.bochnerKernelSpace_closed
#check @Carleman.mem_bochnerKernelSpace_iff
#print axioms Carleman.mem_bochnerKernelSpace_iff
#check @Carleman.timeCellReconstruction_mem_bochnerKernel
#print axioms Carleman.timeCellReconstruction_mem_bochnerKernel
#check @Carleman.exists_bochnerKernel_weak_subsequence
#print axioms Carleman.exists_bochnerKernel_weak_subsequence
#check @Carleman.bochnerKernel_of_weak_tendsto
#print axioms Carleman.bochnerKernel_of_weak_tendsto
#check @Carleman.cartesianTimeControl_supported
#print axioms Carleman.cartesianTimeControl_supported
#check @Carleman.cartesianTimeControl_supported_small_mesh
#print axioms Carleman.cartesianTimeControl_supported_small_mesh
#check @Carleman.supportedBochner_zeroExtension
#print axioms Carleman.supportedBochner_zeroExtension
#check @Carleman.exists_regional_control_weak_subsequence
#print axioms Carleman.exists_regional_control_weak_subsequence

#check @Carleman.reconstruction_adjoint_left_inverse
#print axioms Carleman.reconstruction_adjoint_left_inverse
#check @Carleman.reconstruction_residual_orthogonal
#print axioms Carleman.reconstruction_residual_orthogonal
#check @Carleman.reconstruction_error_pythagoras
#print axioms Carleman.reconstruction_error_pythagoras
#check @Carleman.reconstruction_best_approximation
#print axioms Carleman.reconstruction_best_approximation
#check @Carleman.finiteCells_union_volume
#print axioms Carleman.finiteCells_union_volume
#check @Carleman.finiteCellLinear_error_bound
#print axioms Carleman.finiteCellLinear_error_bound
#check @Carleman.finiteCell_average_error_bound
#print axioms Carleman.finiteCell_average_error_bound
#check @Carleman.cartesianDualCells_union_volume
#print axioms Carleman.cartesianDualCells_union_volume
#check @Carleman.cartesianDualCells_uncovered_volume
#print axioms Carleman.cartesianDualCells_uncovered_volume
#check @Carleman.cartesianCell_average_continuous_error
#print axioms Carleman.cartesianCell_average_continuous_error
#check @Carleman.cartesianCell_average_lipschitz_error
#print axioms Carleman.cartesianCell_average_lipschitz_error

#check @Carleman.cartesianBoxCellIsometry
#print axioms Carleman.cartesianBoxCellIsometry
#check @Carleman.cartesianBoxCellIsometry_adjoint_average
#print axioms Carleman.cartesianBoxCellIsometry_adjoint_average
#check @Carleman.cartesianBoxCellIsometry_average_norm
#print axioms Carleman.cartesianBoxCellIsometry_average_norm
#check @Carleman.cartesianBoxCell_average_error
#print axioms Carleman.cartesianBoxCell_average_error
#check @Carleman.cartesianBox_uncovered_volume_tendsto
#print axioms Carleman.cartesianBox_uncovered_volume_tendsto
#check @Carleman.isometric_reconstruction_residual_bound
#print axioms Carleman.isometric_reconstruction_residual_bound
#check @Carleman.isometric_reconstruction_tendsto_of_denseRange
#print axioms Carleman.isometric_reconstruction_tendsto_of_denseRange
#check @Carleman.cartesianBoxCell_continuous_residual_tendsto
#print axioms Carleman.cartesianBoxCell_continuous_residual_tendsto
#check @Carleman.cartesianBoxCell_average_strong_convergence
#print axioms Carleman.cartesianBoxCell_average_strong_convergence

#check @Carleman.spatialTest_toLp_denseRange
#print axioms Carleman.spatialTest_toLp_denseRange
#check @Carleman.SimplicialPartition.nodal_lipschitz_value_error
#print axioms Carleman.SimplicialPartition.nodal_lipschitz_value_error
#check @Carleman.SimplicialPartition.test_nodal_L2_error
#print axioms Carleman.SimplicialPartition.test_nodal_L2_error
#check @Carleman.SimplicialPartition.test_projection_L2_error
#print axioms Carleman.SimplicialPartition.test_projection_L2_error
#check @Carleman.full_p1_initial_projection_strong_convergence
#print axioms Carleman.full_p1_initial_projection_strong_convergence

#check @Carleman.finiteCellFunction
#print axioms Carleman.finiteCellFunction
#check @Carleman.finiteCellFunction_on_cell
#print axioms Carleman.finiteCellFunction_on_cell
#check @Carleman.finiteCellFunction_zero_outside
#print axioms Carleman.finiteCellFunction_zero_outside
#check @Carleman.finiteCellFunction_bound
#print axioms Carleman.finiteCellFunction_bound
#check @Carleman.finiteCellMultiplier
#print axioms Carleman.finiteCellMultiplier
#check @Carleman.finiteCellMultiplier_commute
#print axioms Carleman.finiteCellMultiplier_commute
#check @Carleman.finiteCellMultiplier_pairing
#print axioms Carleman.finiteCellMultiplier_pairing
#check @Carleman.cartesianReconstructedPotential
#print axioms Carleman.cartesianReconstructedPotential
#check @Carleman.cartesianReconstructedPotential_bound
#print axioms Carleman.cartesianReconstructedPotential_bound
#check @Carleman.cartesianReconstructedPotential_on_cell
#print axioms Carleman.cartesianReconstructedPotential_on_cell
#check @Carleman.cartesianReconstructedPotential_zero_outside
#print axioms Carleman.cartesianReconstructedPotential_zero_outside
#check @Carleman.cartesianReconstructedPotential_commute
#print axioms Carleman.cartesianReconstructedPotential_commute
#check @Carleman.cartesianReconstructedPotential_pairing
#print axioms Carleman.cartesianReconstructedPotential_pairing
#check @Carleman.cartesianSpacetimeCell
#print axioms Carleman.cartesianSpacetimeCell
#check @Carleman.cartesianSpacetimeCell_measurable
#print axioms Carleman.cartesianSpacetimeCell_measurable
#check @Carleman.cartesianSpacetimeCell_disjoint
#print axioms Carleman.cartesianSpacetimeCell_disjoint
#check @Carleman.cartesianSpacetimeCell_restrict_volume
#print axioms Carleman.cartesianSpacetimeCell_restrict_volume
#check @Carleman.cartesianSpacetimePotential
#print axioms Carleman.cartesianSpacetimePotential
#check @Carleman.cartesianSpacetimePotential_bound
#print axioms Carleman.cartesianSpacetimePotential_bound
#check @Carleman.cartesianSpacetimePotential_on_cell
#print axioms Carleman.cartesianSpacetimePotential_on_cell
#check @Carleman.cartesianSpacetimePotential_zero_outside
#print axioms Carleman.cartesianSpacetimePotential_zero_outside
#check @Carleman.cartesianAveragedPotential_product_formula
#print axioms Carleman.cartesianAveragedPotential_product_formula
#check @Carleman.cartesianSpacetimePotential_on_time_cell
#print axioms Carleman.cartesianSpacetimePotential_on_time_cell
#check @Carleman.cartesianSpacetimeCellIsometry
#print axioms Carleman.cartesianSpacetimeCellIsometry
#check @Carleman.cartesianSpacetimeCellIsometry_adjoint_average
#print axioms Carleman.cartesianSpacetimeCellIsometry_adjoint_average

#check @Carleman.finiteCell_continuous_residual_tendsto
#print axioms Carleman.finiteCell_continuous_residual_tendsto
#check @Carleman.finiteCell_average_strong_convergence
#print axioms Carleman.finiteCell_average_strong_convergence
#check @Carleman.fixedSpacetimeCellIsometry
#print axioms Carleman.fixedSpacetimeCellIsometry
#check @Carleman.fixedSpacetime_uncovered_volume
#print axioms Carleman.fixedSpacetime_uncovered_volume
#check @Carleman.fixedSpacetime_uncovered_volume_tendsto
#print axioms Carleman.fixedSpacetime_uncovered_volume_tendsto
#check @Carleman.fixedSpacetimeCell_average_strong_convergence
#print axioms Carleman.fixedSpacetimeCell_average_strong_convergence
#check @Carleman.BoundedMultiplier.toL2
#print axioms Carleman.BoundedMultiplier.toL2
#check @Carleman.BoundedMultiplier.toL2_ae
#print axioms Carleman.BoundedMultiplier.toL2_ae
#check @Carleman.cartesianSpacetimePotential_eq_projection
#print axioms Carleman.cartesianSpacetimePotential_eq_projection
#check @Carleman.fixedSpacetimePotential
#print axioms Carleman.fixedSpacetimePotential
#check @Carleman.fixedSpacetimePotential_bound
#print axioms Carleman.fixedSpacetimePotential_bound
#check @Carleman.fixedSpacetimePotential_eq_projection
#print axioms Carleman.fixedSpacetimePotential_eq_projection
#check @Carleman.cartesianAveragedPotential_strong_convergence
#print axioms Carleman.cartesianAveragedPotential_strong_convergence

#check @Carleman.fixedTimeCellIsometry
#print axioms Carleman.fixedTimeCellIsometry
#check @Carleman.fixedTimeCellIsometry_adjoint_average
#print axioms Carleman.fixedTimeCellIsometry_adjoint_average
#check @Carleman.fixedTimeCell_uncovered_volume
#print axioms Carleman.fixedTimeCell_uncovered_volume
#check @Carleman.fixedTimeCell_average_strong_convergence
#print axioms Carleman.fixedTimeCell_average_strong_convergence
#check @Carleman.timeReconstructedPotential
#print axioms Carleman.timeReconstructedPotential
#check @Carleman.timeReconstructedPotential_bound
#print axioms Carleman.timeReconstructedPotential_bound
#check @Carleman.timeReconstructedPotential_on_cell
#print axioms Carleman.timeReconstructedPotential_on_cell
#check @Carleman.fixedTimePotential
#print axioms Carleman.fixedTimePotential
#check @Carleman.fixedTimePotential_bound
#print axioms Carleman.fixedTimePotential_bound
#check @Carleman.fixedTimePotential_value
#print axioms Carleman.fixedTimePotential_value
#check @Carleman.BoundedMultiplier.sub_sq_integrable
#print axioms Carleman.BoundedMultiplier.sub_sq_integrable
#check @Carleman.BoundedMultiplier.toL2_sub_norm_sq
#print axioms Carleman.BoundedMultiplier.toL2_sub_norm_sq
#check @Carleman.fixedTimePotential_slice_error
#print axioms Carleman.fixedTimePotential_slice_error
#check @Carleman.fixedTimePotential_slice_error_tendsto
#print axioms Carleman.fixedTimePotential_slice_error_tendsto
#check @Carleman.timeAveragedPotential_strong_convergence
#print axioms Carleman.timeAveragedPotential_strong_convergence

#check @Carleman.BoundedMultiplier.map_toL2_comm
#print axioms Carleman.BoundedMultiplier.map_toL2_comm
#check @Carleman.BoundedMultiplier.test_product_error
#print axioms Carleman.BoundedMultiplier.test_product_error
#check @Carleman.BoundedMultiplier.test_product_strong_convergence
#print axioms Carleman.BoundedMultiplier.test_product_strong_convergence
#check @Carleman.hilbert_weak_strong_pairing
#print axioms Carleman.hilbert_weak_strong_pairing
#check @Carleman.potential_weak_pairing_tendsto
#print axioms Carleman.potential_weak_pairing_tendsto
#check @Carleman.timeAveragedPotential_weak_pairing
#print axioms Carleman.timeAveragedPotential_weak_pairing
#check @Carleman.cartesianAveragedPotential_weak_pairing
#print axioms Carleman.cartesianAveragedPotential_weak_pairing

#check @Carleman.antitone_threshold_cut
#print axioms Carleman.antitone_threshold_cut
#check @Carleman.kuhnOrderedCube_nearest_vertex
#print axioms Carleman.kuhnOrderedCube_nearest_vertex
#check @Carleman.cartesianKuhnSimplex_nearest_vertex
#print axioms Carleman.cartesianKuhnSimplex_nearest_vertex
#check @Carleman.coordinate_hyperplane_volume_zero
#print axioms Carleman.coordinate_hyperplane_volume_zero
#check @Carleman.coordinate_ne_ae
#print axioms Carleman.coordinate_ne_ae
#check @Carleman.cartesianKuhnSimplex_nearest_vertex_ae
#print axioms Carleman.cartesianKuhnSimplex_nearest_vertex_ae
#check @Carleman.cartesian_lattice_unique_nearest
#print axioms Carleman.cartesian_lattice_unique_nearest
#check @Carleman.cartesianCellFunction_nearest_value
#print axioms Carleman.cartesianCellFunction_nearest_value
#check @Carleman.cartesianCell_kuhn_pointwise_consistency
#print axioms Carleman.cartesianCell_kuhn_pointwise_consistency
#check @Carleman.cartesianCell_kuhn_L2_consistency
#print axioms Carleman.cartesianCell_kuhn_L2_consistency

#check @Carleman.timeCellReconstruction_sub
#print axioms Carleman.timeCellReconstruction_sub
#check @Carleman.timeCellReconstruction_norm_le
#print axioms Carleman.timeCellReconstruction_norm_le
#check @Carleman.fixedTimeCellReconstruction
#print axioms Carleman.fixedTimeCellReconstruction
#check @Carleman.fixedTimeCellReconstruction_sub
#print axioms Carleman.fixedTimeCellReconstruction_sub
#check @Carleman.fixedTimeCellReconstruction_norm_le
#print axioms Carleman.fixedTimeCellReconstruction_norm_le
#check @Carleman.cartesianBoxKuhnReconstructionJet
#print axioms Carleman.cartesianBoxKuhnReconstructionJet
#check @Carleman.cartesianBoxCell_kuhn_L2_consistency
#print axioms Carleman.cartesianBoxCell_kuhn_L2_consistency
#check @Carleman.hilbert_weak_of_norm_sub_tendsto_zero
#print axioms Carleman.hilbert_weak_of_norm_sub_tendsto_zero
#check @Carleman.cartesianBoxCell_kuhn_time_consistency
#print axioms Carleman.cartesianBoxCell_kuhn_time_consistency
#check @Carleman.cartesianBoxCell_kuhn_time_error_tendsto
#print axioms Carleman.cartesianBoxCell_kuhn_time_error_tendsto
#check @Carleman.cartesianBoxCell_kuhn_same_weak_limit
#print axioms Carleman.cartesianBoxCell_kuhn_same_weak_limit

#check @Carleman.Physical.forward_energy_increment
#print axioms Carleman.Physical.forward_energy_increment
#check @Carleman.Physical.forward_energy_balance
#print axioms Carleman.Physical.forward_energy_balance
#check @Carleman.Physical.forward_stiffness_budget_of_state_bound
#print axioms Carleman.Physical.forward_stiffness_budget_of_state_bound
#check @Carleman.Physical.forward_stiffness_budget
#print axioms Carleman.Physical.forward_stiffness_budget
#check @Carleman.cartesianPhysicalLaplacian_gradient_sq
#print axioms Carleman.cartesianPhysicalLaplacian_gradient_sq
#check @Carleman.cartesian_state_gradient_budget
#print axioms Carleman.cartesian_state_gradient_budget
#check @Carleman.cartesian_state_gradient_uniform
#print axioms Carleman.cartesian_state_gradient_uniform
#check @Carleman.cartesian_state_fixed_gradient_uniform
#print axioms Carleman.cartesian_state_fixed_gradient_uniform
#check @Carleman.cartesian_controlled_states_same_weak_limit
#print axioms Carleman.cartesian_controlled_states_same_weak_limit


-- T188: actual H¹₀-valued state weak subsequences.
#check @Carleman.timeCellReconstruction_map
#print axioms Carleman.timeCellReconstruction_map
#check @Carleman.fixedTimeCellReconstruction_map
#print axioms Carleman.fixedTimeCellReconstruction_map
#check @Carleman.DirichletEnergyState
#print axioms Carleman.DirichletEnergyState
#check @Carleman.dirichletEnergyStateNormedAddCommGroup
#print axioms Carleman.dirichletEnergyStateNormedAddCommGroup
#check @Carleman.dirichletEnergyStateInnerProductSpace
#print axioms Carleman.dirichletEnergyStateInnerProductSpace
#check @Carleman.dirichletEnergyStateEquiv
#print axioms Carleman.dirichletEnergyStateEquiv
#check @Carleman.dirichletStateValue
#print axioms Carleman.dirichletStateValue
#check @Carleman.dirichletStateGradient
#print axioms Carleman.dirichletStateGradient
#check @Carleman.dirichletEnergyState_norm_sq
#print axioms Carleman.dirichletEnergyState_norm_sq
#check @Carleman.dirichletEnergyState_complete
#print axioms Carleman.dirichletEnergyState_complete
#check @Carleman.dirichletEnergyStateSecondCountable
#print axioms Carleman.dirichletEnergyStateSecondCountable
#check @Carleman.dirichlet_time_norm_sq
#print axioms Carleman.dirichlet_time_norm_sq
#check @Carleman.exists_dirichlet_time_weak_subsequence
#print axioms Carleman.exists_dirichlet_time_weak_subsequence
#check @Carleman.cartesianBoxDirichletState
#print axioms Carleman.cartesianBoxDirichletState
#check @Carleman.cartesianBoxDirichletState_value
#print axioms Carleman.cartesianBoxDirichletState_value
#check @Carleman.cartesianBoxDirichletState_gradient
#print axioms Carleman.cartesianBoxDirichletState_gradient
#check @Carleman.cartesianBoxDirichletState_value_norm_le
#print axioms Carleman.cartesianBoxDirichletState_value_norm_le
#check @Carleman.timeCellReconstruction_norm_sq_le
#print axioms Carleman.timeCellReconstruction_norm_sq_le
#check @Carleman.fixedTimeCellReconstruction_norm_sq_le
#print axioms Carleman.fixedTimeCellReconstruction_norm_sq_le
#check @Carleman.cartesian_state_node_uniform
#print axioms Carleman.cartesian_state_node_uniform
#check @Carleman.stateTimeEnergyBound
#print axioms Carleman.stateTimeEnergyBound
#check @Carleman.cartesian_state_dirichlet_time_uniform
#print axioms Carleman.cartesian_state_dirichlet_time_uniform
#check @Carleman.cartesian_controlled_states_weak_subsequence
#print axioms Carleman.cartesian_controlled_states_weak_subsequence

#check @Carleman.Physical.physical_summation_by_parts
#print axioms Carleman.Physical.physical_summation_by_parts
#check @Carleman.Physical.forward_equation_weak_identity
#print axioms Carleman.Physical.forward_equation_weak_identity
#check @Carleman.timeCellReconstruction_difference_inner
#print axioms Carleman.timeCellReconstruction_difference_inner
#check @Carleman.fixedTimeCellReconstruction_inner
#print axioms Carleman.fixedTimeCellReconstruction_inner
#check @Carleman.fixedTimeCellReconstruction_difference_inner
#print axioms Carleman.fixedTimeCellReconstruction_difference_inner
#check @Carleman.cartesianPhysicalLaplacian_gradient_pairing
#print axioms Carleman.cartesianPhysicalLaplacian_gradient_pairing
#check @Carleman.cartesian_forward_reconstructed_weak_identity
#print axioms Carleman.cartesian_forward_reconstructed_weak_identity
#check @Carleman.cartesianBoxCellControl
#print axioms Carleman.cartesianBoxCellControl
#check @Carleman.cartesianBoxReconstructedPotential
#print axioms Carleman.cartesianBoxReconstructedPotential
#check @Carleman.cartesianBoxReconstructedPotential_commute
#print axioms Carleman.cartesianBoxReconstructedPotential_commute
#check @Carleman.cartesian_fixed_forward_reconstructed_weak_identity
#print axioms Carleman.cartesian_fixed_forward_reconstructed_weak_identity
#check @Carleman.timeCellReconstruction_multiplier_inner
#print axioms Carleman.timeCellReconstruction_multiplier_inner
#check @Carleman.fixedTimeCellReconstruction_multiplier_inner
#print axioms Carleman.fixedTimeCellReconstruction_multiplier_inner

#check @Carleman.simpleL2_uncurry_memLp
#print axioms Carleman.simpleL2_uncurry_memLp
#check @Carleman.simpleL2_product
#print axioms Carleman.simpleL2_product
#check @Carleman.simpleL2_uncurry_add_ae
#print axioms Carleman.simpleL2_uncurry_add_ae
#check @Carleman.simpleL2_uncurry_smul_ae
#print axioms Carleman.simpleL2_uncurry_smul_ae
#check @Carleman.simpleL2_productLinear
#print axioms Carleman.simpleL2_productLinear
#check @Carleman.simpleL2_bochnerLinear
#print axioms Carleman.simpleL2_bochnerLinear
#check @Carleman.memLp_toLp_norm_sq
#print axioms Carleman.memLp_toLp_norm_sq
#check @Carleman.simpleL2_product_norm
#print axioms Carleman.simpleL2_product_norm
#check @Carleman.simpleL2_bochnerLinear_dense
#print axioms Carleman.simpleL2_bochnerLinear_dense
#check @Carleman.bochnerL2ProductIsometry
#print axioms Carleman.bochnerL2ProductIsometry
#check @Carleman.bochnerL2ProductIsometry_simple
#print axioms Carleman.bochnerL2ProductIsometry_simple
#check @Carleman.bochnerL2ProductIsometry_simple_ae
#print axioms Carleman.bochnerL2ProductIsometry_simple_ae
#check @Carleman.bochnerL2ProductIsometry_indicator_ae
#print axioms Carleman.bochnerL2ProductIsometry_indicator_ae
#check @Carleman.bochnerL2ProductIsometry_weak
#print axioms Carleman.bochnerL2ProductIsometry_weak
#check @Carleman.bochnerL2ProductIsometry_time_ae
#print axioms Carleman.bochnerL2ProductIsometry_time_ae
#check @Carleman.bochnerL2ProductIsometry_fixed_time_ae
#print axioms Carleman.bochnerL2ProductIsometry_fixed_time_ae
#check @Carleman.cartesian_time_product_reconstruction
#print axioms Carleman.cartesian_time_product_reconstruction
#check @Carleman.cartesian_time_product_potential
#print axioms Carleman.cartesian_time_product_potential
#check @Carleman.cartesian_fixed_time_product_reconstruction
#print axioms Carleman.cartesian_fixed_time_product_reconstruction
#check @Carleman.cartesian_time_product_potential_pairing
#print axioms Carleman.cartesian_time_product_potential_pairing

#check @Carleman.fixedTimeCellIsometry_eq_reconstruction
#print axioms Carleman.fixedTimeCellIsometry_eq_reconstruction
#check @Carleman.timeCell_derivative_average
#print axioms Carleman.timeCell_derivative_average
#check @Carleman.timeCell_test_difference_eq_projection
#print axioms Carleman.timeCell_test_difference_eq_projection
#check @Carleman.fixedTimeCell_test_difference_eq_projection
#print axioms Carleman.fixedTimeCell_test_difference_eq_projection
#check @Carleman.time_test_difference_strong_convergence
#print axioms Carleman.time_test_difference_strong_convergence
#check @Carleman.time_test_left_sample_error
#print axioms Carleman.time_test_left_sample_error
#check @Carleman.time_test_left_sample_strong_convergence
#print axioms Carleman.time_test_left_sample_strong_convergence
#check @Carleman.continuous_time_memLp
#print axioms Carleman.continuous_time_memLp
#check @Carleman.time_test_lipschitz
#print axioms Carleman.time_test_lipschitz
#check @Carleman.smooth_time_test_consistency
#print axioms Carleman.smooth_time_test_consistency
#check @Carleman.timeTensor
#print axioms Carleman.timeTensor
#check @Carleman.timeTensor_ae
#print axioms Carleman.timeTensor_ae
#check @Carleman.timeTensor_reconstruction
#print axioms Carleman.timeTensor_reconstruction
#check @Carleman.timeTensor_strong_convergence
#print axioms Carleman.timeTensor_strong_convergence
#check @Carleman.tensor_time_test_consistency
#print axioms Carleman.tensor_time_test_consistency
#check @Carleman.fixedTimeCellReconstruction_sum
#print axioms Carleman.fixedTimeCellReconstruction_sum
#check @Carleman.finite_tensor_time_test_consistency
#print axioms Carleman.finite_tensor_time_test_consistency
#check @Carleman.finite_tensor_test_endpoint_consistency
#print axioms Carleman.finite_tensor_test_endpoint_consistency

#check @Carleman.SimplicialPartition.nodal_lipschitz_derivative_error
#print axioms Carleman.SimplicialPartition.nodal_lipschitz_derivative_error
#check @Carleman.SimplicialPartition.test_nodal_derivative_L2_error
#print axioms Carleman.SimplicialPartition.test_nodal_derivative_L2_error
#check @Carleman.SimplicialPartition.test_nodal_zero_boundary
#print axioms Carleman.SimplicialPartition.test_nodal_zero_boundary
#check @Carleman.SimplicialPartition.testDirichletState
#print axioms Carleman.SimplicialPartition.testDirichletState
#check @Carleman.SimplicialPartition.testDirichletState_value
#print axioms Carleman.SimplicialPartition.testDirichletState_value
#check @Carleman.SimplicialPartition.testDirichletState_gradient
#print axioms Carleman.SimplicialPartition.testDirichletState_gradient
#check @Carleman.SpatialTest.dirichletState
#print axioms Carleman.SpatialTest.dirichletState
#check @Carleman.SpatialTest.dirichletState_value
#print axioms Carleman.SpatialTest.dirichletState_value
#check @Carleman.SpatialTest.dirichletState_gradient
#print axioms Carleman.SpatialTest.dirichletState_gradient
#check @Carleman.test_nodal_value_strong_convergence
#print axioms Carleman.test_nodal_value_strong_convergence
#check @Carleman.test_nodal_derivative_strong_convergence
#print axioms Carleman.test_nodal_derivative_strong_convergence
#check @Carleman.dirichletEnergyState_tendsto_of_fields
#print axioms Carleman.dirichletEnergyState_tendsto_of_fields
#check @Carleman.full_p1_test_H1_strong_convergence
#print axioms Carleman.full_p1_test_H1_strong_convergence
#check @Carleman.SimplicialPartition.testDirichletState_finite_value
#print axioms Carleman.SimplicialPartition.testDirichletState_finite_value
#check @Carleman.full_p1_finite_time_test_consistency
#print axioms Carleman.full_p1_finite_time_test_consistency
#check @Carleman.full_p1_finite_test_endpoint_consistency
#print axioms Carleman.full_p1_finite_test_endpoint_consistency

#check @Carleman.cartesianNodalSample
#print axioms Carleman.cartesianNodalSample
#check @Carleman.cartesianNodalSample_apply
#print axioms Carleman.cartesianNodalSample_apply
#check @Carleman.cartesianInteriorData_test_vertex
#print axioms Carleman.cartesianInteriorData_test_vertex
#check @Carleman.cartesianKuhnReconstructionLp_test_eq_nodal
#print axioms Carleman.cartesianKuhnReconstructionLp_test_eq_nodal
#check @Carleman.cartesianBoxKuhnPartition
#print axioms Carleman.cartesianBoxKuhnPartition
#check @Carleman.cartesianBoxKuhnPartition_faceMatching
#print axioms Carleman.cartesianBoxKuhnPartition_faceMatching
#check @Carleman.cartesianBoxKuhnPartition_boundaryFitted
#print axioms Carleman.cartesianBoxKuhnPartition_boundaryFitted
#check @Carleman.cartesianBoxDirichletState_test_eq_nodal
#print axioms Carleman.cartesianBoxDirichletState_test_eq_nodal
#check @Carleman.cartesianBoxKuhnPartition_maxDiameter_le
#print axioms Carleman.cartesianBoxKuhnPartition_maxDiameter_le
#check @Carleman.cartesianBoxKuhn_uniform_inballs
#print axioms Carleman.cartesianBoxKuhn_uniform_inballs
#check @Carleman.cartesian_test_H1_strong_convergence
#print axioms Carleman.cartesian_test_H1_strong_convergence
#check @Carleman.cartesian_test_cell_L2_strong_convergence
#print axioms Carleman.cartesian_test_cell_L2_strong_convergence
#check @Carleman.cartesianBoxDirichletLinearMap
#print axioms Carleman.cartesianBoxDirichletLinearMap
#check @Carleman.cartesianBoxDirichletLinearMap_apply
#print axioms Carleman.cartesianBoxDirichletLinearMap_apply
#check @Carleman.cartesianNodalSample_finite
#print axioms Carleman.cartesianNodalSample_finite
#check @Carleman.cartesian_finite_time_test_H1_consistency
#print axioms Carleman.cartesian_finite_time_test_H1_consistency
#check @Carleman.cartesian_finite_time_test_cell_L2_consistency
#print axioms Carleman.cartesian_finite_time_test_cell_L2_consistency
#check @Carleman.cartesian_finite_test_endpoint_consistency
#print axioms Carleman.cartesian_finite_test_endpoint_consistency

#check @Carleman.cartesian_test_cell_uniform_error
#print axioms Carleman.cartesian_test_cell_uniform_error
#check @Carleman.cartesian_box_test_cell_uniform_error
#print axioms Carleman.cartesian_box_test_cell_uniform_error
#check @Carleman.p1_test_uniform_error
#print axioms Carleman.p1_test_uniform_error
#check @Carleman.timeCell_ae_covered
#print axioms Carleman.timeCell_ae_covered
#check @Carleman.finite_time_tensor_uniform_error
#print axioms Carleman.finite_time_tensor_uniform_error
#check @Carleman.finite_tensor_test_bounds
#print axioms Carleman.finite_tensor_test_bounds
#check @Carleman.bochner_finite_time_tensor_ae
#print axioms Carleman.bochner_finite_time_tensor_ae
#check @Carleman.finite_tensor_test_aestronglyMeasurable
#print axioms Carleman.finite_tensor_test_aestronglyMeasurable
#check @Carleman.bochner_finite_time_tensor_uniform_error
#print axioms Carleman.bochner_finite_time_tensor_uniform_error
#check @Carleman.cartesian_finite_time_test_uniform_bound
#print axioms Carleman.cartesian_finite_time_test_uniform_bound
#check @Carleman.SimplicialPartition.nodalLp_finite
#print axioms Carleman.SimplicialPartition.nodalLp_finite
#check @Carleman.p1_finite_time_test_uniform_bound
#print axioms Carleman.p1_finite_time_test_uniform_bound
#check @Carleman.cartesian_finite_time_test_Linfty_consistency
#print axioms Carleman.cartesian_finite_time_test_Linfty_consistency
#check @Carleman.p1_finite_time_test_Linfty_consistency
#print axioms Carleman.p1_finite_time_test_Linfty_consistency

#check @Carleman.finite_tensor_test_bounded
#print axioms Carleman.finite_tensor_test_bounded
#check @Carleman.finiteTensorTestMultiplier
#print axioms Carleman.finiteTensorTestMultiplier
#check @Carleman.finiteTensorTestMultiplier_value
#print axioms Carleman.finiteTensorTestMultiplier_value
#check @Carleman.L2_tendsto_of_Linfty_error
#print axioms Carleman.L2_tendsto_of_Linfty_error
#check @Carleman.cartesianFiniteTestProduct
#print axioms Carleman.cartesianFiniteTestProduct
#check @Carleman.p1FiniteTestProduct
#print axioms Carleman.p1FiniteTestProduct
#check @Carleman.cartesian_finite_test_product_strong_convergence
#print axioms Carleman.cartesian_finite_test_product_strong_convergence
#check @Carleman.p1_finite_test_product_strong_convergence
#print axioms Carleman.p1_finite_test_product_strong_convergence
#check @Carleman.cartesian_finite_test_potential_strong_convergence
#print axioms Carleman.cartesian_finite_test_potential_strong_convergence
#check @Carleman.p1_finite_test_potential_strong_convergence
#print axioms Carleman.p1_finite_test_potential_strong_convergence

#check @Carleman.timeTensor_map
#print axioms Carleman.timeTensor_map
#check @Carleman.cartesianFiniteTestSequence
#print axioms Carleman.cartesianFiniteTestSequence
#check @Carleman.cartesianFiniteTestSequence_front
#print axioms Carleman.cartesianFiniteTestSequence_front
#check @Carleman.cartesianFiniteTestSequence_endpoints
#print axioms Carleman.cartesianFiniteTestSequence_endpoints
#check @Carleman.cartesianGridPotential
#print axioms Carleman.cartesianGridPotential
#check @Carleman.cartesian_fixed_time_product_potential
#print axioms Carleman.cartesian_fixed_time_product_potential
#check @Carleman.cartesian_finite_test_gradient_strong_convergence
#print axioms Carleman.cartesian_finite_test_gradient_strong_convergence
#check @Carleman.cartesian_finite_test_weak_limit_identity
#print axioms Carleman.cartesian_finite_test_weak_limit_identity

-- T197: original independent refinement and actual control endpoints.
#check @Carleman.Physical.physicalMeshScale_tendsto_atTop
#print axioms Carleman.Physical.physicalMeshScale_tendsto_atTop
#check @Carleman.Physical.physicalMeshScale_dt_bound
#print axioms Carleman.Physical.physicalMeshScale_dt_bound
#check @Carleman.Physical.physicalMeshScale_dt_tendsto_zero
#print axioms Carleman.Physical.physicalMeshScale_dt_tendsto_zero
#check @Carleman.Physical.physical_conditions_eventually
#print axioms Carleman.Physical.physical_conditions_eventually
#check @Carleman.Physical.physical_terminal_norm_tendsto_zero
#print axioms Carleman.Physical.physical_terminal_norm_tendsto_zero
#check @Carleman.cartesianGridPotential_bound
#print axioms Carleman.cartesianGridPotential_bound
#check @Carleman.cartesianBoxTimeControl_norm
#print axioms Carleman.cartesianBoxTimeControl_norm
#check @Carleman.cartesianBoxTimeControl_supported
#print axioms Carleman.cartesianBoxTimeControl_supported
#check @Carleman.Physical.box_cartesian_controls_independent_refinement
#print axioms Carleman.Physical.box_cartesian_controls_independent_refinement


-- T198: every original weak control accumulation point.
#check @Carleman.hilbert_weak_limit_norm_le
#print axioms Carleman.hilbert_weak_limit_norm_le
#check @Carleman.regional_control_of_weak_limit
#print axioms Carleman.regional_control_of_weak_limit
#check @Carleman.FiniteDirichletControlIdentity
#print axioms Carleman.FiniteDirichletControlIdentity
#check @Carleman.cartesian_weak_control_limit_finite_identity
#print axioms Carleman.cartesian_weak_control_limit_finite_identity
#check @Carleman.Physical.box_cartesian_controls_weak_accumulation
#print axioms Carleman.Physical.box_cartesian_controls_weak_accumulation


-- T199: the original weak equation on all Dirichlet energy tests.
#check @Carleman.exists_refining_time_grids
#print axioms Carleman.exists_refining_time_grids
#check @Carleman.finiteTensorTestMultiplier_eq_product
#print axioms Carleman.finiteTensorTestMultiplier_eq_product
#check @Carleman.exists_dirichlet_test_sequence
#print axioms Carleman.exists_dirichlet_test_sequence
#check @Carleman.FiniteDirichletControlIdentity.spatial_test
#print axioms Carleman.FiniteDirichletControlIdentity.spatial_test
#check @Carleman.FiniteDirichletControlIdentity.all_energy_tests
#print axioms Carleman.FiniteDirichletControlIdentity.all_energy_tests


-- T200: the actual strong-dual weak time derivative.
#check @Carleman.timeTensor_eq_scalarTensor
#print axioms Carleman.timeTensor_eq_scalarTensor
#check @Carleman.inner_timeTensor_integral
#print axioms Carleman.inner_timeTensor_integral
#check @Carleman.compLpL_adjoint
#print axioms Carleman.compLpL_adjoint
#check @Carleman.HasWeakTimeDerivative.map_integral
#print axioms Carleman.HasWeakTimeDerivative.map_integral
#check @Carleman.dirichletTimeMass
#print axioms Carleman.dirichletTimeMass
#check @Carleman.dirichletTimeLoad
#print axioms Carleman.dirichletTimeLoad
#check @Carleman.dirichletTimeMass_pairing
#print axioms Carleman.dirichletTimeMass_pairing
#check @Carleman.dirichletTimeLoad_pairing
#print axioms Carleman.dirichletTimeLoad_pairing
#check @Carleman.FiniteDirichletControlIdentity.mass_test_identity
#print axioms Carleman.FiniteDirichletControlIdentity.mass_test_identity
#check @Carleman.FiniteDirichletControlIdentity.mass_weak_time_derivative
#print axioms Carleman.FiniteDirichletControlIdentity.mass_weak_time_derivative
#check @Carleman.dirichletPivotDual
#print axioms Carleman.dirichletPivotDual
#check @Carleman.dirichletPivotDual_apply
#print axioms Carleman.dirichletPivotDual_apply
#check @Carleman.dirichletDualTimeLoad
#print axioms Carleman.dirichletDualTimeLoad
#check @Carleman.dirichletDualTimeLoad_pairing
#print axioms Carleman.dirichletDualTimeLoad_pairing
#check @Carleman.FiniteDirichletControlIdentity.dual_weak_time_derivative
#print axioms Carleman.FiniteDirichletControlIdentity.dual_weak_time_derivative


-- T201: actual mass regularization and energy/Bochner strong limits.
#check @Carleman.positiveMassForm
#print axioms Carleman.positiveMassForm
#check @Carleman.positiveMassForm_coercive
#print axioms Carleman.positiveMassForm_coercive
#check @Carleman.positiveMassInverse
#print axioms Carleman.positiveMassInverse
#check @Carleman.positiveMassInverse_equation
#print axioms Carleman.positiveMassInverse_equation
#check @Carleman.positiveMassInverse_left
#print axioms Carleman.positiveMassInverse_left
#check @Carleman.positiveMassInverse_commute
#print axioms Carleman.positiveMassInverse_commute
#check @Carleman.positiveMassRegularizer
#print axioms Carleman.positiveMassRegularizer
#check @Carleman.positiveMassRegularizer_norm
#print axioms Carleman.positiveMassRegularizer_norm
#check @Carleman.positiveMassRegularizer_residual_norm
#print axioms Carleman.positiveMassRegularizer_residual_norm
#check @Carleman.positiveMassRegularizer_range_error
#print axioms Carleman.positiveMassRegularizer_range_error
#check @Carleman.positiveMassRegularizer_strong
#print axioms Carleman.positiveMassRegularizer_strong
#check @Carleman.adjoint_mass_denseRange
#print axioms Carleman.adjoint_mass_denseRange
#check @Carleman.compLpL_strong_of_contractions
#print axioms Carleman.compLpL_strong_of_contractions
#check @Carleman.dirichletTimeMass_nonneg
#print axioms Carleman.dirichletTimeMass_nonneg
#check @Carleman.dirichletTimeMass_dense
#print axioms Carleman.dirichletTimeMass_dense
#check @Carleman.dirichletMassRegularizer
#print axioms Carleman.dirichletMassRegularizer
#check @Carleman.dirichletMassRegularizer_norm
#print axioms Carleman.dirichletMassRegularizer_norm
#check @Carleman.dirichletMassRegularizer_strong
#print axioms Carleman.dirichletMassRegularizer_strong
#check @Carleman.dirichletMassRegularizer_bochner_strong
#print axioms Carleman.dirichletMassRegularizer_bochner_strong


-- T202: actual pivot energy variation and weighted closed-interval trace.
#check @Carleman.ac_time_norm_sub_bound
#print axioms Carleman.ac_time_norm_sub_bound
#check @Carleman.integral_norm_mul_le_l2
#print axioms Carleman.integral_norm_mul_le_l2
#check @Carleman.HasWeakTimeDerivative.pivot_energy_variation
#print axioms Carleman.HasWeakTimeDerivative.pivot_energy_variation
#check @Carleman.HasWeakTimeDerivative.pivot_trace_bound
#print axioms Carleman.HasWeakTimeDerivative.pivot_trace_bound


-- T203: actual continuous mass regularization paths and strong graph convergence.
#check @Carleman.HasWeakTimeDerivative.linear_map
#print axioms Carleman.HasWeakTimeDerivative.linear_map
#check @Carleman.mass_regularized_time_paths
#print axioms Carleman.mass_regularized_time_paths
#check @Carleman.FiniteDirichletControlIdentity.regularized_time_paths
#print axioms Carleman.FiniteDirichletControlIdentity.regularized_time_paths


-- T204: actual uniform path convergence and the original H-continuous representative.
#check @Carleman.HasWeakTimeDerivative.sub_memLp
#print axioms Carleman.HasWeakTimeDerivative.sub_memLp
#check @Carleman.pivot_path_limit
#print axioms Carleman.pivot_path_limit
#check @Carleman.exists_pivot_time_representative
#print axioms Carleman.exists_pivot_time_representative
#check @Carleman.FiniteDirichletControlIdentity.continuous_H_representative
#print axioms Carleman.FiniteDirichletControlIdentity.continuous_H_representative


-- T205: actual original initial and terminal traces from unrestricted tests.
#check @Carleman.HasWeakTimeDerivative.scalar_affine_green
#print axioms Carleman.HasWeakTimeDerivative.scalar_affine_green
#check @Carleman.HasWeakTimeDerivative.scalar_endpoints
#print axioms Carleman.HasWeakTimeDerivative.scalar_endpoints
#check @Carleman.FiniteDirichletControlIdentity.continuous_pairing_weak
#print axioms Carleman.FiniteDirichletControlIdentity.continuous_pairing_weak
#check @Carleman.FiniteDirichletControlIdentity.continuous_pairing_test
#print axioms Carleman.FiniteDirichletControlIdentity.continuous_pairing_test
#check @Carleman.FiniteDirichletControlIdentity.continuous_H_endpoints
#print axioms Carleman.FiniteDirichletControlIdentity.continuous_H_endpoints
#check @Carleman.FiniteDirichletControlIdentity.continuous_H_trace
#print axioms Carleman.FiniteDirichletControlIdentity.continuous_H_trace


-- T206: every actual Cartesian weak control limit gives the original null-control state.
#check @Carleman.DirichletNullControlState
#print axioms Carleman.DirichletNullControlState
#check @Carleman.FiniteDirichletControlIdentity.null_control_state
#print axioms Carleman.FiniteDirichletControlIdentity.null_control_state
#check @Carleman.Physical.box_cartesian_controls_null_limits
#print axioms Carleman.Physical.box_cartesian_controls_null_limits


-- T207: actual conforming states in the full original time-energy space.
#check @Carleman.dirichletGalerkinState
#print axioms Carleman.dirichletGalerkinState
#check @Carleman.dirichletGalerkinState_value
#print axioms Carleman.dirichletGalerkinState_value
#check @Carleman.dirichletGalerkinState_stiffness
#print axioms Carleman.dirichletGalerkinState_stiffness
#check @Carleman.dirichletGalerkinState_norm_sq
#print axioms Carleman.dirichletGalerkinState_norm_sq
#check @Carleman.conforming_state_node_uniform
#print axioms Carleman.conforming_state_node_uniform
#check @Carleman.conforming_state_dirichlet_time_uniform
#print axioms Carleman.conforming_state_dirichlet_time_uniform


-- T208: actual conforming weak compactness, six-term identity and full P1 tests.
#check @Carleman.conforming_controlled_states_weak_subsequence
#print axioms Carleman.conforming_controlled_states_weak_subsequence
#check @Carleman.conforming_forward_reconstructed_weak_identity
#print axioms Carleman.conforming_forward_reconstructed_weak_identity
#check @Carleman.conforming_fixed_forward_reconstructed_weak_identity
#print axioms Carleman.conforming_fixed_forward_reconstructed_weak_identity
#check @Carleman.SimplicialPartition.testGalerkinState
#print axioms Carleman.SimplicialPartition.testGalerkinState
#check @Carleman.SimplicialPartition.testGalerkinState_value
#print axioms Carleman.SimplicialPartition.testGalerkinState_value
#check @Carleman.SimplicialPartition.testGalerkinState_lift
#print axioms Carleman.SimplicialPartition.testGalerkinState_lift
#check @Carleman.SimplicialPartition.testGalerkinState_finite_lift
#print axioms Carleman.SimplicialPartition.testGalerkinState_finite_lift


-- T209: original averaged potential and actual full P1 finite-test consistency.
#check @Carleman.time_average_product_potential
#print axioms Carleman.time_average_product_potential
#check @Carleman.fixedTimeCellPotential
#print axioms Carleman.fixedTimeCellPotential
#check @Carleman.fixedTimeCellPotential_bound
#print axioms Carleman.fixedTimeCellPotential_bound
#check @Carleman.fixed_time_average_product_potential
#print axioms Carleman.fixed_time_average_product_potential
#check @Carleman.fixedTimeCellPotential_value
#print axioms Carleman.fixedTimeCellPotential_value
#check @Carleman.time_average_reconstructed_weak_pairing
#print axioms Carleman.time_average_reconstructed_weak_pairing
#check @Carleman.p1FiniteTestSequence
#print axioms Carleman.p1FiniteTestSequence
#check @Carleman.p1FiniteTestSequence_lift
#print axioms Carleman.p1FiniteTestSequence_lift
#check @Carleman.p1FiniteTestSequence_value
#print axioms Carleman.p1FiniteTestSequence_value
#check @Carleman.full_p1_galerkin_finite_test_endpoint_consistency
#print axioms Carleman.full_p1_galerkin_finite_test_endpoint_consistency
#check @Carleman.full_p1_galerkin_finite_time_test_consistency
#print axioms Carleman.full_p1_galerkin_finite_time_test_consistency


-- T210: each original P1 weak control limit has the full equation and continuous null state.
#check @Carleman.regional_time_control_norm
#print axioms Carleman.regional_time_control_norm
#check @Carleman.regional_time_control_supported
#print axioms Carleman.regional_time_control_supported
#check @Carleman.full_p1_finite_test_weak_limit_identity
#print axioms Carleman.full_p1_finite_test_weak_limit_identity
#check @Carleman.full_p1_weak_control_limit_null_state
#print axioms Carleman.full_p1_weak_control_limit_null_state

-- T211: actual independently refining P1 control families and every weak null limit.
#check @Carleman.Physical.box_p1_controls_independent_refinement
#print axioms Carleman.Physical.box_p1_controls_independent_refinement
#check @Carleman.Physical.box_p1_controls_null_limits
#print axioms Carleman.Physical.box_p1_controls_null_limits

-- T212: exact energy at every time for the original weak pivot derivative.
#check @Carleman.HasWeakTimeDerivative.pivot_energy_identity_to
#print axioms Carleman.HasWeakTimeDerivative.pivot_energy_identity_to
#check @Carleman.time_restrict_inner_integral
#print axioms Carleman.time_restrict_inner_integral
#check @Carleman.pivot_path_limit_strong
#print axioms Carleman.pivot_path_limit_strong
#check @Carleman.exists_pivot_time_energy_representative
#print axioms Carleman.exists_pivot_time_energy_representative
#check @Carleman.pivot_time_energy_identity
#print axioms Carleman.pivot_time_energy_identity
#check @Carleman.FiniteDirichletControlIdentity.energy_identity
#print axioms Carleman.FiniteDirichletControlIdentity.energy_identity
#check @Carleman.FiniteDirichletControlIdentity.continuous_H_energy_trace
#print axioms Carleman.FiniteDirichletControlIdentity.continuous_H_energy_trace

-- T213: original local control energy and actual bounded product-potential pairing.
#check @Carleman.BoundedMultiplier.compLpL_map
#print axioms Carleman.BoundedMultiplier.compLpL_map
#check @Carleman.cutoff_map_idempotent
#print axioms Carleman.cutoff_map_idempotent
#check @Carleman.cutoff_inner_integral
#print axioms Carleman.cutoff_inner_integral
#check @Carleman.bochnerL2ProductIsometry_cutoff
#print axioms Carleman.bochnerL2ProductIsometry_cutoff
#check @Carleman.cutoff_inner_cutoff
#print axioms Carleman.cutoff_inner_cutoff
#check @Carleman.cutoff_multiplier_pairing
#print axioms Carleman.cutoff_multiplier_pairing
#check @Carleman.dirichletTimeLoad_cutoff_pairing
#print axioms Carleman.dirichletTimeLoad_cutoff_pairing
#check @Carleman.dirichletTimeLoad_cutoff_upper_bound
#print axioms Carleman.dirichletTimeLoad_cutoff_upper_bound
#check @Carleman.FiniteDirichletControlIdentity.local_energy_inequality
#print axioms Carleman.FiniteDirichletControlIdentity.local_energy_inequality

-- T214: actual energy solutions with the same original data are unique.
#check @Carleman.continuous_volterra_nonneg_eq_zero
#print axioms Carleman.continuous_volterra_nonneg_eq_zero
#check @Carleman.time_cutoff_norm_sq_of_ae
#print axioms Carleman.time_cutoff_norm_sq_of_ae
#check @Carleman.dirichlet_mass_energy_zero
#print axioms Carleman.dirichlet_mass_energy_zero
#check @Carleman.dirichletTimeLoad_sub
#print axioms Carleman.dirichletTimeLoad_sub
#check @Carleman.dirichlet_mass_energy_unique
#print axioms Carleman.dirichlet_mass_energy_unique
#check @Carleman.FiniteDirichletControlIdentity.identifies_energy_solution
#print axioms Carleman.FiniteDirichletControlIdentity.identifies_energy_solution

-- T215: the original strong-dual equation and its unique continuous energy solution.
#check @Carleman.HasWeakTimeDerivative.of_injective_map_integral
#print axioms Carleman.HasWeakTimeDerivative.of_injective_map_integral
#check @Carleman.dirichlet_dual_mass_weak_iff
#print axioms Carleman.dirichlet_dual_mass_weak_iff
#check @Carleman.dirichlet_dual_energy_memLp
#print axioms Carleman.dirichlet_dual_energy_memLp
#check @Carleman.DirichletEnergySolution
#print axioms Carleman.DirichletEnergySolution
#check @Carleman.DirichletNullControlState.energy_solution
#print axioms Carleman.DirichletNullControlState.energy_solution
#check @Carleman.DirichletEnergySolution.mass_weak_time_derivative
#print axioms Carleman.DirichletEnergySolution.mass_weak_time_derivative
#check @Carleman.DirichletEnergySolution.unique
#print axioms Carleman.DirichletEnergySolution.unique
#check @Carleman.FiniteDirichletControlIdentity.unique_energy_solution
#print axioms Carleman.FiniteDirichletControlIdentity.unique_energy_solution

-- T216: actual arbitrary-order compact tests and the original H0m closure.
#check @Carleman.SpatialTest.eq_of_value_eq
#print axioms Carleman.SpatialTest.eq_of_value_eq
#check @Carleman.SpatialTest.wordTest
#print axioms Carleman.SpatialTest.wordTest
#check @Carleman.SpatialTest.wordTest_perm
#print axioms Carleman.SpatialTest.wordTest_perm
#check @Carleman.SpatialTest.multiTest
#print axioms Carleman.SpatialTest.multiTest
#check @Carleman.SpatialTest.multiTest_nil
#print axioms Carleman.SpatialTest.multiTest_nil
#check @Carleman.SpatialTest.multiTest_cons
#print axioms Carleman.SpatialTest.multiTest_cons
#check @Carleman.SpatialTest.allOrderJet
#print axioms Carleman.SpatialTest.allOrderJet
#check @Carleman.SpatialTest.allOrderJet_value
#print axioms Carleman.SpatialTest.allOrderJet_value
#check @Carleman.SpatialTest.allOrderJet_component
#print axioms Carleman.SpatialTest.allOrderJet_component
#check @Carleman.SpatialTest.allOrderJet_truncate
#print axioms Carleman.SpatialTest.allOrderJet_truncate
#check @Carleman.SpatialTest.allOrderJet_one
#print axioms Carleman.SpatialTest.allOrderJet_one
#check @Carleman.SpatialTest.zeroTest_allOrderJet
#print axioms Carleman.SpatialTest.zeroTest_allOrderJet
#check @Carleman.SpatialTest.addTest_allOrderJet
#print axioms Carleman.SpatialTest.addTest_allOrderJet
#check @Carleman.SpatialTest.smulTest_allOrderJet
#print axioms Carleman.SpatialTest.smulTest_allOrderJet
#check @Carleman.higherDirichletJetSpace
#print axioms Carleman.higherDirichletJetSpace
#check @Carleman.higherDirichletSubspace
#print axioms Carleman.higherDirichletSubspace
#check @Carleman.higherDirichletSubspace_sobolev
#print axioms Carleman.higherDirichletSubspace_sobolev
#check @Carleman.test_mem_higherDirichletJetSpace
#print axioms Carleman.test_mem_higherDirichletJetSpace
#check @Carleman.test_mem_higherDirichletSubspace
#print axioms Carleman.test_mem_higherDirichletSubspace
#check @Carleman.higherDirichletJetSpace_eq_closure
#print axioms Carleman.higherDirichletJetSpace_eq_closure
#check @Carleman.mem_higherDirichletJetSpace_iff
#print axioms Carleman.mem_higherDirichletJetSpace_iff
#check @Carleman.higherDirichletSubspace_closed
#print axioms Carleman.higherDirichletSubspace_closed
#check @Carleman.higherDirichletSubspace_dense
#print axioms Carleman.higherDirichletSubspace_dense
#check @Carleman.higherDirichletSubspace_one
#print axioms Carleman.higherDirichletSubspace_one
#check @Carleman.higherDirichletEnergy_complete
#print axioms Carleman.higherDirichletEnergy_complete

-- T217: constructed smooth multiplication on actual Hm and H0m.
#check @Carleman.WeakSobolevJet.leibnizField_perm
#print axioms Carleman.WeakSobolevJet.leibnizField_perm
#check @Carleman.WeakSobolevJet.smoothProductJet
#print axioms Carleman.WeakSobolevJet.smoothProductJet
#check @Carleman.WeakSobolevJet.smoothProductJet_value
#print axioms Carleman.WeakSobolevJet.smoothProductJet_value
#check @Carleman.WeakSobolevJet.continuous_wordField
#print axioms Carleman.WeakSobolevJet.continuous_wordField
#check @Carleman.WeakSobolevJet.continuous_leibnizField
#print axioms Carleman.WeakSobolevJet.continuous_leibnizField
#check @Carleman.WeakSobolevJet.smoothProductCLM
#print axioms Carleman.WeakSobolevJet.smoothProductCLM
#check @Carleman.smoothProductCLM_test
#print axioms Carleman.smoothProductCLM_test
#check @Carleman.smoothProductCLM_mem_higherDirichlet
#print axioms Carleman.smoothProductCLM_mem_higherDirichlet
#check @Carleman.boundedSmooth_map_mem_sobolev
#print axioms Carleman.boundedSmooth_map_mem_sobolev
#check @Carleman.boundedSmooth_map_mem_higherDirichlet
#print axioms Carleman.boundedSmooth_map_mem_higherDirichlet
#check @Carleman.boundedSmooth_map_mem_higherDirichlet_domain
#print axioms Carleman.boundedSmooth_map_mem_higherDirichlet_domain

-- T218: actual arbitrary-order coefficient form and uniform weighted upper bound.
#check @Carleman.MultiDerivativeIndex
#print axioms Carleman.MultiDerivativeIndex
#check @Carleman.jetScalarComponent
#print axioms Carleman.jetScalarComponent
#check @Carleman.coefficientJetForm
#print axioms Carleman.coefficientJetForm
#check @Carleman.coefficientJetForm_apply
#print axioms Carleman.coefficientJetForm_apply
#check @Carleman.coefficientJetForm_integral
#print axioms Carleman.coefficientJetForm_integral
#check @Carleman.coefficientJetForm_symmetric
#print axioms Carleman.coefficientJetForm_symmetric
#check @Carleman.jetScalarComponent_weighted_le
#print axioms Carleman.jetScalarComponent_weighted_le
#check @Carleman.coefficientJetForm_weighted_upper
#print axioms Carleman.coefficientJetForm_weighted_upper
#check @Carleman.HigherDirichletEnergy
#print axioms Carleman.HigherDirichletEnergy
#check @Carleman.higherDirichletToJet
#print axioms Carleman.higherDirichletToJet
#check @Carleman.higherDirichletEnergy_norm_sq
#print axioms Carleman.higherDirichletEnergy_norm_sq
#check @Carleman.higherCoefficientForm
#print axioms Carleman.higherCoefficientForm
#check @Carleman.higherCoefficientForm_apply
#print axioms Carleman.higherCoefficientForm_apply
#check @Carleman.higherCoefficientForm_symmetric
#print axioms Carleman.higherCoefficientForm_symmetric
#check @Carleman.higherCoefficientForm_integral
#print axioms Carleman.higherCoefficientForm_integral
#check @Carleman.higherCoefficientForm_weighted_upper
#print axioms Carleman.higherCoefficientForm_weighted_upper
#check @Carleman.higherCoefficientOriginalForm
#print axioms Carleman.higherCoefficientOriginalForm

-- T219: arbitrary small high-order energy coefficient for actual lower-order terms.
#check @Carleman.WeakSobolevJet.lowerParameterNorm
#print axioms Carleman.WeakSobolevJet.lowerParameterNorm
#check @Carleman.WeakSobolevJet.lowerParameterNorm_nonneg
#print axioms Carleman.WeakSobolevJet.lowerParameterNorm_nonneg
#check @Carleman.WeakSobolevJet.lowerParameterNorm_rescale
#print axioms Carleman.WeakSobolevJet.lowerParameterNorm_rescale
#check @Carleman.WeakSobolevJet.boundedLipschitz_lowerParameter_small
#print axioms Carleman.WeakSobolevJet.boundedLipschitz_lowerParameter_small
#check @Carleman.WeakSobolevJet.boundedLipschitz_lowerParameter_product_small
#print axioms Carleman.WeakSobolevJet.boundedLipschitz_lowerParameter_product_small
#check @Carleman.WeakSobolevJet.lowerOrderQuadratic_le
#print axioms Carleman.WeakSobolevJet.lowerOrderQuadratic_le
#check @Carleman.WeakSobolevJet.boundedLipschitz_lowerOrderQuadratic_small
#print axioms Carleman.WeakSobolevJet.boundedLipschitz_lowerOrderQuadratic_small
#check @Carleman.SobolevHilbert.toJet_norm_le
#print axioms Carleman.SobolevHilbert.toJet_norm_le
#check @Carleman.boundedLipschitz_hilbert_lowerOrderQuadratic_small
#print axioms Carleman.boundedLipschitz_hilbert_lowerOrderQuadratic_small

-- T220: actual strictly lower-order Leibniz remainder and coefficient-form error.
#check @Carleman.derivativeSplits_empty_left
#print axioms Carleman.derivativeSplits_empty_left
#check @Carleman.derivativeRemainderSplits
#print axioms Carleman.derivativeRemainderSplits
#check @Carleman.derivativeRemainderSplits_lt
#print axioms Carleman.derivativeRemainderSplits_lt
#check @Carleman.WeakSobolevJet.leibnizRemainder
#print axioms Carleman.WeakSobolevJet.leibnizRemainder
#check @Carleman.WeakSobolevJet.leibnizField_eq_principal_add
#print axioms Carleman.WeakSobolevJet.leibnizField_eq_principal_add
#check @Carleman.WeakSobolevJet.lowerParameterNorm_component
#print axioms Carleman.WeakSobolevJet.lowerParameterNorm_component
#check @Carleman.WeakSobolevJet.lowerParameterNorm_le_parameterNorm
#print axioms Carleman.WeakSobolevJet.lowerParameterNorm_le_parameterNorm
#check @Carleman.WeakSobolevJet.leibnizRemainder_term_bound
#print axioms Carleman.WeakSobolevJet.leibnizRemainder_term_bound
#check @Carleman.WeakSobolevJet.leibnizRemainder_weighted_bound
#print axioms Carleman.WeakSobolevJet.leibnizRemainder_weighted_bound
#check @Carleman.WeakSobolevJet.conjugated_word_remainder_bound
#print axioms Carleman.WeakSobolevJet.conjugated_word_remainder_bound
#check @Carleman.jetScalarComponent_parameter_le
#print axioms Carleman.jetScalarComponent_parameter_le
#check @Carleman.coefficientJetForm_inverse_pairing
#print axioms Carleman.coefficientJetForm_inverse_pairing
#check @Carleman.coefficientJetForm_error_of_components
#print axioms Carleman.coefficientJetForm_error_of_components
#check @Carleman.intrinsic_conjugated_component_remainder_bound
#print axioms Carleman.intrinsic_conjugated_component_remainder_bound
#check @Carleman.coefficientJetForm_smooth_conjugation_error
#print axioms Carleman.coefficientJetForm_smooth_conjugation_error

-- T221: original allowed-weight lower bound on the full H₀ᵐ space.
#check @Carleman.higherDirichlet_smoothProduct_exists
#print axioms Carleman.higherDirichlet_smoothProduct_exists
#check @Carleman.allowedWeight_inverse_relative_uniform
#print axioms Carleman.allowedWeight_inverse_relative_uniform
#check @Carleman.higherCoefficientForm_allowedWeight_lower
#print axioms Carleman.higherCoefficientForm_allowedWeight_lower
#check @Carleman.higherCoefficientForm_closure_weighted_coercivity
#print axioms Carleman.higherCoefficientForm_closure_weighted_coercivity

-- T222: actual distributional bounded weak coefficient product.
#check @Carleman.SpatialTest.valueMultiplier
#print axioms Carleman.SpatialTest.valueMultiplier
#check @Carleman.SpatialTest.mollifiedProduct
#print axioms Carleman.SpatialTest.mollifiedProduct
#check @Carleman.SpatialTest.mollifiedProduct_toLp
#print axioms Carleman.SpatialTest.mollifiedProduct_toLp
#check @Carleman.SpatialTest.mollifiedProduct_derivativeLp_eventually
#print axioms Carleman.SpatialTest.mollifiedProduct_derivativeLp_eventually
#check @Carleman.SpatialTest.mollifiedProduct_toLp_tendsto
#print axioms Carleman.SpatialTest.mollifiedProduct_toLp_tendsto
#check @Carleman.SpatialTest.mollifiedProduct_derivativeLp_tendsto
#print axioms Carleman.SpatialTest.mollifiedProduct_derivativeLp_tendsto
#check @Carleman.SpatialTest.inner_valueMultiplier
#print axioms Carleman.SpatialTest.inner_valueMultiplier
#check @Carleman.IsWeakSpatialDerivative.mul_bounded_of_weakLp
#print axioms Carleman.IsWeakSpatialDerivative.mul_bounded_of_weakLp
#check @Carleman.BoundedMultiplier.toLp
#print axioms Carleman.BoundedMultiplier.toLp
#check @Carleman.BoundedMultiplier.toLp_ae
#print axioms Carleman.BoundedMultiplier.toLp_ae
#check @Carleman.IsWeakMultiplierDerivative
#print axioms Carleman.IsWeakMultiplierDerivative
#check @Carleman.isWeakMultiplierDerivative_iff
#print axioms Carleman.isWeakMultiplierDerivative_iff
#check @Carleman.IsWeakSpatialDerivative.mul_weakCoefficient
#print axioms Carleman.IsWeakSpatialDerivative.mul_weakCoefficient

-- T223: finite-order bounded weak coefficient Leibniz and actual product jets.
#check @Carleman.BoundedWeakCoefficient
#print axioms Carleman.BoundedWeakCoefficient
#check @Carleman.BoundedWeakCoefficient.truncate
#print axioms Carleman.BoundedWeakCoefficient.truncate
#check @Carleman.WeakSobolevJet.weakCoefficient_leibnizField_weak
#print axioms Carleman.WeakSobolevJet.weakCoefficient_leibnizField_weak
#check @Carleman.WeakSobolevJet.weakCoefficient_wordField_mul
#print axioms Carleman.WeakSobolevJet.weakCoefficient_wordField_mul
#check @Carleman.WeakSobolevJet.weakCoefficient_leibnizField_perm
#print axioms Carleman.WeakSobolevJet.weakCoefficient_leibnizField_perm
#check @Carleman.WeakSobolevJet.weakCoefficientProductJet
#print axioms Carleman.WeakSobolevJet.weakCoefficientProductJet
#check @Carleman.WeakSobolevJet.weakCoefficientProductJet_value
#print axioms Carleman.WeakSobolevJet.weakCoefficientProductJet_value
#check @Carleman.WeakSobolevJet.weakCoefficientProductCLM
#print axioms Carleman.WeakSobolevJet.weakCoefficientProductCLM
#check @Carleman.WeakSobolevJet.weakCoefficientProductJet_word
#print axioms Carleman.WeakSobolevJet.weakCoefficientProductJet_word

-- T224: true general coefficient differential expression and associated operator graph.
#check @Carleman.SpatialTest.wordTest_append
#print axioms Carleman.SpatialTest.wordTest_append
#check @Carleman.SpatialTest.wordTest_derivativeTest
#print axioms Carleman.SpatialTest.wordTest_derivativeTest
#check @Carleman.weakWordChain_test
#print axioms Carleman.weakWordChain_test
#check @Carleman.WeakSobolevJet.coefficientDifferentialTerm
#print axioms Carleman.WeakSobolevJet.coefficientDifferentialTerm
#check @Carleman.WeakSobolevJet.coefficientDifferentialTerm_nil
#print axioms Carleman.WeakSobolevJet.coefficientDifferentialTerm_nil
#check @Carleman.WeakSobolevJet.coefficientDifferentialTerm_weak
#print axioms Carleman.WeakSobolevJet.coefficientDifferentialTerm_weak
#check @Carleman.WeakSobolevJet.coefficientDifferentialTerm_test
#print axioms Carleman.WeakSobolevJet.coefficientDifferentialTerm_test
#check @Carleman.WeakSobolevJet.wordField_multiIndex_truncate
#print axioms Carleman.WeakSobolevJet.wordField_multiIndex_truncate
#check @Carleman.coefficientDifferentialOperator
#print axioms Carleman.coefficientDifferentialOperator
#check @Carleman.coefficientDifferentialOperator_test
#print axioms Carleman.coefficientDifferentialOperator_test
#check @Carleman.coefficientDifferentialOperator_form
#print axioms Carleman.coefficientDifferentialOperator_form
#check @Carleman.higherCoefficient_operator_graph_of_sobolev
#print axioms Carleman.higherCoefficient_operator_graph_of_sobolev
#check @Carleman.higherCoefficient_operator_eq_differential
#print axioms Carleman.higherCoefficient_operator_eq_differential
#check @Carleman.higherCoefficient_operator_domain_eq
#print axioms Carleman.higherCoefficient_operator_domain_eq
#check @Carleman.higherCoefficient_operator_canonical
#print axioms Carleman.higherCoefficient_operator_canonical

-- T225: actual original general coefficient operator uniform commutator.
#check @Carleman.list_sum_map_sub
#print axioms Carleman.list_sum_map_sub
#check @Carleman.WeakSobolevJet.coefficientTermBound
#print axioms Carleman.WeakSobolevJet.coefficientTermBound
#check @Carleman.WeakSobolevJet.coefficientTermBound_nonneg
#print axioms Carleman.WeakSobolevJet.coefficientTermBound_nonneg
#check @Carleman.WeakSobolevJet.coefficientDifferentialTerm_error_of_words
#print axioms Carleman.WeakSobolevJet.coefficientDifferentialTerm_error_of_words
#check @Carleman.coefficientOperatorBound
#print axioms Carleman.coefficientOperatorBound
#check @Carleman.coefficientOperatorBound_nonneg
#print axioms Carleman.coefficientOperatorBound_nonneg
#check @Carleman.coefficientDifferentialOperator_error_of_words
#print axioms Carleman.coefficientDifferentialOperator_error_of_words
#check @Carleman.coefficientDifferentialOperator_smooth_commutator
#print axioms Carleman.coefficientDifferentialOperator_smooth_commutator
#check @Carleman.coefficientDifferentialOperator_allowed_commutator
#print axioms Carleman.coefficientDifferentialOperator_allowed_commutator
#check @Carleman.higherCoefficient_operator_multiplier_preserves
#print axioms Carleman.higherCoefficient_operator_multiplier_preserves
#check @Carleman.higherCoefficient_allowed_commutator
#print axioms Carleman.higherCoefficient_allowed_commutator

#check @Carleman.CoerciveForm.operator_adjoint_graph_iff
#print axioms Carleman.CoerciveForm.operator_adjoint_graph_iff
#check @Carleman.higherCoefficient_valueEquiv_jet
#print axioms Carleman.higherCoefficient_valueEquiv_jet
#check @Carleman.higherCoefficient_scalarForm_canonical
#print axioms Carleman.higherCoefficient_scalarForm_canonical
#check @Carleman.higherCoefficient_allowed_form_lower_uniform
#print axioms Carleman.higherCoefficient_allowed_form_lower_uniform
#check @Carleman.higherCoefficient_allowed_data_uniform
#print axioms Carleman.higherCoefficient_allowed_data_uniform
#check @Carleman.higherCoefficient_allowed_family_uniform
#print axioms Carleman.higherCoefficient_allowed_family_uniform
#check @Carleman.higherCoefficient_analytic_realization
#print axioms Carleman.higherCoefficient_analytic_realization

#check @Carleman.sqrtScalarIter
#print axioms Carleman.sqrtScalarIter
#check @Carleman.sqrtScalarIter_bounds
#print axioms Carleman.sqrtScalarIter_bounds
#check @Carleman.sqrtScalarIter_monotone
#print axioms Carleman.sqrtScalarIter_monotone
#check @Carleman.sqrtScalarIter_tendsto
#print axioms Carleman.sqrtScalarIter_tendsto
#check @Carleman.sqrtComplementIter
#print axioms Carleman.sqrtComplementIter
#check @Carleman.sqrtComplementIter_norm
#print axioms Carleman.sqrtComplementIter_norm
#check @Carleman.sqrtComplementIter_dist
#print axioms Carleman.sqrtComplementIter_dist
#check @Carleman.sqrtComplementIter_cauchy
#print axioms Carleman.sqrtComplementIter_cauchy
#check @Carleman.sqrtComplementIter_exists_limit
#print axioms Carleman.sqrtComplementIter_exists_limit
#check @Carleman.sqrtComplementIter_limit_square
#print axioms Carleman.sqrtComplementIter_limit_square
#check @Carleman.sqrtComplementIter_selfAdjoint
#print axioms Carleman.sqrtComplementIter_selfAdjoint
#check @Carleman.positive_contraction_complement_norm
#print axioms Carleman.positive_contraction_complement_norm
#check @Carleman.positive_contraction_exists_sqrt
#print axioms Carleman.positive_contraction_exists_sqrt
#check @Carleman.positive_exists_sqrt
#print axioms Carleman.positive_exists_sqrt

#check @Carleman.CoerciveForm.inverseH
#print axioms Carleman.CoerciveForm.inverseH
#check @Carleman.CoerciveForm.inverseH_eq
#print axioms Carleman.CoerciveForm.inverseH_eq
#check @Carleman.CoerciveForm.inverseH_form
#print axioms Carleman.CoerciveForm.inverseH_form
#check @Carleman.CoerciveForm.inverseH_pair
#print axioms Carleman.CoerciveForm.inverseH_pair
#check @Carleman.CoerciveForm.inverseH_positive
#print axioms Carleman.CoerciveForm.inverseH_positive
#check @Carleman.CoerciveForm.inverseH_injective
#print axioms Carleman.CoerciveForm.inverseH_injective
#check @Carleman.CoerciveForm.inverseH_range
#print axioms Carleman.CoerciveForm.inverseH_range
#check @Carleman.CoerciveForm.inverseH_dense
#print axioms Carleman.CoerciveForm.inverseH_dense
#check @Carleman.CoerciveForm.inverseEnergy_dense
#print axioms Carleman.CoerciveForm.inverseEnergy_dense
#check @Carleman.CoerciveForm.inverseSqrt_injective
#print axioms Carleman.CoerciveForm.inverseSqrt_injective
#check @Carleman.CoerciveForm.inverseSqrt_dense
#print axioms Carleman.CoerciveForm.inverseSqrt_dense
#check @Carleman.CoerciveForm.inverseSqrt_energy_pair
#print axioms Carleman.CoerciveForm.inverseSqrt_energy_pair
#check @Carleman.CoerciveForm.inverseSqrt_energy_bound
#print axioms Carleman.CoerciveForm.inverseSqrt_energy_bound
#check @Carleman.CoerciveForm.inverseSqrtLift
#print axioms Carleman.CoerciveForm.inverseSqrtLift
#check @Carleman.CoerciveForm.inverseSqrtLift_apply
#print axioms Carleman.CoerciveForm.inverseSqrtLift_apply
#check @Carleman.CoerciveForm.inverseSqrtLift_pair
#print axioms Carleman.CoerciveForm.inverseSqrtLift_pair
#check @Carleman.CoerciveForm.inverseSqrtLift_embed
#print axioms Carleman.CoerciveForm.inverseSqrtLift_embed
#check @Carleman.CoerciveForm.inverseSqrtLift_lower_bound
#print axioms Carleman.CoerciveForm.inverseSqrtLift_lower_bound
#check @Carleman.CoerciveForm.inverseSqrtLift_surjective
#print axioms Carleman.CoerciveForm.inverseSqrtLift_surjective
#check @Carleman.CoerciveForm.inverseSqrt_range
#print axioms Carleman.CoerciveForm.inverseSqrt_range
#check @Carleman.CoerciveForm.formSqrtDomain
#print axioms Carleman.CoerciveForm.formSqrtDomain
#check @Carleman.CoerciveForm.formSqrt
#print axioms Carleman.CoerciveForm.formSqrt
#check @Carleman.CoerciveForm.formSqrt_inverse
#print axioms Carleman.CoerciveForm.formSqrt_inverse
#check @Carleman.CoerciveForm.formSqrt_graph
#print axioms Carleman.CoerciveForm.formSqrt_graph
#check @Carleman.CoerciveForm.formSqrt_energy
#print axioms Carleman.CoerciveForm.formSqrt_energy
#check @Carleman.CoerciveForm.formSqrt_nonneg
#print axioms Carleman.CoerciveForm.formSqrt_nonneg
#check @Carleman.CoerciveForm.formSqrt_adjoint_graph
#print axioms Carleman.CoerciveForm.formSqrt_adjoint_graph
#check @Carleman.CoerciveForm.inverseH_operator_graph
#print axioms Carleman.CoerciveForm.inverseH_operator_graph
#check @Carleman.CoerciveForm.formSqrt_square_graph
#print axioms Carleman.CoerciveForm.formSqrt_square_graph
#check @Carleman.CoerciveForm.exists_positive_form_square_root
#print axioms Carleman.CoerciveForm.exists_positive_form_square_root

#check @Carleman.OriginalForm.formSqrtDomain_eq
#print axioms Carleman.OriginalForm.formSqrtDomain_eq
#check @Carleman.OriginalForm.SquareRootData
#print axioms Carleman.OriginalForm.SquareRootData
#check @Carleman.OriginalForm.exists_squareRootData
#print axioms Carleman.OriginalForm.exists_squareRootData
#check @Carleman.higherCoefficient_spatial_operators
#print axioms Carleman.higherCoefficient_spatial_operators


#check @Carleman.halfspaceExpSum
#print axioms Carleman.halfspaceExpSum
#check @Carleman.halfspaceSmoothInner
#print axioms Carleman.halfspaceSmoothInner
#check @Carleman.halfspaceExpSum_contDiff
#print axioms Carleman.halfspaceExpSum_contDiff
#check @Carleman.halfspaceExpSum_convex
#print axioms Carleman.halfspaceExpSum_convex
#check @Carleman.halfspaceSmoothInner_open
#print axioms Carleman.halfspaceSmoothInner_open
#check @Carleman.halfspaceSmoothInner_convex
#print axioms Carleman.halfspaceSmoothInner_convex
#check @Carleman.halfspaceExpSum_le_half_mem
#print axioms Carleman.halfspaceExpSum_le_half_mem
#check @Carleman.halfspaceSmoothInner_closure_subset
#print axioms Carleman.halfspaceSmoothInner_closure_subset
#check @Carleman.halfspaceSmoothInner_mono
#print axioms Carleman.halfspaceSmoothInner_mono
#check @Carleman.halfspaceExpSum_tendsto_zero
#print axioms Carleman.halfspaceExpSum_tendsto_zero
#check @Carleman.halfspaceSmoothInner_eventually_mem
#print axioms Carleman.halfspaceSmoothInner_eventually_mem
#check @Carleman.halfspaceSmoothInner_exhaustion
#print axioms Carleman.halfspaceSmoothInner_exhaustion
#check @Carleman.halfspaceSmoothInner_compact
#print axioms Carleman.halfspaceSmoothInner_compact
#check @Carleman.halfspaceExpSum_hasFDerivAt
#print axioms Carleman.halfspaceExpSum_hasFDerivAt
#check @Carleman.halfspaceExpSum_support
#print axioms Carleman.halfspaceExpSum_support
#check @Carleman.halfspaceSmoothInner_boundary_regular
#print axioms Carleman.halfspaceSmoothInner_boundary_regular
#check @Carleman.exists_halfspace_smooth_exhaustion
#print axioms Carleman.exists_halfspace_smooth_exhaustion


#check @Carleman.exists_analytic_level_chart
#print axioms Carleman.exists_analytic_level_chart
#check @Carleman.analytic_chart_derivative_inverse
#print axioms Carleman.analytic_chart_derivative_inverse
#check @Carleman.level_chart_image_sublevel
#print axioms Carleman.level_chart_image_sublevel
#check @Carleman.level_chart_frontier_iff
#print axioms Carleman.level_chart_frontier_iff
#check @Carleman.halfspaceExpSum_analytic
#print axioms Carleman.halfspaceExpSum_analytic
#check @Carleman.halfspaceSmoothInner_analytic_chart
#print axioms Carleman.halfspaceSmoothInner_analytic_chart


#check @Carleman.spatialTranslationLp
#print axioms Carleman.spatialTranslationLp
#check @Carleman.spatialTranslationLp_ae
#print axioms Carleman.spatialTranslationLp_ae
#check @Carleman.spatialTranslationLp_norm
#print axioms Carleman.spatialTranslationLp_norm
#check @Carleman.spatialTranslationLp_zero
#print axioms Carleman.spatialTranslationLp_zero
#check @Carleman.spatialTranslationLp_add
#print axioms Carleman.spatialTranslationLp_add
#check @Carleman.spatialTranslationLp_inner
#print axioms Carleman.spatialTranslationLp_inner
#check @Carleman.mollified_full_translation_bound
#print axioms Carleman.mollified_full_translation_bound
#check @Carleman.IsWeakSpatialDerivative.translation_bound_nonneg
#print axioms Carleman.IsWeakSpatialDerivative.translation_bound_nonneg
#check @Carleman.IsWeakSpatialDerivative.translation_bound
#print axioms Carleman.IsWeakSpatialDerivative.translation_bound
#check @Carleman.spatialDifferenceQuotient
#print axioms Carleman.spatialDifferenceQuotient
#check @Carleman.spatialDifferenceQuotient_apply
#print axioms Carleman.spatialDifferenceQuotient_apply
#check @Carleman.IsWeakSpatialDerivative.differenceQuotient_bound
#print axioms Carleman.IsWeakSpatialDerivative.differenceQuotient_bound
#check @Carleman.spatialDifferenceQuotient_inner
#print axioms Carleman.spatialDifferenceQuotient_inner
#check @Carleman.IsWeakSpatialDerivative.translation
#print axioms Carleman.IsWeakSpatialDerivative.translation
#check @Carleman.IsWeakSpatialDerivative.differenceQuotient
#print axioms Carleman.IsWeakSpatialDerivative.differenceQuotient

-- T233: actual test difference quotients and local weak derivative criterion
#check @Carleman.spatialDifferenceQuotient_ae
#print axioms Carleman.spatialDifferenceQuotient_ae
#check @Carleman.spatialDifferenceQuotient_tendsto_of_contDiff
#print axioms Carleman.spatialDifferenceQuotient_tendsto_of_contDiff
#check @Carleman.SpatialTest.differenceQuotient_tendsto
#print axioms Carleman.SpatialTest.differenceQuotient_tendsto
#check @Carleman.SpatialTest.full_toLp_inner
#print axioms Carleman.SpatialTest.full_toLp_inner
#check @Carleman.SpatialTest.full_derivativeLp_inner
#print axioms Carleman.SpatialTest.full_derivativeLp_inner
#check @Carleman.differenceQuotient_test_bound
#print axioms Carleman.differenceQuotient_test_bound
#check @Carleman.exists_weakSpatialDerivative_of_differenceQuotient_bound
#print axioms Carleman.exists_weakSpatialDerivative_of_differenceQuotient_bound
#check @Carleman.exists_weakH2_of_differenceQuotient_bounds
#print axioms Carleman.exists_weakH2_of_differenceQuotient_bounds


#check @Carleman.WeakSobolevJet.translateFirst
#print axioms Carleman.WeakSobolevJet.translateFirst
#check @Carleman.WeakSobolevJet.translateFirst_value
#print axioms Carleman.WeakSobolevJet.translateFirst_value
#check @Carleman.WeakSobolevJet.translateFirst_gradient
#print axioms Carleman.WeakSobolevJet.translateFirst_gradient
#check @Carleman.WeakSobolevJet.translateFirst_tendsto
#print axioms Carleman.WeakSobolevJet.translateFirst_tendsto
#check @Carleman.WeakSobolevJet.differenceFirst
#print axioms Carleman.WeakSobolevJet.differenceFirst
#check @Carleman.WeakSobolevJet.differenceFirst_value
#print axioms Carleman.WeakSobolevJet.differenceFirst_value
#check @Carleman.WeakSobolevJet.differenceFirst_gradient
#print axioms Carleman.WeakSobolevJet.differenceFirst_gradient
#check @Carleman.WeakSobolevJet.differenceFirst_gradient_pairing
#print axioms Carleman.WeakSobolevJet.differenceFirst_gradient_pairing
#check @Carleman.WeakSobolevJet.differenceFirst_energy
#print axioms Carleman.WeakSobolevJet.differenceFirst_energy
#check @Carleman.SpatialTest.translateInto
#print axioms Carleman.SpatialTest.translateInto
#check @Carleman.SpatialTest.translateFirst_test
#print axioms Carleman.SpatialTest.translateFirst_test
#check @Carleman.WeakSobolevJet.translateFirst_dirichlet_mem
#print axioms Carleman.WeakSobolevJet.translateFirst_dirichlet_mem
#check @Carleman.WeakSobolevJet.differenceFirst_dirichlet_mem
#print axioms Carleman.WeakSobolevJet.differenceFirst_dirichlet_mem
#check @Carleman.WeakSobolevJet.zeroExtend_restrict_of_ae_zero
#print axioms Carleman.WeakSobolevJet.zeroExtend_restrict_of_ae_zero
#check @Carleman.WeakSobolevJet.differenceFirst_dirichlet_extension
#print axioms Carleman.WeakSobolevJet.differenceFirst_dirichlet_extension
#check @Carleman.dirichlet_tangential_difference_gradient_bound
#print axioms Carleman.dirichlet_tangential_difference_gradient_bound
#check @Carleman.weakGradient_test_mixed_commute
#print axioms Carleman.weakGradient_test_mixed_commute
#check @Carleman.dirichlet_tangential_test_bound
#print axioms Carleman.dirichlet_tangential_test_bound
#check @Carleman.exists_dirichlet_H2_of_tangential_invariance
#print axioms Carleman.exists_dirichlet_H2_of_tangential_invariance
#check @Carleman.exists_halfspace_dirichlet_H2
#print axioms Carleman.exists_halfspace_dirichlet_H2


#check @Carleman.BoundedMultiplier.spatialTranslate
#print axioms Carleman.BoundedMultiplier.spatialTranslate
#check @Carleman.BoundedMultiplier.spatialTranslate_map
#print axioms Carleman.BoundedMultiplier.spatialTranslate_map
#check @Carleman.BoundedMultiplier.lipschitz_difference_bound
#print axioms Carleman.BoundedMultiplier.lipschitz_difference_bound
#check @Carleman.BoundedMultiplier.spatialDifference
#print axioms Carleman.BoundedMultiplier.spatialDifference
#check @Carleman.BoundedMultiplier.differenceQuotient_product
#print axioms Carleman.BoundedMultiplier.differenceQuotient_product
#check @Carleman.BoundedMultiplier.differenceQuotient_commutator_bound
#print axioms Carleman.BoundedMultiplier.differenceQuotient_commutator_bound
#check @Carleman.matrixL2Pairing
#print axioms Carleman.matrixL2Pairing
#check @Carleman.matrixL2Pairing_bound
#print axioms Carleman.matrixL2Pairing_bound
#check @Carleman.matrixL2Pairing_coercive
#print axioms Carleman.matrixL2Pairing_coercive
#check @Carleman.matrixGradientPairing
#print axioms Carleman.matrixGradientPairing
#check @Carleman.matrixGradientPairing_coercive
#print axioms Carleman.matrixGradientPairing_coercive
#check @Carleman.matrixGradientPairing_bound
#print axioms Carleman.matrixGradientPairing_bound
#check @Carleman.matrixGradientPairing_difference
#print axioms Carleman.matrixGradientPairing_difference
#check @Carleman.matrixGradientPairing_tendsto_right
#print axioms Carleman.matrixGradientPairing_tendsto_right
#check @Carleman.matrixGradient_equation_dirichlet
#print axioms Carleman.matrixGradient_equation_dirichlet
#check @Carleman.dirichlet_variable_tangential_difference_gradient_bound
#print axioms Carleman.dirichlet_variable_tangential_difference_gradient_bound
#check @Carleman.matrixGradientPairing_dirichlet_integral
#print axioms Carleman.matrixGradientPairing_dirichlet_integral
#check @Carleman.matrixGradientPairing_test_integral
#print axioms Carleman.matrixGradientPairing_test_integral
#check @Carleman.dirichlet_variable_tangential_test_bound
#print axioms Carleman.dirichlet_variable_tangential_test_bound

#check @Carleman.BoundedMultiplier.reciprocal
#print axioms Carleman.BoundedMultiplier.reciprocal
#check @Carleman.BoundedMultiplier.reciprocalDerivative
#print axioms Carleman.BoundedMultiplier.reciprocalDerivative
#check @Carleman.BoundedMultiplier.spatialDerivativeOn
#print axioms Carleman.BoundedMultiplier.spatialDerivativeOn
#check @Carleman.matrix_elliptic_diagonal
#print axioms Carleman.matrix_elliptic_diagonal
#check @Carleman.weak_derivative_divide_coefficient
#print axioms Carleman.weak_derivative_divide_coefficient
#check @Carleman.exists_normal_derivative_of_matrix_equation
#print axioms Carleman.exists_normal_derivative_of_matrix_equation
#check @Carleman.exists_variable_H2_of_tangential_test_bounds
#print axioms Carleman.exists_variable_H2_of_tangential_test_bounds
#check @Carleman.matrixGradientPairing_test_restricted
#print axioms Carleman.matrixGradientPairing_test_restricted
#check @Carleman.exists_variable_dirichlet_H2_of_tangential_invariance
#print axioms Carleman.exists_variable_dirichlet_H2_of_tangential_invariance
#check @Carleman.exists_variable_halfspace_dirichlet_H2
#print axioms Carleman.exists_variable_halfspace_dirichlet_H2

#check @Carleman.spatialGraphShear
#print axioms Carleman.spatialGraphShear
#check @Carleman.spatialGraphShear_psi
#print axioms Carleman.spatialGraphShear_psi
#check @Carleman.spatialGraphShear_halfspace
#print axioms Carleman.spatialGraphShear_halfspace
#check @Carleman.spatialGraphShear_hasFDerivAt
#print axioms Carleman.spatialGraphShear_hasFDerivAt
#check @Carleman.spatialGraphShear_normal_derivative
#print axioms Carleman.spatialGraphShear_normal_derivative
#check @Carleman.spatialGraphShear_det
#print axioms Carleman.spatialGraphShear_det
#check @Carleman.spatialGraphShear_measurePreserving
#print axioms Carleman.spatialGraphShear_measurePreserving
#check @Carleman.spatialGraphShear_measurePreserving_restrict
#print axioms Carleman.spatialGraphShear_measurePreserving_restrict
#check @Carleman.spatialGraphShear_halfspace_measurePreserving
#print axioms Carleman.spatialGraphShear_halfspace_measurePreserving
#check @Carleman.spatialGraphShear_contDiff
#print axioms Carleman.spatialGraphShear_contDiff
#check @Carleman.spatialGraphShear_symm_contDiff
#print axioms Carleman.spatialGraphShear_symm_contDiff
#check @Carleman.spatialGraphShear_fderiv_invariant
#print axioms Carleman.spatialGraphShear_fderiv_invariant
#check @Carleman.SpatialTest.pullbackSmoothHomeomorph
#print axioms Carleman.SpatialTest.pullbackSmoothHomeomorph
#check @Carleman.SpatialTest.pullbackSmoothHomeomorph_derivative
#print axioms Carleman.SpatialTest.pullbackSmoothHomeomorph_derivative
#check @Carleman.SpatialTest.pullbackGraphShear_derivative
#print axioms Carleman.SpatialTest.pullbackGraphShear_derivative
#check @Carleman.SpatialTest.pullbackGraphShear_symm_derivative
#print axioms Carleman.SpatialTest.pullbackGraphShear_symm_derivative
#check @Carleman.graphSlopeMultiplier
#print axioms Carleman.graphSlopeMultiplier
#check @Carleman.graphSlopeMultiplier_contDiff
#print axioms Carleman.graphSlopeMultiplier_contDiff
#check @Carleman.graphSlopeMultiplier_normal_derivative
#print axioms Carleman.graphSlopeMultiplier_normal_derivative
#check @Carleman.homeomorphPullbackLp
#print axioms Carleman.homeomorphPullbackLp
#check @Carleman.homeomorphPullbackLp_ae
#print axioms Carleman.homeomorphPullbackLp_ae
#check @Carleman.homeomorphPullbackLp_inverse
#print axioms Carleman.homeomorphPullbackLp_inverse
#check @Carleman.integral_mul_homeomorphPullbackLp
#print axioms Carleman.integral_mul_homeomorphPullbackLp
#check @Carleman.SpatialTest.pullbackSmoothHomeomorph_toLp
#print axioms Carleman.SpatialTest.pullbackSmoothHomeomorph_toLp

#check @Carleman.IsWeakSpatialDerivative.graphShear_normal_pullback
#print axioms Carleman.IsWeakSpatialDerivative.graphShear_normal_pullback
#check @Carleman.IsWeakSpatialDerivative.mul_of_derivative_zero
#print axioms Carleman.IsWeakSpatialDerivative.mul_of_derivative_zero
#check @Carleman.IsWeakSpatialDerivative.graphShear_pullback
#print axioms Carleman.IsWeakSpatialDerivative.graphShear_pullback
#check @Carleman.WeakSobolevJet.graphShearPullback
#print axioms Carleman.WeakSobolevJet.graphShearPullback
#check @Carleman.WeakSobolevJet.graphShearPullback_value
#print axioms Carleman.WeakSobolevJet.graphShearPullback_value
#check @Carleman.WeakSobolevJet.graphShearPullback_gradient
#print axioms Carleman.WeakSobolevJet.graphShearPullback_gradient
#check @Carleman.WeakSobolevJet.graphShearPullback_tendsto
#print axioms Carleman.WeakSobolevJet.graphShearPullback_tendsto
#check @Carleman.WeakSobolevJet.graphShearPullback_test
#print axioms Carleman.WeakSobolevJet.graphShearPullback_test
#check @Carleman.WeakSobolevJet.graphShearPullback_dirichlet
#print axioms Carleman.WeakSobolevJet.graphShearPullback_dirichlet
#check @Carleman.WeakSobolevJet.graphShearPullback_value_norm
#print axioms Carleman.WeakSobolevJet.graphShearPullback_value_norm
#check @Carleman.WeakSobolevJet.graphShearPullback_gradient_bound
#print axioms Carleman.WeakSobolevJet.graphShearPullback_gradient_bound

#check @Carleman.exists_graphShearPullback_H2
#print axioms Carleman.exists_graphShearPullback_H2
#check @Carleman.exists_graphShearPullback_H2_ae
#print axioms Carleman.exists_graphShearPullback_H2_ae
#check @Carleman.spatialGraphShear_neg_eq_symm
#print axioms Carleman.spatialGraphShear_neg_eq_symm
#check @Carleman.graphSlopeMultiplier_neg
#print axioms Carleman.graphSlopeMultiplier_neg
#check @Carleman.exists_H2_of_graphShearPullback_H2
#print axioms Carleman.exists_H2_of_graphShearPullback_H2
#check @Carleman.graphShearPullback_H2_iff
#print axioms Carleman.graphShearPullback_H2_iff

#check @Carleman.graphCovectorMap
#print axioms Carleman.graphCovectorMap
#check @Carleman.graphCovectorMap_apply
#print axioms Carleman.graphCovectorMap_apply
#check @Carleman.graphCovectorMap_inverse
#print axioms Carleman.graphCovectorMap_inverse
#check @Carleman.graphCovectorMap_norm_bound
#print axioms Carleman.graphCovectorMap_norm_bound
#check @Carleman.graphCovectorMap_lower_bound
#print axioms Carleman.graphCovectorMap_lower_bound
#check @Carleman.graphMetricEntry
#print axioms Carleman.graphMetricEntry
#check @Carleman.graphMetricEntry_energy
#print axioms Carleman.graphMetricEntry_energy
#check @Carleman.graphMetricEntry_symmetric
#print axioms Carleman.graphMetricEntry_symmetric
#check @Carleman.graphMetricEntry_bilinear
#print axioms Carleman.graphMetricEntry_bilinear
#check @Carleman.graphMetricEntry_elliptic
#print axioms Carleman.graphMetricEntry_elliptic
#check @Carleman.graphSlopeVector
#print axioms Carleman.graphSlopeVector
#check @Carleman.graphSlopeVector_apply
#print axioms Carleman.graphSlopeVector_apply
#check @Carleman.graphSlopeVector_contDiff
#print axioms Carleman.graphSlopeVector_contDiff
#check @Carleman.graphSlopeVector_norm
#print axioms Carleman.graphSlopeVector_norm
#check @Carleman.graphSlopeVector_lipschitz
#print axioms Carleman.graphSlopeVector_lipschitz
#check @Carleman.graphCovectorMap_basis_norm
#print axioms Carleman.graphCovectorMap_basis_norm
#check @Carleman.graphCovectorMap_basis_sub
#print axioms Carleman.graphCovectorMap_basis_sub
#check @Carleman.graphMetricEntry_norm
#print axioms Carleman.graphMetricEntry_norm
#check @Carleman.graphMetricEntry_sub_bound
#print axioms Carleman.graphMetricEntry_sub_bound
#check @Carleman.graphMetricEntry_contDiff
#print axioms Carleman.graphMetricEntry_contDiff
#check @Carleman.graphMetricEntry_lipschitz
#print axioms Carleman.graphMetricEntry_lipschitz
#check @Carleman.graphEllipticCoefficient
#print axioms Carleman.graphEllipticCoefficient
#check @Carleman.graphEllipticCoefficient_contDiff
#print axioms Carleman.graphEllipticCoefficient_contDiff
#check @Carleman.graphEllipticCoefficient_lipschitz
#print axioms Carleman.graphEllipticCoefficient_lipschitz
#check @Carleman.graphEllipticCoefficient_elliptic
#print axioms Carleman.graphEllipticCoefficient_elliptic
#check @Carleman.graphMetricEntry_bilinear_coordinates
#print axioms Carleman.graphMetricEntry_bilinear_coordinates
#check @Carleman.graphEllipticCoefficient_pairing
#print axioms Carleman.graphEllipticCoefficient_pairing
#check @Carleman.WeakSobolevJet.graphShearPullback_inverse_gradient
#print axioms Carleman.WeakSobolevJet.graphShearPullback_inverse_gradient
#check @Carleman.graphShearPullback_energy
#print axioms Carleman.graphShearPullback_energy
#check @Carleman.graphShearPullback_equation
#print axioms Carleman.graphShearPullback_equation
#check @Carleman.graphShearPullback_equation_integral
#print axioms Carleman.graphShearPullback_equation_integral

#check @Carleman.exists_dirichlet_H2_of_graph_tangential_invariance
#print axioms Carleman.exists_dirichlet_H2_of_graph_tangential_invariance
#check @Carleman.exists_graphEpigraph_dirichlet_H2
#print axioms Carleman.exists_graphEpigraph_dirichlet_H2
#check @Carleman.spatialGraphShear_hypograph
#print axioms Carleman.spatialGraphShear_hypograph
#check @Carleman.exists_graphHypograph_dirichlet_H2
#print axioms Carleman.exists_graphHypograph_dirichlet_H2

#check @Carleman.SpatialTest.retarget
#print axioms Carleman.SpatialTest.retarget
#check @Carleman.SpatialTest.retarget_fullJet
#print axioms Carleman.SpatialTest.retarget_fullJet
#check @Carleman.SpatialTest.extendDirichlet_pairing_of_support
#print axioms Carleman.SpatialTest.extendDirichlet_pairing_of_support
#check @Carleman.SpatialTest.subdomainZeroExtend_inner_of_support
#print axioms Carleman.SpatialTest.subdomainZeroExtend_inner_of_support
#check @Carleman.SpatialTest.cutoffWeakJet
#print axioms Carleman.SpatialTest.cutoffWeakJet
#check @Carleman.SpatialTest.cutoffWeakJet_value
#print axioms Carleman.SpatialTest.cutoffWeakJet_value
#check @Carleman.SpatialTest.cutoffWeakJet_gradient
#print axioms Carleman.SpatialTest.cutoffWeakJet_gradient
#check @Carleman.SpatialTest.cutoffTransfer
#print axioms Carleman.SpatialTest.cutoffTransfer
#check @Carleman.SpatialTest.cutoff_extendDirichlet_test
#print axioms Carleman.SpatialTest.cutoff_extendDirichlet_test
#check @Carleman.SpatialTest.cutoff_extendDirichlet_mem
#print axioms Carleman.SpatialTest.cutoff_extendDirichlet_mem
#check @Carleman.SpatialTest.cutoffTransferredLoad
#print axioms Carleman.SpatialTest.cutoffTransferredLoad
#check @Carleman.SpatialTest.cutoff_extendDirichlet_equation
#print axioms Carleman.SpatialTest.cutoff_extendDirichlet_equation
#check @Carleman.SpatialTest.cutoff_extendDirichlet_value_ae
#print axioms Carleman.SpatialTest.cutoff_extendDirichlet_value_ae
#check @Carleman.SpatialTest.exists_local_H2_of_cutoff_transfer
#print axioms Carleman.SpatialTest.exists_local_H2_of_cutoff_transfer
#check @Carleman.SpatialTest.exists_local_H2_of_cutoff_graph_epigraph
#print axioms Carleman.SpatialTest.exists_local_H2_of_cutoff_graph_epigraph
#check @Carleman.SpatialTest.exists_local_H2_of_cutoff_graph_hypograph
#print axioms Carleman.SpatialTest.exists_local_H2_of_cutoff_graph_hypograph

#check @Carleman.coordinateLevelMap
#print axioms Carleman.coordinateLevelMap
#check @Carleman.coordinateLevelMap_normal
#print axioms Carleman.coordinateLevelMap_normal
#check @Carleman.coordinateLevelMap_tangent
#print axioms Carleman.coordinateLevelMap_tangent
#check @Carleman.coordinateLevelMap_contDiff
#print axioms Carleman.coordinateLevelMap_contDiff
#check @Carleman.coordinateLevelMap_hasFDerivAt
#print axioms Carleman.coordinateLevelMap_hasFDerivAt
#check @Carleman.coordinateLevelMap_det
#print axioms Carleman.coordinateLevelMap_det
#check @Carleman.exists_nonzero_coordinate_derivative
#print axioms Carleman.exists_nonzero_coordinate_derivative
#check @Carleman.exists_coordinate_level_chart
#print axioms Carleman.exists_coordinate_level_chart
#check @Carleman.coordinateLevelMap_constant_normal_invariant
#print axioms Carleman.coordinateLevelMap_constant_normal_invariant
#check @Carleman.exists_local_coordinate_level_height
#print axioms Carleman.exists_local_coordinate_level_height
#check @Carleman.exists_local_coordinate_level_height_of_regular
#print axioms Carleman.exists_local_coordinate_level_height_of_regular
#check @Carleman.halfspaceSmoothInner_coordinate_level_height
#print axioms Carleman.halfspaceSmoothInner_coordinate_level_height

#check @Carleman.exists_compact_smooth_extension_near
#print axioms Carleman.exists_compact_smooth_extension_near
#check @Carleman.exists_lipschitzWith_of_smooth_compact
#print axioms Carleman.exists_lipschitzWith_of_smooth_compact
#check @Carleman.coordinateTangentProjection
#print axioms Carleman.coordinateTangentProjection
#check @Carleman.coordinateLevelMap_constant_affine
#print axioms Carleman.coordinateLevelMap_constant_affine
#check @Carleman.coordinateLevelMap_constant_lipschitz
#print axioms Carleman.coordinateLevelMap_constant_lipschitz
#check @Carleman.coordinateLevelMap_constant_hasFDerivAt
#print axioms Carleman.coordinateLevelMap_constant_hasFDerivAt
#check @Carleman.exists_smooth_normal_invariant_extension
#print axioms Carleman.exists_smooth_normal_invariant_extension
#check @Carleman.exists_bounded_smooth_coordinate_level_height
#print axioms Carleman.exists_bounded_smooth_coordinate_level_height
#check @Carleman.halfspaceSmoothInner_bounded_coordinate_level_height
#print axioms Carleman.halfspaceSmoothInner_bounded_coordinate_level_height

#check @Carleman.coordinateLine
#print axioms Carleman.coordinateLine
#check @Carleman.coordinateLine_self
#print axioms Carleman.coordinateLine_self
#check @Carleman.coordinateLine_hasDerivAt
#print axioms Carleman.coordinateLine_hasDerivAt
#check @Carleman.coordinateLine_convex_preimage
#print axioms Carleman.coordinateLine_convex_preimage
#check @Carleman.coordinateLine_lt_iff_of_positive
#print axioms Carleman.coordinateLine_lt_iff_of_positive
#check @Carleman.coordinateLine_lt_iff_of_negative
#print axioms Carleman.coordinateLine_lt_iff_of_negative
#check @Carleman.exists_sublevel_hypograph_near_of_positive
#print axioms Carleman.exists_sublevel_hypograph_near_of_positive
#check @Carleman.exists_sublevel_epigraph_near_of_negative
#print axioms Carleman.exists_sublevel_epigraph_near_of_negative
#check @Carleman.exists_sublevel_graph_near_regular
#print axioms Carleman.exists_sublevel_graph_near_regular
#check @Carleman.exists_spatial_cutoff_one_near
#print axioms Carleman.exists_spatial_cutoff_one_near
#check @Carleman.exists_local_dirichlet_H2_of_regular_level
#print axioms Carleman.exists_local_dirichlet_H2_of_regular_level
#check @Carleman.halfspaceSmoothInner_local_boundary_H2
#print axioms Carleman.halfspaceSmoothInner_local_boundary_H2

#check @Carleman.exists_finite_smooth_partition
#print axioms Carleman.exists_finite_smooth_partition
#check @Carleman.SpatialTest.monoDomain_inner
#print axioms Carleman.SpatialTest.monoDomain_inner
#check @Carleman.SpatialTest.monoDomain_derivative_inner
#print axioms Carleman.SpatialTest.monoDomain_derivative_inner
#check @Carleman.SpatialTest.cutoffTransfer_toLp_norm_le
#print axioms Carleman.SpatialTest.cutoffTransfer_toLp_norm_le
#check @Carleman.SpatialTest.partition_jet
#print axioms Carleman.SpatialTest.partition_jet
#check @Carleman.exists_H2_of_finite_local_partition
#print axioms Carleman.exists_H2_of_finite_local_partition
#check @Carleman.exists_H2_of_finite_local_cover
#print axioms Carleman.exists_H2_of_finite_local_cover
#check @Carleman.exists_H2_of_compact_closure_local
#print axioms Carleman.exists_H2_of_compact_closure_local
#check @Carleman.exists_local_interior_H2_ball
#print axioms Carleman.exists_local_interior_H2_ball
#check @Carleman.exists_dirichlet_H2_of_regular_analytic_sublevel
#print axioms Carleman.exists_dirichlet_H2_of_regular_analytic_sublevel
#check @Carleman.halfspaceSmoothInner_dirichlet_H2
#print axioms Carleman.halfspaceSmoothInner_dirichlet_H2

#check @Carleman.smooth_directional_fderiv_eq
#print axioms Carleman.smooth_directional_fderiv_eq
#check @Carleman.second_fderiv_comp_zero_of_tangent
#print axioms Carleman.second_fderiv_comp_zero_of_tangent
#check @Carleman.coordinateLevelMap_const_composition_derivative
#print axioms Carleman.coordinateLevelMap_const_composition_derivative
#check @Carleman.level_graph_gradient_multiple
#print axioms Carleman.level_graph_gradient_multiple
#check @Carleman.second_fderiv_sub_smul
#print axioms Carleman.second_fderiv_sub_smul
#check @Carleman.level_graph_tangent_hessian_multiple
#print axioms Carleman.level_graph_tangent_hessian_multiple
#check @Carleman.regular_level_zero_gradient_hessian
#print axioms Carleman.regular_level_zero_gradient_hessian
#check @Carleman.halfspaceSmoothInner_frontier_of_level
#print axioms Carleman.halfspaceSmoothInner_frontier_of_level
#check @Carleman.halfspaceSmoothInner_zero_gradient_hessian
#print axioms Carleman.halfspaceSmoothInner_zero_gradient_hessian
#check @Carleman.halfspaceExpSum_second_directional
#print axioms Carleman.halfspaceExpSum_second_directional
#check @Carleman.halfspaceExpSum_hessian_nonneg
#print axioms Carleman.halfspaceExpSum_hessian_nonneg

#check Carleman.euclidean_coordinate_expansion
#print axioms Carleman.euclidean_coordinate_expansion
#check Carleman.graphSlopeVector_inner
#print axioms Carleman.graphSlopeVector_inner
#check Carleman.graphSlopeVector_ne_zero
#print axioms Carleman.graphSlopeVector_ne_zero
#check Carleman.graphSlopeVector_multiple
#print axioms Carleman.graphSlopeVector_multiple
#check Carleman.scaledLevelTangent
#print axioms Carleman.scaledLevelTangent
#check Carleman.scaledLevelTangent_inner
#print axioms Carleman.scaledLevelTangent_inner
#check Carleman.bilinear_scaled_tangent_sum
#print axioms Carleman.bilinear_scaled_tangent_sum
#check Carleman.spatialLaplacian_eq_hessian_trace
#print axioms Carleman.spatialLaplacian_eq_hessian_trace
#check Carleman.levelBoundaryFlux
#print axioms Carleman.levelBoundaryFlux
#check Carleman.spatialLaplacian_contDiff
#print axioms Carleman.spatialLaplacian_contDiff
#check Carleman.levelBoundaryFlux_contDiff
#print axioms Carleman.levelBoundaryFlux_contDiff
#check Carleman.levelBoundaryFlux_scaled_identity
#print axioms Carleman.levelBoundaryFlux_scaled_identity
#check Carleman.levelBoundaryFlux_nonneg
#print axioms Carleman.levelBoundaryFlux_nonneg
#check Carleman.halfspaceSmoothInner_boundaryFlux_nonneg
#print axioms Carleman.halfspaceSmoothInner_boundaryFlux_nonneg

#check Carleman.compact_smooth_product_integrable
#print axioms Carleman.compact_smooth_product_integrable
#check Carleman.integral_smoothD_compact
#print axioms Carleman.integral_smoothD_compact
#check Carleman.weighted_mixed_derivative_pair
#print axioms Carleman.weighted_mixed_derivative_pair
#check Carleman.weighted_hessian_pair
#print axioms Carleman.weighted_hessian_pair
#check Carleman.smoothHessianSq
#print axioms Carleman.smoothHessianSq
#check Carleman.smoothHessianSq_contDiff
#print axioms Carleman.smoothHessianSq_contDiff
#check Carleman.levelBoundaryFlux_eq_double_sum
#print axioms Carleman.levelBoundaryFlux_eq_double_sum
#check Carleman.weighted_hessian_identity
#print axioms Carleman.weighted_hessian_identity
#check Carleman.weighted_level_hessian_identity
#print axioms Carleman.weighted_level_hessian_identity
#check Carleman.weighted_laplacian_identity
#print axioms Carleman.weighted_laplacian_identity
#check Carleman.weighted_level_gradient_mass
#print axioms Carleman.weighted_level_gradient_mass

#check Carleman.smoothTransition_deriv_zero_of_nonpos
#print axioms Carleman.smoothTransition_deriv_zero_of_nonpos
#check Carleman.smoothTransition_deriv_zero_of_one_le
#print axioms Carleman.smoothTransition_deriv_zero_of_one_le
#check Carleman.levelCutoff
#print axioms Carleman.levelCutoff
#check Carleman.levelLayerWeight
#print axioms Carleman.levelLayerWeight
#check Carleman.levelCutoff_contDiff
#print axioms Carleman.levelCutoff_contDiff
#check Carleman.levelLayerWeight_contDiff
#print axioms Carleman.levelLayerWeight_contDiff
#check Carleman.levelCutoff_bounds
#print axioms Carleman.levelCutoff_bounds
#check Carleman.levelLayerWeight_nonneg
#print axioms Carleman.levelLayerWeight_nonneg
#check Carleman.levelCutoff_zero
#print axioms Carleman.levelCutoff_zero
#check Carleman.levelCutoff_one
#print axioms Carleman.levelCutoff_one
#check Carleman.levelLayerWeight_zero_outer
#print axioms Carleman.levelLayerWeight_zero_outer
#check Carleman.levelLayerWeight_zero_inner
#print axioms Carleman.levelLayerWeight_zero_inner
#check Carleman.levelCutoff_fderiv
#print axioms Carleman.levelCutoff_fderiv
#check Carleman.levelCutoff_tsupport
#print axioms Carleman.levelCutoff_tsupport
#check Carleman.levelLayerWeight_tsupport
#print axioms Carleman.levelLayerWeight_tsupport
#check Carleman.levelCutoff_compact
#print axioms Carleman.levelCutoff_compact
#check Carleman.levelLayerWeight_compact
#print axioms Carleman.levelLayerWeight_compact
#check Carleman.levelCutoff_tendsto
#print axioms Carleman.levelCutoff_tendsto
#check Carleman.levelCutoff_hessian_identity
#print axioms Carleman.levelCutoff_hessian_identity
#check Carleman.levelCutoff_gradient_mass
#print axioms Carleman.levelCutoff_gradient_mass

#check Carleman.exists_positive_level_layer
#print axioms Carleman.exists_positive_level_layer
#check Carleman.levelLayer_flux_lower_bound
#print axioms Carleman.levelLayer_flux_lower_bound
#check Carleman.continuous_integrableOn_bounded_sublevel
#print axioms Carleman.continuous_integrableOn_bounded_sublevel
#check Carleman.levelCutoff_integral_tendsto
#print axioms Carleman.levelCutoff_integral_tendsto
#check Carleman.levelCutoff_mass_bound
#print axioms Carleman.levelCutoff_mass_bound
#check Carleman.levelCutoff_defect_lower_bound
#print axioms Carleman.levelCutoff_defect_lower_bound
#check Carleman.classical_level_hessian_defect_nonneg
#print axioms Carleman.classical_level_hessian_defect_nonneg
#check Carleman.classical_level_hessian_le_laplacian
#print axioms Carleman.classical_level_hessian_le_laplacian
#check Carleman.halfspaceSmoothInner_classical_hessian_bound
#print axioms Carleman.halfspaceSmoothInner_classical_hessian_bound

#check Carleman.WeakSobolevJet.valueLiftLinear
#print axioms Carleman.WeakSobolevJet.valueLiftLinear
#check Carleman.WeakSobolevJet.valueLiftLinear_value
#print axioms Carleman.WeakSobolevJet.valueLiftLinear_value
#check Carleman.WeakSobolevJet.valueLiftLinear_closedGraph
#print axioms Carleman.WeakSobolevJet.valueLiftLinear_closedGraph
#check Carleman.WeakSobolevJet.valueLiftCLM
#print axioms Carleman.WeakSobolevJet.valueLiftCLM
#check Carleman.WeakSobolevJet.valueLiftCLM_value
#print axioms Carleman.WeakSobolevJet.valueLiftCLM_value
#check Carleman.WeakSobolevJet.valueLiftCLM_unique
#print axioms Carleman.WeakSobolevJet.valueLiftCLM_unique
#check Carleman.WeakSobolevJet.graphShear_H2_value_exists
#print axioms Carleman.WeakSobolevJet.graphShear_H2_value_exists
#check Carleman.WeakSobolevJet.graphShearH2Pullback
#print axioms Carleman.WeakSobolevJet.graphShearH2Pullback
#check Carleman.WeakSobolevJet.graphShearH2Pullback_value
#print axioms Carleman.WeakSobolevJet.graphShearH2Pullback_value
#check Carleman.WeakSobolevJet.graphShearH2Pullback_ae
#print axioms Carleman.WeakSobolevJet.graphShearH2Pullback_ae
#check Carleman.WeakSobolevJet.graphShearH2Pullback_truncate
#print axioms Carleman.WeakSobolevJet.graphShearH2Pullback_truncate
#check Carleman.WeakSobolevJet.graphShearH2Pullback_dirichlet
#print axioms Carleman.WeakSobolevJet.graphShearH2Pullback_dirichlet
#check Carleman.WeakSobolevJet.graphShearH2Pullback_tendsto
#print axioms Carleman.WeakSobolevJet.graphShearH2Pullback_tendsto
#check Carleman.WeakSobolevJet.graphShearH2Pullback_test
#print axioms Carleman.WeakSobolevJet.graphShearH2Pullback_test

#check Carleman.derivativeFieldAssembly_components
#print axioms Carleman.derivativeFieldAssembly_components
#check Carleman.derivativeField_tendsto_of_components
#print axioms Carleman.derivativeField_tendsto_of_components
#check Carleman.WeakSobolevJet.tendsto_of_components
#print axioms Carleman.WeakSobolevJet.tendsto_of_components
#check Carleman.SpatialTest.allOrderJetOn
#print axioms Carleman.SpatialTest.allOrderJetOn
#check Carleman.SpatialTest.allOrderJetOn_component
#print axioms Carleman.SpatialTest.allOrderJetOn_component
#check Carleman.SpatialTest.allOrderJetOn_value
#print axioms Carleman.SpatialTest.allOrderJetOn_value
#check Carleman.SpatialTest.allOrderJetOn_component_one_ae
#print axioms Carleman.SpatialTest.allOrderJetOn_component_one_ae
#check Carleman.SpatialTest.allOrderJetOn_component_two_ae
#print axioms Carleman.SpatialTest.allOrderJetOn_component_two_ae
#check Carleman.SpatialTest.allOrderJetOn_dirichlet
#print axioms Carleman.SpatialTest.allOrderJetOn_dirichlet
#check Carleman.SpatialTest.allOrderJetOn_two_tendsto_of_errors
#print axioms Carleman.SpatialTest.allOrderJetOn_two_tendsto_of_errors
#check Carleman.exists_box_dirichlet_strong_h2_approximation
#print axioms Carleman.exists_box_dirichlet_strong_h2_approximation

#check Carleman.WeakSobolevJet.truncateCLM
#print axioms Carleman.WeakSobolevJet.truncateCLM
#check Carleman.dirichletH2JetSpace
#print axioms Carleman.dirichletH2JetSpace
#check Carleman.dirichletH2JetSpace_isClosed
#print axioms Carleman.dirichletH2JetSpace_isClosed
#check Carleman.dirichletH2JetSpace_complete
#print axioms Carleman.dirichletH2JetSpace_complete
#check Carleman.dirichletH2ValueCLM
#print axioms Carleman.dirichletH2ValueCLM
#check Carleman.dirichletH2LiftLinear
#print axioms Carleman.dirichletH2LiftLinear
#check Carleman.dirichletH2LiftLinear_value
#print axioms Carleman.dirichletH2LiftLinear_value
#check Carleman.dirichletH2LiftLinear_closedGraph
#print axioms Carleman.dirichletH2LiftLinear_closedGraph
#check Carleman.dirichletH2LiftCLM
#print axioms Carleman.dirichletH2LiftCLM
#check Carleman.dirichletH2LiftCLM_value
#print axioms Carleman.dirichletH2LiftCLM_value
#check Carleman.DirichletH2Regular
#print axioms Carleman.DirichletH2Regular
#check Carleman.dirichletH2Regular_box
#print axioms Carleman.dirichletH2Regular_box
#check Carleman.dirichletH2Regular_graphEpigraph
#print axioms Carleman.dirichletH2Regular_graphEpigraph
#check Carleman.dirichletH2Regular_graphHypograph
#print axioms Carleman.dirichletH2Regular_graphHypograph
#check Carleman.dirichletH2Regular_smoothInner
#print axioms Carleman.dirichletH2Regular_smoothInner
#check Carleman.SpatialTest.cutoffValueTransfer
#print axioms Carleman.SpatialTest.cutoffValueTransfer
#check Carleman.SpatialTest.cutoffValueTransfer_apply
#print axioms Carleman.SpatialTest.cutoffValueTransfer_apply
#check Carleman.SpatialTest.cutoffH2_value_exists
#print axioms Carleman.SpatialTest.cutoffH2_value_exists
#check Carleman.SpatialTest.cutoffH2Transfer
#print axioms Carleman.SpatialTest.cutoffH2Transfer
#check Carleman.SpatialTest.cutoffH2Transfer_value
#print axioms Carleman.SpatialTest.cutoffH2Transfer_value
#check Carleman.SpatialTest.cutoffH2Transfer_truncate
#print axioms Carleman.SpatialTest.cutoffH2Transfer_truncate
#check Carleman.SpatialTest.cutoffH2Transfer_dirichlet
#print axioms Carleman.SpatialTest.cutoffH2Transfer_dirichlet
#check Carleman.SpatialTest.cutoffH2Transfer_tendsto
#print axioms Carleman.SpatialTest.cutoffH2Transfer_tendsto
#check Carleman.SpatialTest.cutoffH2Transfer_ae
#print axioms Carleman.SpatialTest.cutoffH2Transfer_ae
#check Carleman.SpatialTest.cutoffH2Transfer_of_smooth
#print axioms Carleman.SpatialTest.cutoffH2Transfer_of_smooth
#check Carleman.SpatialTest.frontier_mem_of_cutoff_agreement
#print axioms Carleman.SpatialTest.frontier_mem_of_cutoff_agreement
#check Carleman.SpatialTest.cutoffTransfer_boundary_zero
#print axioms Carleman.SpatialTest.cutoffTransfer_boundary_zero
#check Carleman.SpatialTest.exists_cutoff_box_strong_h2_approximation
#print axioms Carleman.SpatialTest.exists_cutoff_box_strong_h2_approximation

#check Carleman.SpatialTest.cutoffH2Transfer_roundtrip
#print axioms Carleman.SpatialTest.cutoffH2Transfer_roundtrip
#check Carleman.exists_compact_localbox_strong_h2_approximation
#print axioms Carleman.exists_compact_localbox_strong_h2_approximation
#check Carleman.signedCoordinateHalfspace
#print axioms Carleman.signedCoordinateHalfspace
#check Carleman.signedCoordinateHalfspace_isOpen
#print axioms Carleman.signedCoordinateHalfspace_isOpen
#check Carleman.dirichletH2Regular_signedHalfspace
#print axioms Carleman.dirichletH2Regular_signedHalfspace
#check Carleman.exists_signedHalfspace_box_cutoff
#print axioms Carleman.exists_signedHalfspace_box_cutoff
#check Carleman.exists_compact_halfspace_strong_h2_approximation
#print axioms Carleman.exists_compact_halfspace_strong_h2_approximation
#check Carleman.dirichletH2Regular_univ
#print axioms Carleman.dirichletH2Regular_univ
#check Carleman.exists_fullspace_box_cutoff
#print axioms Carleman.exists_fullspace_box_cutoff
#check Carleman.exists_compact_fullspace_strong_h2_approximation
#print axioms Carleman.exists_compact_fullspace_strong_h2_approximation

#check Carleman.WeakSobolevJet.graphShearInverseH2_value_exists
#print axioms Carleman.WeakSobolevJet.graphShearInverseH2_value_exists
#check Carleman.WeakSobolevJet.graphShearInverseH2
#print axioms Carleman.WeakSobolevJet.graphShearInverseH2
#check Carleman.WeakSobolevJet.graphShearInverseH2_value
#print axioms Carleman.WeakSobolevJet.graphShearInverseH2_value
#check Carleman.WeakSobolevJet.graphShearInverseH2_dirichlet
#print axioms Carleman.WeakSobolevJet.graphShearInverseH2_dirichlet
#check Carleman.WeakSobolevJet.graphShearInverseH2_left_inverse
#print axioms Carleman.WeakSobolevJet.graphShearInverseH2_left_inverse
#check Carleman.WeakSobolevJet.graphShearInverseH2_right_inverse
#print axioms Carleman.WeakSobolevJet.graphShearInverseH2_right_inverse
#check Carleman.WeakSobolevJet.graphShearInverseH2_tendsto
#print axioms Carleman.WeakSobolevJet.graphShearInverseH2_tendsto
#check Carleman.WeakSobolevJet.graphShearH2Pullback_globalTest
#print axioms Carleman.WeakSobolevJet.graphShearH2Pullback_globalTest
#check Carleman.WeakSobolevJet.graphShearInverseH2_globalTest
#print axioms Carleman.WeakSobolevJet.graphShearInverseH2_globalTest
#check Carleman.exists_compact_graphShear_strong_h2_approximation
#print axioms Carleman.exists_compact_graphShear_strong_h2_approximation
#check Carleman.graphCoordinateSide
#print axioms Carleman.graphCoordinateSide
#check Carleman.graphCoordinateSide_isOpen
#print axioms Carleman.graphCoordinateSide_isOpen
#check Carleman.graphCoordinateSide_preimage
#print axioms Carleman.graphCoordinateSide_preimage
#check Carleman.exists_compact_graphSide_strong_h2_approximation
#print axioms Carleman.exists_compact_graphSide_strong_h2_approximation

#check Carleman.HasSmoothDirichletH2Approximation
#print axioms Carleman.HasSmoothDirichletH2Approximation
#check Carleman.SpatialTest.cutoffH2Transfer_approximation
#print axioms Carleman.SpatialTest.cutoffH2Transfer_approximation
#check Carleman.SpatialTest.cutoffH2Transfer_nested_roundtrip
#print axioms Carleman.SpatialTest.cutoffH2Transfer_nested_roundtrip
#check Carleman.SpatialTest.cutoffH2Transfer_off_support
#print axioms Carleman.SpatialTest.cutoffH2Transfer_off_support
#check Carleman.exists_localized_strong_h2_approximation
#print axioms Carleman.exists_localized_strong_h2_approximation
#check Carleman.compact_fullspace_hasSmoothDirichletH2Approximation
#print axioms Carleman.compact_fullspace_hasSmoothDirichletH2Approximation
#check Carleman.dirichletH2Regular_graphSide
#print axioms Carleman.dirichletH2Regular_graphSide
#check Carleman.exists_interior_local_strong_h2_approximation
#print axioms Carleman.exists_interior_local_strong_h2_approximation
#check Carleman.exists_boundary_local_strong_h2_approximation
#print axioms Carleman.exists_boundary_local_strong_h2_approximation
#check Carleman.SpatialTest.sumTest
#print axioms Carleman.SpatialTest.sumTest
#check Carleman.SpatialTest.sumTest_allOrderJetOn
#print axioms Carleman.SpatialTest.sumTest_allOrderJetOn
#check Carleman.SpatialTest.cutoffH2Transfer_partition
#print axioms Carleman.SpatialTest.cutoffH2Transfer_partition
#check Carleman.hasSmoothDirichletH2Approximation_sum
#print axioms Carleman.hasSmoothDirichletH2Approximation_sum
#check Carleman.hasSmoothDirichletH2Approximation_of_finite_cover
#print axioms Carleman.hasSmoothDirichletH2Approximation_of_finite_cover
#check Carleman.hasSmoothDirichletH2Approximation_of_compact_closure_local
#print axioms Carleman.hasSmoothDirichletH2Approximation_of_compact_closure_local
#check Carleman.regular_analytic_sublevel_strong_h2_approximation
#print axioms Carleman.regular_analytic_sublevel_strong_h2_approximation
#check Carleman.halfspaceSmoothInner_strong_h2_approximation
#print axioms Carleman.halfspaceSmoothInner_strong_h2_approximation

#check Carleman.realLp_norm_sq_of_ae
#print axioms Carleman.realLp_norm_sq_of_ae
#check Carleman.SpatialTest.allOrderJetOn_component_two_smoothD_ae
#print axioms Carleman.SpatialTest.allOrderJetOn_component_two_smoothD_ae
#check Carleman.SpatialTest.allOrderJetOn_negativeLaplacian
#print axioms Carleman.SpatialTest.allOrderJetOn_negativeLaplacian
#check Carleman.SpatialTest.allOrderJetOn_negativeLaplacian_norm_sq
#print axioms Carleman.SpatialTest.allOrderJetOn_negativeLaplacian_norm_sq
#check Carleman.SpatialTest.allOrderJetOn_component_sq_le_hessian
#print axioms Carleman.SpatialTest.allOrderJetOn_component_sq_le_hessian
#check Carleman.SpatialTest.allOrderJetOn_hessian_bound_of_classical
#print axioms Carleman.SpatialTest.allOrderJetOn_hessian_bound_of_classical
#check Carleman.weak_hessian_bound_of_strong_density
#print axioms Carleman.weak_hessian_bound_of_strong_density
#check Carleman.halfspaceSmoothInner_weak_hessian_bound
#print axioms Carleman.halfspaceSmoothInner_weak_hessian_bound
#check Carleman.halfspaceSmoothInner_weak_hessian_norm_bound
#print axioms Carleman.halfspaceSmoothInner_weak_hessian_norm_bound

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants.toList do
    if (`Carleman).isPrefixOf (privateToUserName name) then
      for ax in ← collectAxioms name do
        unless allowed.contains ax do
          throwError "{name} depends on an unapproved axiom: {ax}"
      checked := checked + 1
  logInfo m!"Axiom audit passed for all {checked} Carleman declarations."

