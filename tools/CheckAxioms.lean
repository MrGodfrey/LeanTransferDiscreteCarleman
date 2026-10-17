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
