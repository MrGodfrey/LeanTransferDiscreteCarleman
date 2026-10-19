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
#check @Carleman.BoundedMultiplier.restrictMeasure
#print axioms Carleman.BoundedMultiplier.restrictMeasure
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
