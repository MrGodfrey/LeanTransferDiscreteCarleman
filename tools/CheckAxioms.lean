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
