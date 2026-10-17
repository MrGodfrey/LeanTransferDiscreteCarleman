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
