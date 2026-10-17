module

public import Carleman.Weights.WeightedWeakTrajectory

/-! Exact conjugation of the original weak evolution, for both orientations.
All operator evaluations use the canonical a.e. domain representatives. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.PeriodicWeakTrajectory
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)}
  {D : Submodule ℝ (Lp ℝ 2 ν)} {A : D →ₗ[ℝ] Lp ℝ 2 ν}
  {g : TimeGrid} {w : TimeWeight} {β : ℝ} (h : TimeWeightRegularity w g β)
  (ρ : SpatialProfile ν) (τ : ℝ)
  (hw : ∀ t (u : D), (ρ.multiplier w τ t).map (u : Lp ℝ 2 ν) ∈ D)
  (hξ : ∀ t (u : D), (ρ.neg.multiplier w (-τ) t).map (u : Lp ℝ 2 ν) ∈ D)

/-- Equality of weighted H trajectories also identifies their actual domain
representatives a.e.; no everywhere D(A) regularity is added. -/
theorem domainValue_of_weighted (u v : PeriodicWeakTrajectory g D A)
    (hv : v.value = (fun t => (ρ.multiplier w τ t).map (u.value t))) :
    v.domainValue =ᵐ[g.timeMeasure]
      (fun t => conformingWeight (ρ.multiplier w τ t) (hw t) (u.domainValue t)) := by
  filter_upwards [v.domainValue_ae, u.domainValue_ae] with t ht hu
  apply Subtype.ext
  change (v.domainValue t : Lp ℝ 2 ν) = (ρ.multiplier w τ t).map (u.domainValue t : Lp ℝ 2 ν)
  rw [ht, hu, hv]

/-- Equation (9.26-eq2) for the actual weak derivative and both time signs.
The supplied equalities merely identify the weighted path constructed above. -/
theorem weighted_conjugation_identity (u v : PeriodicWeakTrajectory g D A)
    (hv : v.value = (fun t => (ρ.multiplier w τ t).map (u.value t)))
    (hdv : v.derivative = ρ.weightedTimeDerivative h τ u.value u.derivative)
    (s : Orientation) (μ : ℝ → ℝ) :
    ∀ᵐ t ∂g.timeMeasure,
      s.sign • v.derivative t + A (v.domainValue t) + μ t • v.value t =
        (ρ.multiplier w τ t).map
          (s.sign • u.derivative t + A (u.domainValue t) + μ t • u.value t) +
        conjugatedCommutator A (ρ.multiplier w τ t) (ρ.neg.multiplier w (-τ) t)
          (hw t) (hξ t) (v.domainValue t) +
        s.sign • ρ.logDerivativeAction h τ t (v.value t) := by
  filter_upwards [domainValue_of_weighted ρ τ hw u v hv] with t ht
  have hi : conformingWeight (ρ.neg.multiplier w (-τ) t) (hξ t) (v.domainValue t) =
      u.domainValue t := by
    rw [ht]
    apply Subtype.ext
    exact BoundedMultiplier.map_inverse _ _
      (Filter.Eventually.of_forall fun x => by rw [mul_comm]; exact ρ.multiplier_inverse w τ t x) _
  rw [conjugatedCommutator_eq A _ _ _ _
    (Filter.Eventually.of_forall (ρ.multiplier_inverse w τ t)), hi, hdv, hv]
  simp only [SpatialProfile.weightedTimeDerivative, BoundedMultiplier.map_add,
    BoundedMultiplier.map_smul]
  module
end Carleman.PeriodicWeakTrajectory
