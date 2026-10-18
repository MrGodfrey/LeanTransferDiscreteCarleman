module

public import Carleman.Weights.ClosureConforming
public import Carleman.Weights.AllowedFormBounds
public import Carleman.Spatial.WeightedEnergySeminorm

/-! The actual σ² test has a uniform bound from Nσ to Nσ⁻¹.
Two conjugation inequalities suffice, so no enlarged allowed exponent range
or new smoothness assumption is needed. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hbounded : Bornology.IsBounded S)
  (hν : ∀ᵐ x ∂ν, x ∈ S)
  {V : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d m ν S)

include hbounded in
/-- One constant for all time weights, exponents, times and conforming states. -/
theorem squared_weight_test_uniform (ρ : SpatialProfile ν) (hρ : SmoothOnClosure ρ.value S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : TimeWeight) (τ t : ℝ)
      (hw : ∀ v : V, (ρ.multiplier w τ t).map (v : Lp ℝ 2 ν) ∈ V)
      (_hξ : ∀ v : V, (ρ.neg.multiplier w (-τ) t).map (v : Lp ℝ 2 ν) ∈ V) (v : V),
      conformingWeightedNorm hS hν hV (w.q t) (ρ.neg.multiplier w (-τ) t)
        (conformingWeight (ρ.multiplier w τ t) hw (conformingWeight (ρ.multiplier w τ t) hw v)) ≤
      C*conformingWeightedNorm hS hν hV (w.q t) (ρ.multiplier w τ t) v := by
  obtain ⟨J,hJ,hconj⟩ := closure_conforming_conjugation_uniform hS hbounded hν hV ρ hρ
  refine ⟨J^2,sq_pos_of_pos hJ,?_⟩
  intro w τ t hw hξ v
  let W := conformingWeight (ρ.multiplier w τ t) hw
  let I := conformingWeight (ρ.neg.multiplier w (-τ) t) hξ
  have hcancel : I (W (W v)) = W v := by
    apply Subtype.ext
    change (ρ.neg.multiplier w (-τ) t).map
      ((ρ.multiplier w τ t).map ((ρ.multiplier w τ t).map (v : Lp ℝ 2 ν))) = _
    exact (ρ.neg.multiplier w (-τ) t).map_inverse (ρ.multiplier w τ t)
      (Filter.Eventually.of_forall fun x => by
        have he := ρ.multiplier_inverse w τ t x
        rwa [mul_comm] at he) _
  have hi := (hconj w (-τ) t true hξ (W (W v))).2.2.2
  change conformingWeightedNorm hS hν hV (w.q t) (ρ.neg.multiplier w (-τ) t) (W (W v)) ≤
    J*conformingWeightedNorm hS hν hV (w.q t) BoundedMultiplier.one (I (W (W v))) at hi
  rw [hcancel] at hi
  have hw' := (hconj w τ t false hw v).2.2.1
  change conformingWeightedNorm hS hν hV (w.q t) BoundedMultiplier.one (W v) ≤
    J*conformingWeightedNorm hS hν hV (w.q t) (ρ.multiplier w τ t) v at hw'
  exact hi.trans ((mul_le_mul_of_nonneg_left hw' hJ.le).trans_eq (by ring))

end Carleman
