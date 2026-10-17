module

public import Carleman.Weights.IntrinsicConjugation
public import Carleman.Weights.ConformingConjugation
public import Carleman.Spatial.ShiftedFormBounds

/-! A2's actual domain multiplication realizes the two-sided spatial estimates.
One constant handles all times, time weights, exponents, signs and states. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Carleman
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hbounded : Bornology.IsBounded S)
  (hνS : ∀ᵐ x ∂ν, x ∈ S)
  {D : Submodule ℝ (Lp ℝ 2 ν)} (hD : D ≤ sobolevSubspace d n ν S)

include hbounded
/-- Simultaneous positive/inverse-profile norm comparisons. n=2m gives R,
n=m gives N. No time-domain or frequency restriction enters the constant. -/
theorem closure_conforming_conjugation_uniform (ρ : SpatialProfile ν) (hρ : SmoothOnClosure ρ.value S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : TimeWeight) (τ t : ℝ) (negative : Bool),
      let σ := ((if negative then ρ.neg else ρ).multiplier w τ t)
      ∀ hw : ∀ u : D, σ.map (u : Lp ℝ 2 ν) ∈ D,
      ∀ u : D,
        conformingParameterNorm hS hνS hD (w.q t) BoundedMultiplier.one (conformingWeight σ hw u) ≤
          C*conformingParameterNorm hS hνS hD (w.q t) σ u ∧
        conformingParameterNorm hS hνS hD (w.q t) σ u ≤
          C*conformingParameterNorm hS hνS hD (w.q t) BoundedMultiplier.one (conformingWeight σ hw u) ∧
        conformingWeightedNorm hS hνS hD (w.q t) BoundedMultiplier.one (conformingWeight σ hw u) ≤
          C*conformingWeightedNorm hS hνS hD (w.q t) σ u ∧
        conformingWeightedNorm hS hνS hD (w.q t) σ u ≤
          C*conformingWeightedNorm hS hνS hD (w.q t) BoundedMultiplier.one (conformingWeight σ hw u) := by
  obtain ⟨C₁, hC₁, hR⟩ := intrinsic_allowedWeight_parameterNorm_uniform (n := n) hS hνS (hρ.boundedSmoothOn hbounded)
  obtain ⟨C₂, hC₂, hN⟩ := intrinsic_allowedWeight_weightedNorm_uniform (n := n) hS hνS (hρ.boundedSmoothOn hbounded)
  refine ⟨max C₁ C₂, hC₁.trans_le (le_max_left _ _), ?_⟩
  intro w τ t negative σ hw u
  let eta : ℝ := if negative then -1 else 1
  have heta : |eta|=1 := by cases negative <;> norm_num [eta]
  have hσ : σ.value = (fun x => w.q t^τ*Real.exp (w.q t*(eta*ρ.value x))) := by
    funext x
    cases negative <;> simp [σ, eta, SpatialProfile.multiplier, SpatialProfile.neg, mul_comm]
  have he : WeakSobolevJet.value (domainSobolevJet hS hνS hD (conformingWeight σ hw u)) =
      σ.map (WeakSobolevJet.value (domainSobolevJet hS hνS hD u)) := by
    rw [domainSobolevJet_value, domainSobolevJet_value]
    rfl
  obtain ⟨h1, h2⟩ := hR (w.q t) (w.lower t) τ eta heta σ hσ _ _ he
  obtain ⟨h3, h4⟩ := hN (w.q t) (w.lower t) τ eta heta σ hσ _ _ he
  exact ⟨h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (WeakSobolevJet.parameterNorm_nonneg (w.nonneg t) _ _)),
    h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (WeakSobolevJet.parameterNorm_nonneg (w.nonneg t) _ _)),
    h3.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (WeakSobolevJet.weightedNorm_nonneg _ _ _)),
    h4.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (WeakSobolevJet.weightedNorm_nonneg _ _ _))⟩
end Carleman
