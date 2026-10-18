module

public import Carleman.Section3.SignedUniform

/-! Exactly A2 and both A3 bounds for the allowed positive/inverse profile
family. No conclusion, interpolation inequality or error bound is a field. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Section3
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {V D : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d m ν S)
  (hD : D ≤ sobolevSubspace d (2*m) ν S) (a : V → V → ℝ) (A : D →ₗ[ℝ] Lp ℝ 2 ν)
  (ρ : SpatialProfile ν) (w : TimeWeight) (c C Ccomm τStar : ℝ)

structure AllowedFamily : Prop where
  data : ∀ (e : Bool) (τ : ℝ), |τ| ≤ τStar → AllowedWeightData hS hν hV hD a A (ρ.signed e) w τ c C Ccomm
  upper : ∀ (e : Bool) (τ : ℝ), |τ| ≤ τStar → ∀ (t : ℝ) (v z : V),
    |a v z| ≤ C*conformingWeightedNorm hS hν hV (w.q t) ((ρ.signed e).multiplier w τ t) v *
      conformingWeightedNorm hS hν hV (w.q t) ((ρ.signed e).neg.multiplier w (-τ) t) z

theorem AllowedFamily.inverse (h : AllowedFamily hS hν hV hD a A ρ w c C Ccomm τStar)
    (e : Bool) (τ : ℝ) (hτ : |τ| ≤ τStar) :
    AllowedWeightData hS hν hV hD a A (ρ.signed e).neg w (-τ) c C Ccomm := by
  rw [ρ.signed_neg]
  exact h.data (!e) (-τ) (by simpa only [abs_neg] using hτ)
end Carleman.Section3
