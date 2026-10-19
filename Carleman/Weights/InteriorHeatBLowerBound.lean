module

public import Carleman.Weights.HeatRemainderBound

/-! Uniform-in-time and weight bounds for the actual Gaussian B coefficient. -/
@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace Carleman
variable {d : ℕ}

def interiorHeatLeadingCoefficient (c : SpatialCoordinates d) (l Q : ℝ)
    (x : SpatialCoordinates d) : ℝ :=
  4*Q^3*l^3*(interiorGaussian c l x)^3*‖gradient (interiorQuadratic c) x‖^2*
    (l*‖gradient (interiorQuadratic c) x‖^2-6)

theorem interiorGaussianHeatB_uniform_lower_bound {S : Set (SpatialCoordinates d)}
    (hS : Bornology.IsBounded S) (c : SpatialCoordinates d) (l : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ → ℝ, ContDiff ℝ ∞ q → ∀ β : ℝ, 0 ≤ β →
      ∀ t : ℝ, 1 ≤ q t → |deriv q t| ≤ β*(q t)^2 →
      |deriv (deriv q) t| ≤ β^2*(q t)^3 → ∀ x ∈ S,
      interiorHeatLeadingCoefficient c l (q t) x-C*((q t)^2+(β+β^2)*(q t)^3) ≤
      pointwiseHeatB spaceTimeSpatialDirection (1,0) (interiorGaussianHeatPhase c l q)
        (heatConjugationK spaceTimeSpatialDirection (1,0)
          (interiorGaussianHeatPhase c l q) (interiorGaussianHeatPsi c l q))
        (interiorGaussianHeatPsi c l q) (t,x) := by
  let ρ := interiorCarlemanProfile c l
  let A₂ : SpatialCoordinates d → ℝ := fun x =>
    64*l^3*(interiorGaussian c l x)^2*‖x-c‖^2-128*l^2*(interiorGaussian c l x)^2
  let A₁ : SpatialCoordinates d → ℝ := fun x =>
    16*l^2*(interiorGaussian c l x)^2*‖x-c‖^2-16*l*interiorGaussian c l x*ρ x
  let A₀ : SpatialCoordinates d → ℝ := fun x => 8*l*interiorGaussian c l x
  have hφ := (interiorGaussian_contDiff c l).continuous
  have hρ : Continuous ρ := (interiorCarlemanProfile_contDiff c l).continuous
  have hA₂ : Continuous A₂ := by fun_prop
  have hA₁ : Continuous A₁ := by fun_prop
  have hA₀ : Continuous A₀ := by fun_prop
  let H : SpatialCoordinates d → ℝ := fun x => |A₂ x|+|A₁ x|+|A₀ x|+|ρ x|
  have hH : Continuous H := ((hA₂.abs.add hA₁.abs).add hA₀.abs).add hρ.abs
  obtain ⟨K₀,hK₀⟩ := hS.isCompact_closure.exists_bound_of_continuousOn hH.continuousOn
  let K := |K₀|+1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hbound : ∀ x ∈ S, |A₂ x|+|A₁ x|+|A₀ x|+|ρ x| ≤ K := by
    intro x hx
    have hh := hK₀ x (subset_closure hx)
    rw [Real.norm_eq_abs] at hh
    have h := le_abs_self (H x)
    have h0 := le_abs_self K₀
    dsimp only [H,K] at *
    linarith
  refine ⟨2*K,by positivity,?_⟩
  intro q hq β hβ t ht hq₁ hq₂ x hx
  have hb := hbound x hx
  have h2 : |A₂ x| ≤ K := by linarith [abs_nonneg (A₁ x),abs_nonneg (A₀ x),abs_nonneg (ρ x)]
  have h1 : |A₁ x| ≤ K := by linarith [abs_nonneg (A₂ x),abs_nonneg (A₀ x),abs_nonneg (ρ x)]
  have h0 : |A₀ x| ≤ K := by linarith [abs_nonneg (A₂ x),abs_nonneg (A₁ x),abs_nonneg (ρ x)]
  have hr : |ρ x| ≤ K := by linarith [abs_nonneg (A₂ x),abs_nonneg (A₁ x),abs_nonneg (A₀ x)]
  have he := heat_remainder_bound hK.le ht hβ hq₁ hq₂ h2 h1 h0 hr
  have hlo := (abs_le.mp he).1
  rw [interiorGaussianHeatB_leading c l hq]
  dsimp only [interiorHeatLeadingCoefficient,A₂,A₁,A₀,ρ] at hlo ⊢
  nlinarith

end Carleman
