module

public import Carleman.Weights.InteriorHeatPotential
public import Carleman.Weights.HeatAbsorptionParameters

/-! Pointwise absorption for the actual heat-cross potential and observation indicator. -/
@[expose] public noncomputable section
open Set
namespace Carleman
variable {d : ℕ}

theorem interiorHeat_observation_absorption (c : SpatialCoordinates d) (l : ℝ)
    (W : Set (SpatialCoordinates d)) (x : SpatialCoordinates d)
    {a m K C Q β E Z : ℝ} (hQ : 0 ≤ Q) (hE : 0 ≤ E)
    (ha : a ≤ l*interiorGaussian c l x)
    (hm : m ≤ interiorHeatPotential c l x+W.indicator (fun _ => K) x)
    (hsmall : C*(Q^2+(β+β^2)*Q^3) ≤ (m/2)*Q^3) :
    a*Q*E+(m/2)*Q^3*Z^2+C*(Q^2+(β+β^2)*Q^3)*Z^2 ≤
      Q*l*interiorGaussian c l x*E+Q^3*interiorHeatPotential c l x*Z^2+
        K*W.indicator (fun _ => Q^3*Z^2) x := by
  classical
  have h1 := mul_le_mul_of_nonneg_right ha (mul_nonneg hQ hE)
  have h2 := mul_le_mul_of_nonneg_right hm (show 0 ≤ Q^3*Z^2 by positivity)
  have h3 := mul_le_mul_of_nonneg_right hsmall (sq_nonneg Z)
  by_cases hx : x ∈ W
  · simp only [indicator_of_mem hx] at h2 ⊢
    nlinarith
  · simp only [indicator_of_notMem hx] at h2 ⊢
    nlinarith

end Carleman
