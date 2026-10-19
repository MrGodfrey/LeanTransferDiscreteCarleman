module

public import Carleman.Weights.InteriorHeatMatrixEnergy
public import Carleman.Weights.InteriorHeatBLowerBound
public import Carleman.Weights.InteriorHeatMixedTerm
public import Carleman.Spatial.HeatIdentityRegularity

/-! A lower bound for the actual heat bulk expression, with all coefficients internal. -/
@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace Carleman
variable {d : ℕ}

theorem interiorGaussianHeat_bulk_lower_bound {S : Set (SpatialCoordinates d)}
    (hS : Bornology.IsBounded S) (c : SpatialCoordinates d) {l : ℝ} (hl : 0 < l) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ → ℝ, ContDiff ℝ ∞ q → ∀ β : ℝ, 0 ≤ β →
      ∀ z : (ℝ × SpatialCoordinates d) → ℝ, ∀ t : ℝ, 1 ≤ q t →
      |deriv q t| ≤ β*(q t)^2 → |deriv (deriv q) t| ≤ β^2*(q t)^3 → ∀ x ∈ S,
      let L := interiorGaussianHeatPhase c l q
      let p := interiorGaussianHeatPsi c l q
      let k := heatConjugationK spaceTimeSpatialDirection (1,0) L p
      4*q t*l*interiorGaussian c l x*directionalEnergy spaceTimeSpatialDirection z (t,x)+
        interiorHeatLeadingCoefficient c l (q t) x*(z (t,x))^2 ≤
      heatCarlemanBulk spaceTimeSpatialDirection (1,0) L k p z (t,x)+
        C*((q t)^2+(β+β^2)*(q t)^3)*(z (t,x))^2 := by
  obtain ⟨C₁,hC₁,hB⟩ := interiorGaussianHeatB_uniform_lower_bound hS c l
  obtain ⟨C₂,hC₂,hmixed⟩ := interiorGaussianHeat_mixed_term_bound hS c hl
  refine ⟨C₁+C₂,by positivity,?_⟩
  intro q hq β hβ z t ht hq₁ hq₂ x hx
  dsimp only
  have hq0 : 0 ≤ q t := by linarith
  have hmatrix := interiorGaussianHeatMatrixEnergy_coercive c l hq z t hq0 x
  have hmix := hmixed q hq z t ht x hx
  have hb := mul_le_mul_of_nonneg_right (hB q hq β hβ t ht hq₁ hq₂ x hx) (sq_nonneg (z (t,x)))
  have henergy : 0 ≤ q t*l*interiorGaussian c l x*directionalEnergy spaceTimeSpatialDirection z (t,x) :=
    mul_nonneg (by positivity [interiorGaussian_pos c l x]) (directionalEnergy_nonneg _ _ _)
  have hrest : 0 ≤ C₂*(β+β^2)*(q t)^3*(z (t,x))^2 := by positivity
  unfold heatCarlemanBulk
  nlinarith [sq_nonneg (directionalLap spaceTimeSpatialDirection z (t,x)+
    heatConjugationK spaceTimeSpatialDirection (1,0) (interiorGaussianHeatPhase c l q)
      (interiorGaussianHeatPsi c l q) (t,x)*z (t,x))]

end Carleman
