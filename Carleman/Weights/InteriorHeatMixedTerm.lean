module

public import Carleman.Spatial.DirectionalYoung
public import Carleman.Weights.InteriorHeatCoefficients

/-! Uniform mixed-term control for the actual Gaussian auxiliary coefficient. -/
@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace Carleman
variable {d : ℕ}

theorem interiorGaussianHeatPsi_uniform_energy_bound {S : Set (SpatialCoordinates d)}
    (hS : Bornology.IsBounded S) (c : SpatialCoordinates d) {l : ℝ} (hl : 0 < l) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ → ℝ, ContDiff ℝ ∞ q →
      ∀ t : ℝ, 1 ≤ q t → ∀ x ∈ S,
      directionalEnergy spaceTimeSpatialDirection (interiorGaussianHeatPsi c l q) (t,x) ≤
        (C*(q t)^2)*(q t*l*interiorGaussian c l x) := by
  let P : SpatialCoordinates d → ℝ := fun x => 8*l^3*‖x-c‖^2+(8-4*(d:ℝ))*l^2
  let H : SpatialCoordinates d → ℝ := fun x => interiorGaussian c l x*(P x)^2*‖x-c‖^2/l
  have hφ := (interiorGaussian_contDiff c l).continuous
  have hP : Continuous P := by fun_prop
  have hH : Continuous H := by fun_prop
  obtain ⟨K,hK⟩ := hS.isCompact_closure.exists_bound_of_continuousOn hH.continuousOn
  let C := |K|+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro q hq t ht x hx
  have hb : H x ≤ C := by
    have hh := hK x (subset_closure hx)
    rw [Real.norm_eq_abs] at hh
    dsimp only [C]
    linarith [le_abs_self (H x),le_abs_self K]
  have he : directionalEnergy spaceTimeSpatialDirection (interiorGaussianHeatPsi c l q) (t,x)=
      (q t)^2*l*interiorGaussian c l x*H x := by
    rw [interiorGaussianHeatPsi_energy c l hq]
    dsimp only [H,P]
    field_simp
  rw [he]
  have hq0 : 0 ≤ q t := by linarith
  have hφ0 := (interiorGaussian_pos c l x).le
  have h1 := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ (q t)^2*l*interiorGaussian c l x by positivity)
  have h2 := mul_nonneg (show 0 ≤ C*(q t)^2*l*interiorGaussian c l x by positivity)
    (sub_nonneg.mpr ht)
  nlinarith

theorem interiorGaussianHeat_mixed_term_bound {S : Set (SpatialCoordinates d)}
    (hS : Bornology.IsBounded S) (c : SpatialCoordinates d) {l : ℝ} (hl : 0 < l) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ → ℝ, ContDiff ℝ ∞ q →
      ∀ z : (ℝ × SpatialCoordinates d) → ℝ, ∀ t : ℝ, 1 ≤ q t → ∀ x ∈ S,
      2*directionalPair spaceTimeSpatialDirection (interiorGaussianHeatPsi c l q) z (t,x)*z (t,x) ≤
        q t*l*interiorGaussian c l x*directionalEnergy spaceTimeSpatialDirection z (t,x)+
          C*(q t)^2*(z (t,x))^2 := by
  obtain ⟨C,hC,hbound⟩ := interiorGaussianHeatPsi_uniform_energy_bound hS c hl
  refine ⟨C,hC,?_⟩
  intro q hq z t ht x hx
  have hq0 : 0 < q t := by linarith
  exact directionalPair_young _ _ _ _ (by positivity [interiorGaussian_pos c l x])
    (hbound q hq t ht x hx)

end Carleman
