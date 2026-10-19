module

public import Carleman.Spatial.HeatGradientReturn
public import Carleman.Weights.InteriorHeatCoefficients

/-! A spatially uniform return estimate for the manuscript's actual Gaussian phase. -/
@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace Carleman
variable {d : ℕ}

theorem spatial_directionalEnergy_gradient (f : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d) :
    directionalEnergy (EuclideanSpace.basisFun (Fin d) ℝ) f x=‖gradient f x‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  unfold directionalEnergy
  apply Finset.sum_congr rfl
  intro i _
  rw [smoothD,← inner_gradient_left,EuclideanSpace.inner_basisFun_real]

theorem spaceTime_directionalEnergy_gradient {u : (ℝ × SpatialCoordinates d) → ℝ}
    (hu : ContDiff ℝ ∞ u) (t : ℝ) (x : SpatialCoordinates d) :
    directionalEnergy spaceTimeSpatialDirection u (t,x)=‖gradient (fun y => u (t,y)) x‖^2 := by
  rw [← spatial_directionalEnergy_gradient]
  unfold directionalEnergy
  apply Finset.sum_congr rfl
  intro i _
  rw [spaceTimeSpatialDirection,spaceTime_spatialD hu]
  rfl

theorem interiorGaussianHeatPhase_uniform_energy {S : Set (SpatialCoordinates d)}
    (hS : Bornology.IsBounded S) (c : SpatialCoordinates d) (l : ℝ) :
    ∃ J : ℝ, 0 < J ∧ ∀ q : ℝ → ℝ, ContDiff ℝ ∞ q → ∀ t : ℝ, ∀ x ∈ S,
      directionalEnergy spaceTimeSpatialDirection (interiorGaussianHeatPhase c l q) (t,x) ≤ J*(q t)^2 := by
  let G := directionalEnergy (EuclideanSpace.basisFun (Fin d) ℝ) (interiorCarlemanProfile c l)
  have hG : Continuous G :=
    (directionalEnergy_contDiff _ (interiorCarlemanProfile_contDiff c l)).continuous
  obtain ⟨D,hD⟩ := hS.isCompact_closure.exists_bound_of_continuousOn hG.continuousOn
  let J := |D|+1
  refine ⟨J,by dsimp only [J]; positivity,?_⟩
  intro q hq t x hx
  have hb : G x ≤ J := by
    have hh := hD x (subset_closure hx)
    rw [Real.norm_eq_abs] at hh
    dsimp only [J]
    linarith [le_abs_self (G x),le_abs_self D]
  change directionalEnergy spaceTimeSpatialDirection (separableHeatPhase q (interiorCarlemanProfile c l)) (t,x) ≤ _
  rw [separableHeatPhase_energy hq (interiorCarlemanProfile_contDiff c l)]
  have hh := mul_le_mul_of_nonneg_left hb (sq_nonneg (q t))
  dsimp only [G] at hh
  nlinarith

theorem interiorGaussianHeat_return_bound {S : Set (SpatialCoordinates d)}
    (hS : Bornology.IsBounded S) (c : SpatialCoordinates d) (l : ℝ) :
    ∃ H : ℝ, 0 < H ∧ ∀ q : ℝ → ℝ, ContDiff ℝ ∞ q →
      ∀ u : (ℝ × SpatialCoordinates d) → ℝ, ContDiff ℝ ∞ u →
      ∀ t : ℝ, 0 ≤ q t → ∀ x ∈ S,
      let L := interiorGaussianHeatPhase c l q
      let z := fun tx => Real.exp (L tx)*u tx
      (q t)^3*(Real.exp (L (t,x)))^2*(u (t,x))^2+
        q t*(Real.exp (L (t,x)))^2*directionalEnergy spaceTimeSpatialDirection u (t,x) ≤
      H*(q t*directionalEnergy spaceTimeSpatialDirection z (t,x)+(q t)^3*(z (t,x))^2) := by
  obtain ⟨J,hJ,hbound⟩ := interiorGaussianHeatPhase_uniform_energy hS c l
  refine ⟨3+2*J,by positivity,?_⟩
  intro q hq u hu t ht x hx
  dsimp only
  let L := interiorGaussianHeatPhase c l q
  let z := fun tx => Real.exp (L tx)*u tx
  have hg := mul_le_mul_of_nonneg_left
    (heat_gradient_return spaceTimeSpatialDirection (interiorGaussianHeatPhase_contDiff c l hq) hu (t,x)) ht
  have he := mul_le_mul_of_nonneg_right (hbound q hq t x hx)
    (show 0 ≤ 2*q t*(z (t,x))^2 by positivity)
  have hE := directionalEnergy_nonneg spaceTimeSpatialDirection z (t,x)
  have hV : (z (t,x))^2=(Real.exp (L (t,x)))^2*(u (t,x))^2 := by dsimp only [z]; ring
  have hn : 0 ≤ (1+2*J)*q t*directionalEnergy spaceTimeSpatialDirection z (t,x) := by positivity
  have hv0 : 0 ≤ (q t)^3*(z (t,x))^2 := by positivity
  change (q t)^3*(Real.exp (L (t,x)))^2*(u (t,x))^2+
    q t*(Real.exp (L (t,x)))^2*directionalEnergy spaceTimeSpatialDirection u (t,x) ≤ _
  change q t*((Real.exp (L (t,x)))^2*directionalEnergy spaceTimeSpatialDirection u (t,x)) ≤
    q t*(2*directionalEnergy spaceTimeSpatialDirection z (t,x)+
      2*directionalEnergy spaceTimeSpatialDirection L (t,x)*(z (t,x))^2) at hg
  nlinarith [hg,he]

end Carleman
