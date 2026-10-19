module

public import Carleman.Weights.InteriorHeatCoefficients

/-! Exact differentiation of the genuine heat B coefficient for the Gaussian phase. -/
@[expose] public noncomputable section
open scoped ContDiff BigOperators
namespace Carleman
variable {d : ℕ}

theorem pointwiseHeatB_lap_cancel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (e : ι → E) (t : E) {L k : E → ℝ}
    (hL : ContDiff ℝ ∞ L) (hk : ContDiff ℝ ∞ k) (r : E → ℝ) (x : E) :
    pointwiseHeatB e t L k (fun y => -directionalLap e L y-r y) x=
      smoothD t k x+2*directionalPair e k L x-2*k x*r x := by
  unfold pointwiseHeatB
  rw [directional_div_product e hk hL]
  ring

theorem interiorGaussianHeatK_timeD (c : SpatialCoordinates d) (l : ℝ)
    {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (t : ℝ) (x : SpatialCoordinates d) :
    smoothD (1,0) (heatConjugationK spaceTimeSpatialDirection (1,0)
      (interiorGaussianHeatPhase c l q) (interiorGaussianHeatPsi c l q)) (t,x)=
      deriv (deriv q) t*interiorCarlemanProfile c l x+
      2*q t*deriv q t*directionalEnergy (EuclideanSpace.basisFun (Fin d) ℝ)
        (interiorCarlemanProfile c l) x+8*l*deriv q t*interiorGaussian c l x := by
  let ρ := interiorCarlemanProfile c l
  let G := directionalEnergy (EuclideanSpace.basisFun (Fin d) ℝ) ρ
  have hρ : ContDiff ℝ ∞ ρ := interiorCarlemanProfile_contDiff c l
  have hG : ContDiff ℝ ∞ G := directionalEnergy_contDiff _ hρ
  have hq' : ContDiff ℝ ∞ (deriv q) := smoothD_contDiff hq 1
  have he : heatConjugationK spaceTimeSpatialDirection (1,0)
      (interiorGaussianHeatPhase c l q) (interiorGaussianHeatPsi c l q)=
      (fun y => separableHeatPhase (deriv q) ρ y+separableHeatPhase (fun s => (q s)^2) G y+
        8*l*separableHeatPhase q (interiorGaussian c l) y) := by
    funext y
    simpa only [separableHeatPhase,ρ,G,mul_assoc] using interiorGaussianHeatK_formula c l hq y.1 y.2
  rw [he,smoothD_add ((separableHeatPhase_contDiff hq' hρ).add
      (separableHeatPhase_contDiff (hq.pow 2) hG))
      (contDiff_const.mul (separableHeatPhase_contDiff hq (interiorGaussian_contDiff c l))),
    smoothD_add (separableHeatPhase_contDiff hq' hρ) (separableHeatPhase_contDiff (hq.pow 2) hG),
    smoothD_const_mul (separableHeatPhase_contDiff hq (interiorGaussian_contDiff c l)),
    separableHeatPhase_timeD hq' hρ,separableHeatPhase_timeD (hq.pow 2) hG,
    separableHeatPhase_timeD hq (interiorGaussian_contDiff c l)]
  have hpow : deriv (fun s => (q s)^2) t=2*q t*deriv q t := by
    convert! (((hq.differentiable (by simp) t).hasDerivAt).pow 2).deriv using 1
    simp
  rw [hpow]
  dsimp only [ρ,G]
  ring

theorem interiorGaussianHeatK_pair (c : SpatialCoordinates d) (l : ℝ)
    {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (t : ℝ) (x : SpatialCoordinates d) :
    directionalPair spaceTimeSpatialDirection
      (heatConjugationK spaceTimeSpatialDirection (1,0)
        (interiorGaussianHeatPhase c l q) (interiorGaussianHeatPsi c l q))
      (interiorGaussianHeatPhase c l q) (t,x)=
      (deriv q t*q t)*directionalEnergy (EuclideanSpace.basisFun (Fin d) ℝ)
        (interiorCarlemanProfile c l) x+
      (q t)^3*directionalPair (EuclideanSpace.basisFun (Fin d) ℝ)
        (directionalEnergy (EuclideanSpace.basisFun (Fin d) ℝ) (interiorCarlemanProfile c l))
        (interiorCarlemanProfile c l) x+
      8*l*(q t)^2*directionalEnergy (EuclideanSpace.basisFun (Fin d) ℝ)
        (interiorCarlemanProfile c l) x := by
  let ρ := interiorCarlemanProfile c l
  let G := directionalEnergy (EuclideanSpace.basisFun (Fin d) ℝ) ρ
  have hρ : ContDiff ℝ ∞ ρ := interiorCarlemanProfile_contDiff c l
  have hG : ContDiff ℝ ∞ G := directionalEnergy_contDiff _ hρ
  have hq' : ContDiff ℝ ∞ (deriv q) := smoothD_contDiff hq 1
  have he : heatConjugationK spaceTimeSpatialDirection (1,0)
      (interiorGaussianHeatPhase c l q) (interiorGaussianHeatPsi c l q)=
      (fun y => separableHeatPhase (deriv q) ρ y+separableHeatPhase (fun s => (q s)^2) G y+
        8*l*separableHeatPhase q (interiorGaussian c l) y) := by
    funext y
    simpa only [separableHeatPhase,ρ,G,mul_assoc] using interiorGaussianHeatK_formula c l hq y.1 y.2
  rw [he,directionalPair_add_left _ ((separableHeatPhase_contDiff hq' hρ).add
      (separableHeatPhase_contDiff (hq.pow 2) hG))
      (contDiff_const.mul (separableHeatPhase_contDiff hq (interiorGaussian_contDiff c l))),
    directionalPair_add_left _ (separableHeatPhase_contDiff hq' hρ)
      (separableHeatPhase_contDiff (hq.pow 2) hG),
    directionalPair_const_mul_left _ (separableHeatPhase_contDiff hq (interiorGaussian_contDiff c l))]
  change directionalPair _ (separableHeatPhase (deriv q) ρ) (separableHeatPhase q ρ) (t,x)+
    directionalPair _ (separableHeatPhase (fun s => (q s)^2) G) (separableHeatPhase q ρ) (t,x)+
    8*l*directionalPair _ (separableHeatPhase q (interiorGaussian c l)) (separableHeatPhase q ρ) (t,x)=_
  rw [separableHeatPhase_pair hq' hq hρ hρ,separableHeatPhase_pair (hq.pow 2) hq hG hρ,
    separableHeatPhase_pair hq hq (interiorGaussian_contDiff c l) hρ,directionalPair_self,
    interiorCarlemanProfile_gaussian_pair]
  dsimp only [ρ,G]
  ring

theorem interiorGaussianHeatB_formula (c : SpatialCoordinates d) (l : ℝ)
    {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (t : ℝ) (x : SpatialCoordinates d) :
    pointwiseHeatB spaceTimeSpatialDirection (1,0) (interiorGaussianHeatPhase c l q)
      (heatConjugationK spaceTimeSpatialDirection (1,0)
        (interiorGaussianHeatPhase c l q) (interiorGaussianHeatPsi c l q))
      (interiorGaussianHeatPsi c l q) (t,x)=
      64*(q t)^3*l^4*(interiorGaussian c l x)^3*‖x-c‖^4-
      96*(q t)^3*l^3*(interiorGaussian c l x)^3*‖x-c‖^2+
      64*(q t)^2*l^3*(interiorGaussian c l x)^2*‖x-c‖^2-
      128*(q t)^2*l^2*(interiorGaussian c l x)^2+
      deriv q t*(16*q t*l^2*(interiorGaussian c l x)^2*‖x-c‖^2+
        8*l*interiorGaussian c l x-
        16*l*q t*interiorGaussian c l x*interiorCarlemanProfile c l x)+
      deriv (deriv q) t*interiorCarlemanProfile c l x := by
  have hL := interiorGaussianHeatPhase_contDiff c l hq
  have hp := interiorGaussianHeatPsi_contDiff c l hq
  change pointwiseHeatB _ _ _ _ (fun y => -directionalLap spaceTimeSpatialDirection
    (interiorGaussianHeatPhase c l q) y-8*l*separableHeatPhase q (interiorGaussian c l) y) (t,x)=_
  rw [pointwiseHeatB_lap_cancel _ _ hL (heatConjugationK_contDiff _ _ hL hp),
    interiorGaussianHeatK_timeD c l hq,interiorGaussianHeatK_pair c l hq,
    interiorGaussianHeatK_formula c l hq,interiorCarlemanProfile_energy,
    interiorCarlemanProfile_energy_pair]
  dsimp only [separableHeatPhase]
  ring

theorem interiorGaussianHeatB_leading (c : SpatialCoordinates d) (l : ℝ)
    {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (t : ℝ) (x : SpatialCoordinates d) :
    pointwiseHeatB spaceTimeSpatialDirection (1,0) (interiorGaussianHeatPhase c l q)
      (heatConjugationK spaceTimeSpatialDirection (1,0)
        (interiorGaussianHeatPhase c l q) (interiorGaussianHeatPsi c l q))
      (interiorGaussianHeatPsi c l q) (t,x)=
      4*(q t)^3*l^3*(interiorGaussian c l x)^3*‖gradient (interiorQuadratic c) x‖^2*
        (l*‖gradient (interiorQuadratic c) x‖^2-6)+
      (q t)^2*(64*l^3*(interiorGaussian c l x)^2*‖x-c‖^2-
        128*l^2*(interiorGaussian c l x)^2)+
      deriv q t*(16*q t*l^2*(interiorGaussian c l x)^2*‖x-c‖^2+
        8*l*interiorGaussian c l x-
        16*l*q t*interiorGaussian c l x*interiorCarlemanProfile c l x)+
      deriv (deriv q) t*interiorCarlemanProfile c l x := by
  rw [interiorGaussianHeatB_formula c l hq,interiorQuadratic_gradient_norm_sq]
  ring

end Carleman
