module

public import Carleman.Weights.InteriorGaussianDifferential
public import Carleman.Spatial.SeparableHeatPhase
public import Carleman.Spatial.PeriodicHeatFlux

/-! The manuscript's actual time-dependent Gaussian phase, correction, and k coefficient. -/
@[expose] public noncomputable section
open scoped ContDiff BigOperators
namespace Carleman
variable {d : ℕ}

def interiorGaussianHeatPhase (c : SpatialCoordinates d) (l : ℝ) (q : ℝ → ℝ) :
    (ℝ × SpatialCoordinates d) → ℝ :=
  separableHeatPhase q (interiorCarlemanProfile c l)

def interiorGaussianHeatPsi (c : SpatialCoordinates d) (l : ℝ) (q : ℝ → ℝ)
    (tx : ℝ × SpatialCoordinates d) : ℝ :=
  -directionalLap spaceTimeSpatialDirection (interiorGaussianHeatPhase c l q) tx-
    8*l*separableHeatPhase q (interiorGaussian c l) tx

theorem interiorGaussianHeatPhase_contDiff (c : SpatialCoordinates d) (l : ℝ)
    {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (interiorGaussianHeatPhase c l q) :=
  separableHeatPhase_contDiff hq (interiorCarlemanProfile_contDiff c l)

theorem interiorGaussianHeatPsi_contDiff (c : SpatialCoordinates d) (l : ℝ)
    {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (interiorGaussianHeatPsi c l q) :=
  (directionalLap_contDiff _ (interiorGaussianHeatPhase_contDiff c l hq)).neg.sub
    (contDiff_const.mul (separableHeatPhase_contDiff hq (interiorGaussian_contDiff c l)))

theorem interiorGaussianHeatPhase_periodic (c : SpatialCoordinates d) (l : ℝ)
    {q : ℝ → ℝ} {T : ℝ} (hq : Function.Periodic q T) :
    Function.Periodic (interiorGaussianHeatPhase c l q) (T,0) := by
  intro tx
  simp only [interiorGaussianHeatPhase,separableHeatPhase,Prod.fst_add,Prod.snd_add,
    add_zero,hq tx.1]

theorem interiorGaussianHeatPsi_periodic (c : SpatialCoordinates d) (l : ℝ)
    {q : ℝ → ℝ} {T : ℝ} (hq : Function.Periodic q T) :
    Function.Periodic (interiorGaussianHeatPsi c l q) (T,0) := by
  intro tx
  simp only [interiorGaussianHeatPsi,
    directionalLap_periodic _ (interiorGaussianHeatPhase_periodic c l hq) tx,
    separableHeatPhase,Prod.fst_add,Prod.snd_add,add_zero,hq tx.1]

theorem interiorGaussianHeatPsi_formula (c : SpatialCoordinates d) (l : ℝ)
    {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (t : ℝ) (x : SpatialCoordinates d) :
    interiorGaussianHeatPsi c l q (t,x)=
      q t*(-4*l^2*‖x-c‖^2+(2*(d:ℝ)-8)*l)*interiorGaussian c l x := by
  unfold interiorGaussianHeatPsi interiorGaussianHeatPhase
  rw [separableHeatPhase_lap hq (interiorCarlemanProfile_contDiff c l)]
  change -(q t*spatialLaplacian (interiorCarlemanProfile c l) x)-
    8*l*(q t*interiorGaussian c l x)=_
  rw [interiorCarlemanProfile_laplacian]
  ring

theorem interiorGaussianHeatPsi_eq_spatial (c : SpatialCoordinates d) (l : ℝ)
    {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (t : ℝ) (x : SpatialCoordinates d) :
    interiorGaussianHeatPsi c l q (t,x)=interiorHeatPsi c l (q t) x := by
  unfold interiorGaussianHeatPsi interiorHeatPsi
  rw [spaceTime_directionalLap (interiorGaussianHeatPhase_contDiff c l hq)]
  change -spatialLaplacian (fun y => q t*interiorCarlemanProfile c l y) x-
    8*l*(q t*interiorGaussian c l x)=_
  ring

theorem interiorGaussianHeatK_formula (c : SpatialCoordinates d) (l : ℝ)
    {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (t : ℝ) (x : SpatialCoordinates d) :
    heatConjugationK spaceTimeSpatialDirection (1,0) (interiorGaussianHeatPhase c l q)
      (interiorGaussianHeatPsi c l q) (t,x)=
      deriv q t*interiorCarlemanProfile c l x+
      (q t)^2*directionalEnergy (EuclideanSpace.basisFun (Fin d) ℝ) (interiorCarlemanProfile c l) x+
      8*l*q t*interiorGaussian c l x := by
  unfold heatConjugationK interiorGaussianHeatPsi interiorGaussianHeatPhase
  rw [separableHeatPhase_timeD hq (interiorCarlemanProfile_contDiff c l),
    separableHeatPhase_energy hq (interiorCarlemanProfile_contDiff c l)]
  dsimp only [separableHeatPhase]
  ring

theorem interiorGaussianHeatK_explicit (c : SpatialCoordinates d) (l : ℝ)
    {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (t : ℝ) (x : SpatialCoordinates d) :
    heatConjugationK spaceTimeSpatialDirection (1,0) (interiorGaussianHeatPhase c l q)
      (interiorGaussianHeatPsi c l q) (t,x)=
      deriv q t*interiorCarlemanProfile c l x+
      4*(q t)^2*l^2*(interiorGaussian c l x)^2*‖x-c‖^2+
      8*l*q t*interiorGaussian c l x := by
  rw [interiorGaussianHeatK_formula c l hq,interiorCarlemanProfile_energy]
  ring

theorem interiorGaussianHeatPsi_spatialD (c : SpatialCoordinates d) (l : ℝ)
    {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (t : ℝ) (x v : SpatialCoordinates d) :
    smoothD (0,v) (interiorGaussianHeatPsi c l q) (t,x)=
      q t*(8*l^3*‖x-c‖^2+(8-4*(d:ℝ))*l^2)*interiorGaussian c l x*inner ℝ (x-c) v := by
  rw [spaceTime_spatialD (interiorGaussianHeatPsi_contDiff c l hq)]
  have he : (fun y => interiorGaussianHeatPsi c l q (t,y))=
      (fun y => q t*(-4*l^2*‖y-c‖^2+(2*(d:ℝ)-8)*l)*interiorGaussian c l y) :=
    funext (interiorGaussianHeatPsi_formula c l hq t)
  rw [he]
  have h := ((((((hasFDerivAt_id x).sub_const c).norm_sq).const_mul (-4*l^2)).add_const
    ((2*(d:ℝ)-8)*l)).const_mul (q t)).mul (interiorGaussian_hasFDerivAt c l x)
  have hh := congrArg (fun A : SpatialCoordinates d →L[ℝ] ℝ => A v) h.fderiv
  convert! hh using 1
  simp only [add_apply,smul_apply,smul_eq_mul,innerSL_apply_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,id_eq]
  ring

theorem interiorGaussianHeatPsi_energy (c : SpatialCoordinates d) (l : ℝ)
    {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (t : ℝ) (x : SpatialCoordinates d) :
    directionalEnergy spaceTimeSpatialDirection (interiorGaussianHeatPsi c l q) (t,x)=
      (q t)^2*(8*l^3*‖x-c‖^2+(8-4*(d:ℝ))*l^2)^2*
        (interiorGaussian c l x)^2*‖x-c‖^2 := by
  have he i : (smoothD (spaceTimeSpatialDirection i) (interiorGaussianHeatPsi c l q) (t,x))^2=
      ((q t)^2*(8*l^3*‖x-c‖^2+(8-4*(d:ℝ))*l^2)^2*(interiorGaussian c l x)^2)*((x-c) i)^2 := by
    change (smoothD (0,EuclideanSpace.basisFun (Fin d) ℝ i) _ (t,x))^2=_
    rw [interiorGaussianHeatPsi_spatialD c l hq,EuclideanSpace.inner_basisFun_real]
    ring
  simp only [directionalEnergy,he,← Finset.mul_sum,← EuclideanSpace.real_norm_sq_eq]

end Carleman
