module

public import Carleman.Spatial.SpacetimeHeatIdentity

/-! Actual separated time-space phases and their derivatives. -/
@[expose] public noncomputable section
open scoped ContDiff BigOperators
namespace Carleman
variable {d : ℕ}

def separableHeatPhase (q : ℝ → ℝ) (f : SpatialCoordinates d → ℝ)
    (tx : ℝ × SpatialCoordinates d) : ℝ := q tx.1*f tx.2

theorem separableHeatPhase_contDiff {q : ℝ → ℝ} {f : SpatialCoordinates d → ℝ}
    (hq : ContDiff ℝ ∞ q) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (separableHeatPhase q f) :=
  (hq.comp contDiff_fst).mul (hf.comp contDiff_snd)

theorem separableHeatPhase_timeD {q : ℝ → ℝ} {f : SpatialCoordinates d → ℝ}
    (hq : ContDiff ℝ ∞ q) (hf : ContDiff ℝ ∞ f) (t : ℝ) (x : SpatialCoordinates d) :
    smoothD (1,0) (separableHeatPhase q f) (t,x)=deriv q t*f x := by
  rw [spaceTime_timeD (separableHeatPhase_contDiff hq hf)]
  exact (((hq.differentiable (by simp) t).hasDerivAt).mul_const (f x)).deriv

theorem separableHeatPhase_spatialD {q : ℝ → ℝ} {f : SpatialCoordinates d → ℝ}
    (hq : ContDiff ℝ ∞ q) (hf : ContDiff ℝ ∞ f) (t : ℝ) (x v : SpatialCoordinates d) :
    smoothD (0,v) (separableHeatPhase q f) (t,x)=q t*smoothD v f x := by
  rw [spaceTime_spatialD (separableHeatPhase_contDiff hq hf)]
  change fderiv ℝ (fun y => q t*f y) x v=_
  rw [fderiv_const_mul (hf.differentiable (by simp) x)]
  rfl

theorem separableHeatPhase_lap {q : ℝ → ℝ} {f : SpatialCoordinates d → ℝ}
    (hq : ContDiff ℝ ∞ q) (hf : ContDiff ℝ ∞ f) (t : ℝ) (x : SpatialCoordinates d) :
    directionalLap spaceTimeSpatialDirection (separableHeatPhase q f) (t,x)=
      q t*directionalLap (EuclideanSpace.basisFun (Fin d) ℝ) f x := by
  have he i : smoothD (spaceTimeSpatialDirection i) (separableHeatPhase q f)=
      separableHeatPhase q (smoothD (EuclideanSpace.basisFun (Fin d) ℝ i) f) :=
    funext fun y => separableHeatPhase_spatialD hq hf y.1 y.2 _
  simp only [directionalLap,he,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact separableHeatPhase_spatialD hq (smoothD_contDiff hf _) t x _

theorem separableHeatPhase_energy {q : ℝ → ℝ} {f : SpatialCoordinates d → ℝ}
    (hq : ContDiff ℝ ∞ q) (hf : ContDiff ℝ ∞ f) (t : ℝ) (x : SpatialCoordinates d) :
    directionalEnergy spaceTimeSpatialDirection (separableHeatPhase q f) (t,x)=
      (q t)^2*directionalEnergy (EuclideanSpace.basisFun (Fin d) ℝ) f x := by
  unfold directionalEnergy
  simp only [spaceTimeSpatialDirection,separableHeatPhase_spatialD hq hf,mul_pow,← Finset.mul_sum]

theorem separableHeatPhase_pair {q r : ℝ → ℝ} {f g : SpatialCoordinates d → ℝ}
    (hq : ContDiff ℝ ∞ q) (hr : ContDiff ℝ ∞ r)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (t : ℝ) (x : SpatialCoordinates d) :
    directionalPair spaceTimeSpatialDirection (separableHeatPhase q f) (separableHeatPhase r g) (t,x)=
      (q t*r t)*directionalPair (EuclideanSpace.basisFun (Fin d) ℝ) f g x := by
  unfold directionalPair
  simp only [spaceTimeSpatialDirection,separableHeatPhase_spatialD hq hf,
    separableHeatPhase_spatialD hr hg,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem directionalPair_add_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (e : ι → E) {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (z : E → ℝ) (x : E) :
    directionalPair e (fun y => f y+g y) z x=directionalPair e f z x+directionalPair e g z x := by
  simp only [directionalPair,smoothD_add hf hg,add_mul,Finset.sum_add_distrib]

theorem directionalPair_const_mul_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (e : ι → E) {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (a : ℝ) (z : E → ℝ) (x : E) :
    directionalPair e (fun y => a*f y) z x=a*directionalPair e f z x := by
  simp only [directionalPair,smoothD_const_mul hf,mul_assoc,← Finset.mul_sum]

end Carleman
