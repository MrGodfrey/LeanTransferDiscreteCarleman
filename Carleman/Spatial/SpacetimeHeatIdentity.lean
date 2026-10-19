module

public import Carleman.Spatial.PointwiseHeatConjugation
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-! The pointwise identity specialized to the actual space-time heat operator,
with the weighted unknown equal to exp(l) times the original smooth state. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1600000
open scoped ContDiff BigOperators
namespace Carleman
variable {d : ℕ}

def spaceTimeSpatialDirection (i : Fin d) : ℝ × SpatialCoordinates d :=
  (0,EuclideanSpace.basisFun (Fin d) ℝ i)

def spaceTimeHeat (u : (ℝ × SpatialCoordinates d) → ℝ)
    (tx : ℝ × SpatialCoordinates d) : ℝ :=
  deriv (fun s => u (s,tx.2)) tx.1-spatialLaplacian (fun y => u (tx.1,y)) tx.2

theorem spaceTime_timeD {u : (ℝ × SpatialCoordinates d) → ℝ}
    (hu : ContDiff ℝ ∞ u) (t : ℝ) (x : SpatialCoordinates d) :
    smoothD (1,0) u (t,x) = deriv (fun s => u (s,x)) t := by
  have hpath := (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have h := (hu.differentiable (by simp) (t,x)).hasFDerivAt.comp_hasDerivAt t hpath
  exact h.deriv.symm

theorem spaceTime_spatialD {u : (ℝ × SpatialCoordinates d) → ℝ}
    (hu : ContDiff ℝ ∞ u) (t : ℝ) (x v : SpatialCoordinates d) :
    smoothD (0,v) u (t,x) = fderiv ℝ (fun y => u (t,y)) x v := by
  have hpath := (hasFDerivAt_const (𝕜 := ℝ) t x).prodMk (hasFDerivAt_id (𝕜 := ℝ) x)
  have h := (hu.differentiable (by simp) (t,x)).hasFDerivAt.comp x hpath
  convert! (congrArg (fun A : SpatialCoordinates d →L[ℝ] ℝ => A v) h.fderiv).symm using 1

theorem spaceTime_directionalLap {u : (ℝ × SpatialCoordinates d) → ℝ}
    (hu : ContDiff ℝ ∞ u) (t : ℝ) (x : SpatialCoordinates d) :
    directionalLap spaceTimeSpatialDirection u (t,x) =
      spatialLaplacian (fun y => u (t,y)) x := by
  unfold directionalLap spatialLaplacian
  apply Finset.sum_congr rfl
  intro i _
  change smoothD (0,EuclideanSpace.basisFun (Fin d) ℝ i)
    (smoothD (0,EuclideanSpace.basisFun (Fin d) ℝ i) u) (t,x) = _
  rw [spaceTime_spatialD (smoothD_contDiff hu _)]
  have he : (fun y => smoothD (0,EuclideanSpace.basisFun (Fin d) ℝ i) u (t,y)) =
      (fun y => fderiv ℝ (fun z => u (t,z)) y (EuclideanSpace.basisFun (Fin d) ℝ i)) :=
    funext fun y => spaceTime_spatialD hu t y _
  rw [he]

theorem spaceTime_heat_directional {u : (ℝ × SpatialCoordinates d) → ℝ}
    (hu : ContDiff ℝ ∞ u) (tx : ℝ × SpatialCoordinates d) :
    smoothD (1,0) u tx-directionalLap spaceTimeSpatialDirection u tx = spaceTimeHeat u tx := by
  rw [spaceTime_timeD hu tx.1 tx.2,spaceTime_directionalLap hu tx.1 tx.2]
  rfl

theorem spacetime_heat_carleman_identity {l p u : (ℝ × SpatialCoordinates d) → ℝ}
    (hl : ContDiff ℝ ∞ l) (hp : ContDiff ℝ ∞ p) (hu : ContDiff ℝ ∞ u)
    (tx : ℝ × SpatialCoordinates d) :
    let e := spaceTimeSpatialDirection (d := d)
    let t : ℝ × SpatialCoordinates d := (1,0)
    let z := fun y => Real.exp (l y)*u y
    let k := heatConjugationK e t l p
    (Real.exp (l tx)*spaceTimeHeat u tx)^2+
      smoothD t (pointwiseHeatTimeFlux e k z) tx+
      (∑ i, smoothD (e i) (pointwiseHeatFlux e t l k p z i) tx) =
    (directionalLap e z tx+k tx*z tx)^2+
      (smoothD t z tx+2*directionalPair e l z tx-p tx*z tx)^2+
      2*pointwiseHeatMatrixEnergy e l p z tx-2*directionalPair e p z tx*z tx+
        pointwiseHeatB e t l k p tx*(z tx)^2 := by
  dsimp only
  have hcancel : (fun y => Real.exp (-l y)*(Real.exp (l y)*u y)) = u := by
    funext y
    rw [← mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul]
  have h := pointwise_heat_carleman_identity spaceTimeSpatialDirection (1,0)
    hl hp (hl.exp.mul hu) tx
  rw [hcancel,spaceTime_heat_directional hu] at h
  exact h

theorem spacetime_heat_carleman_inequality {l p u : (ℝ × SpatialCoordinates d) → ℝ}
    (hl : ContDiff ℝ ∞ l) (hp : ContDiff ℝ ∞ p) (hu : ContDiff ℝ ∞ u)
    (tx : ℝ × SpatialCoordinates d) :
    let e := spaceTimeSpatialDirection (d := d)
    let t : ℝ × SpatialCoordinates d := (1,0)
    let z := fun y => Real.exp (l y)*u y
    let k := heatConjugationK e t l p
    (directionalLap e z tx+k tx*z tx)^2+
      2*pointwiseHeatMatrixEnergy e l p z tx-2*directionalPair e p z tx*z tx+
        pointwiseHeatB e t l k p tx*(z tx)^2 ≤
    (Real.exp (l tx)*spaceTimeHeat u tx)^2+
      smoothD t (pointwiseHeatTimeFlux e k z) tx+
      (∑ i, smoothD (e i) (pointwiseHeatFlux e t l k p z i) tx) := by
  dsimp only
  have h := spacetime_heat_carleman_identity hl hp hu tx
  dsimp only at h
  rw [h]
  nlinarith [sq_nonneg (smoothD (1,0) (fun y => Real.exp (l y)*u y) tx+
    2*directionalPair spaceTimeSpatialDirection l (fun y => Real.exp (l y)*u y) tx-
    p tx*(Real.exp (l tx)*u tx))]

end Carleman
