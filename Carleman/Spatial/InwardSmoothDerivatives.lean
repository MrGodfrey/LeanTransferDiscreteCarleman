module

public import Carleman.Spatial.ScalarAffineL2
public import Carleman.Spatial.TensorCoordinateL2

/-! True iterated Fréchet derivatives under scalar affine precomposition.
The same inward pullback scales every order-k coordinate by r^k. -/
@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
namespace Carleman
variable {d : ℕ}

theorem scalarAffine_iteratedFDeriv {k : ℕ} {f : SpatialCoordinates d → ℝ}
    (hf : ContDiff ℝ k f) (r : ℝ) (b x : SpatialCoordinates d) :
    iteratedFDeriv ℝ k (fun y => f (r • y+b)) x =
      r^k • iteratedFDeriv ℝ k f (r • x+b) := by
  have hgc : ContDiff ℝ k (fun y => f (y+b)) := hf.comp (contDiff_id.add contDiff_const)
  have he := congrFun (iteratedFDeriv_comp_const_smul r hgc) x
  simpa only [iteratedFDeriv_comp_add_right] using he

theorem inwardPullback_contDiff {N : ℕ∞ω} {f : SpatialCoordinates d → ℝ}
    (hf : ContDiff ℝ N f) (a : SpatialCoordinates d) (n : ℕ) :
    ContDiff ℝ N (inwardPullback a n f) :=
  hf.comp ((contDiff_id.const_smul _).add contDiff_const)

theorem coordinateDerivative_inwardPullback {k : ℕ} {f : SpatialCoordinates d → ℝ}
    (hf : ContDiff ℝ k f) (v : Fin k → Fin d) (a : SpatialCoordinates d) (n : ℕ) :
    coordinateDerivative v (inwardPullback a n f) =
      fun x => (inwardRatio n)^k*inwardPullback a n (coordinateDerivative v f) x := by
  funext x
  change coordinateTensorEval v (iteratedFDeriv ℝ k (fun y => f (inwardRatio n • y+(1-inwardRatio n) • a)) x)=_
  rw [scalarAffine_iteratedFDeriv hf,map_smul]
  rfl

end Carleman
