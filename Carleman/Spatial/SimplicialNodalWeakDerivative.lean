module

public import Carleman.Spatial.SimplicialNodalLipschitz
public import Carleman.Spatial.LipschitzWeakDerivative

/-! The concrete nodal interpolant has the actual piecewise constant gradient
as its distributional derivative in every direction. Boundary-zero data
allow the global Lipschitz zero extension used in the proof. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}
  (M : Carleman.SimplicialPartition S ι) [IsFiniteMeasure (volume.restrict S)]

def nodalDirectionalLp (f : SpatialCoordinates d → ℝ) (e : SpatialCoordinates d) :
    Lp ℝ 2 (volume.restrict S) :=
  (OperatorMultiplier.const (ContinuousLinearMap.apply ℝ ℝ e)).map (M.nodalDerivativeLp f)

theorem nodalDirectionalLp_ae (f : SpatialCoordinates d → ℝ) (e : SpatialCoordinates d) :
    M.nodalDirectionalLp f e =ᵐ[volume.restrict S] (fun x => M.nodalDerivativeFunction f x e) := by
  filter_upwards [OperatorMultiplier.const_map_ae (ContinuousLinearMap.apply ℝ ℝ e)
    (M.nodalDerivativeLp f),M.nodalDerivativeLp_ae f] with x h1 h2
  exact h1.trans (congrArg (fun L : SpatialCoordinates d →L[ℝ] ℝ => L e) h2)

theorem nodalLp_weakDerivative (hS : IsOpen S) (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k) = 0)
    (e : SpatialCoordinates d) :
    IsWeakSpatialDerivative (volume.restrict S) S e
      (M.nodalLp hS.measurableSet hM f) (M.nodalDirectionalLp f e) := by
  apply weakSpatialDerivative_of_lipschitz (M.nodalFunction_lipschitzWith hS hM hB f hf) e
    _ _ (M.nodalLp_ae hS.measurableSet hM f)
  filter_upwards [M.nodalDirectionalLp_ae f e,M.nodalFunction_hasFDerivAt_ae hS.measurableSet hM f] with x hv hx
  exact hv.trans (hx.hasLineDerivAt e).lineDeriv.symm

end Carleman.SimplicialPartition
