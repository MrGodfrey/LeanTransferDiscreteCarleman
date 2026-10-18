module

public import Carleman.Spatial.SimplicialNodalWeakDerivative
public import Carleman.Spatial.FirstOrderSobolevJet

/-! The boundary-zero nodal interpolant belongs to the actual weak H¹
subspace. H¹₀ as a closure of compactly supported smooth functions remains
a further density/zero-trace obligation. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}
  (M : Carleman.SimplicialPartition S ι) [IsFiniteMeasure (volume.restrict S)]

def nodalSobolevJet (hS : IsOpen S) (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k) = 0) :
    WeakSobolevJet d 1 (volume.restrict S) S :=
  firstOrderJet (M.nodalLp hS.measurableSet hM f) (M.nodalDerivativeLp f)
    (fun i => M.nodalLp_weakDerivative hS hM hB f hf (EuclideanSpace.basisFun (Fin d) ℝ i))

theorem nodalSobolevJet_value (hS : IsOpen S) (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k) = 0) :
    WeakSobolevJet.value (M.nodalSobolevJet hS hM hB f hf) = M.nodalLp hS.measurableSet hM f :=
  firstOrderJet_value _ _ _

theorem nodalLp_mem_sobolev (hS : IsOpen S) (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k) = 0) :
    M.nodalLp hS.measurableSet hM f ∈ sobolevSubspace d 1 (volume.restrict S) S :=
  ⟨M.nodalSobolevJet hS hM hB f hf,M.nodalSobolevJet_value hS hM hB f hf⟩

end Carleman.SimplicialPartition
