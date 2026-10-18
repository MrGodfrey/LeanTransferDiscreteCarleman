module

public import Carleman.Spatial.SimplicialGlobalDerivative
public import Carleman.Spatial.LipschitzGlobalSobolev

/-! The actual zero extension of the boundary-zero nodal function belongs
to H¹ of the whole Euclidean space. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}
  (M : Carleman.SimplicialPartition S ι)

def nodalGlobalSobolevJet (hS : IsOpen S) (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k) = 0) :
    WeakSobolevJet d 1 volume Set.univ := by
  apply lipschitzGlobalJet (M.nodalFunction_lipschitzWith hS hM hB f hf)
    (M.nodalGlobalLp hS hM hB f hf) (M.nodalGlobalDerivativeLp f) (M.nodalGlobalLp_ae hS hM hB f hf)
  filter_upwards [M.nodalGlobalDerivativeLp_ae f,M.nodalFunction_hasFDerivAt_global_ae hM f] with x hx hd
  rwa [hx]

theorem nodalGlobalSobolevJet_value (hS : IsOpen S) (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k) = 0) :
    WeakSobolevJet.value (M.nodalGlobalSobolevJet hS hM hB f hf) = M.nodalGlobalLp hS hM hB f hf :=
  lipschitzGlobalJet_value _ _ _ _ _

theorem nodalGlobalLp_mem_sobolev (hS : IsOpen S) (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k) = 0) :
    M.nodalGlobalLp hS hM hB f hf ∈ sobolevSubspace d 1 volume Set.univ :=
  ⟨M.nodalGlobalSobolevJet hS hM hB f hf,M.nodalGlobalSobolevJet_value hS hM hB f hf⟩

end Carleman.SimplicialPartition
