module

public import Carleman.Control.ConformingDirichletState
public import Carleman.Control.P1TensorTestConsistency

/-! The actual full P1 nodal test and its original Dirichlet energy lift. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

namespace SimplicialPartition
variable {ι : Type*} [Fintype ι] [IsFiniteMeasure (volume.restrict S)]

def testGalerkinState (M : SimplicialPartition S ι) (hS : IsOpen S) (hc : Convex ℝ S)
    (hM : M.FaceMatching) (hB : M.BoundaryFitted) (ψ : SpatialTest S) :
    M.conformingSpace (dirichletSubspace S) :=
  ⟨M.nodalLp hS.measurableSet hM ψ.value,
    M.nodalLp_mem_dirichletConformingSpace hS hc hM hB ψ.value (M.test_nodal_zero_boundary hS ψ)⟩

theorem testGalerkinState_value (M : SimplicialPartition S ι) (hS : IsOpen S) (hc : Convex ℝ S)
    (hM : M.FaceMatching) (hB : M.BoundaryFitted) (ψ : SpatialTest S) :
    (M.testGalerkinState hS hc hM hB ψ : Lp ℝ 2 (volume.restrict S))=
      M.nodalLp hS.measurableSet hM ψ.value := rfl

theorem testGalerkinState_lift (M : SimplicialPartition S ι) (hS : IsOpen S) (hc : Convex ℝ S)
    (hd : 0 < d) (hSb : Bornology.IsBounded S)
    (hM : M.FaceMatching) (hB : M.BoundaryFitted) (ψ : SpatialTest S) :
    dirichletGalerkinState hS hd hSb (M.conformingSpace (dirichletSubspace S))
      (M.conformingSpace_le (dirichletSubspace S)) (M.testGalerkinState hS hc hM hB ψ)=
      M.testDirichletState hS hc hM hB ψ := by
  apply conformingEmbed_injective (dirichletSubspace S) hS (ae_restrict_mem hS.measurableSet)
  change dirichletStateValue S _=dirichletStateValue S _
  rw [dirichletGalerkinState_value,testDirichletState_value]
  rfl

theorem testGalerkinState_finite_lift (M : SimplicialPartition S ι)
    (hS : IsOpen S) (hc : Convex ℝ S) (hd : 0 < d) (hSb : Bornology.IsBounded S)
    (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    {L : Type*} [Fintype L] (ψ : L → SpatialTest S) (c : L → ℝ) :
    dirichletGalerkinState hS hd hSb (M.conformingSpace (dirichletSubspace S))
      (M.conformingSpace_le (dirichletSubspace S)) (∑ l, c l • M.testGalerkinState hS hc hM hB (ψ l))=
      ∑ l, c l • M.testDirichletState hS hc hM hB (ψ l) := by
  simp only [map_sum,map_smul,testGalerkinState_lift]

end SimplicialPartition
end Carleman
