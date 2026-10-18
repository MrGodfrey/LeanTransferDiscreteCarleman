module

public import Carleman.Spatial.FullConformingNodal
public import Carleman.Spatial.NodalWeightedNorm
public import Carleman.Spatial.SimplicialProductResidual

/-! Identify the actual weak gradient of a full conforming state with its
continuous nodal representative, without assuming a nodal ansatz for the state. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}
  (M : SimplicialPartition S ι) [IsFiniteMeasure (volume.restrict S)]

theorem nodal_representation_weak_gradient (hS : IsOpen S) (hc : Convex ℝ S)
    (hM : M.FaceMatching) (u : WeakSobolevJet d 1 (volume.restrict S) S)
    (f : SpatialCoordinates d → ℝ) (hf : WeakSobolevJet.value u=M.nodalLp hS.measurableSet hM f) :
    WeakSobolevJet.field 1 u =ᵐ[volume.restrict S]
      (fun x => derivativeOneFiber (fderiv ℝ (M.nodalFunction f) x)) := by
  apply M.ae_of_cells hS hc
  intro i
  have hp : ∀ᵐ x ∂volume.restrict S, x ∈ M.cell i → WeakSobolevJet.value u x=M.localNodal f i x := by
    rw [hf]
    filter_upwards [M.nodalLp_ae hS.measurableSet hM f] with x hx
    intro hi
    rw [hx,M.nodalFunction_on_cell hM f i hi]
  have hg := M.gradient_on_cell hS hc u i (M.localNodal f i) hp
  filter_upwards [hg,M.nodalFunction_fderiv_on_cell_ae hM f i] with x hx hy
  rw [hx,hy]

theorem conforming_dirichlet_nodal_with_gradient (hS : IsOpen S) (hc : Convex ℝ S)
    (hM : M.FaceMatching) (u : WeakSobolevJet d 1 (volume.restrict S) S)
    (hu : WeakSobolevJet.value u ∈ M.conformingSpace (dirichletSubspace S)) :
    ∃ f : SpatialCoordinates d → ℝ,
      (∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k)=0) ∧
      WeakSobolevJet.value u=M.nodalLp hS.measurableSet hM f ∧
      WeakSobolevJet.field 1 u =ᵐ[volume.restrict S]
        (fun x => derivativeOneFiber (fderiv ℝ (M.nodalFunction f) x)) := by
  obtain ⟨f,hf,he⟩ := M.conforming_dirichlet_nodal_representation hS hc hM (WeakSobolevJet.value u) hu
  exact ⟨f,hf,he,M.nodal_representation_weak_gradient hS hc hM u f he⟩

theorem weighted_nodal_mem_dirichletConformingSpace (hS : IsOpen S) (hc : Convex ℝ S)
    (hM : M.FaceMatching) (hB : M.BoundaryFitted) (w f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k)=0) :
    M.nodalLp hS.measurableSet hM (fun x => w x*f x) ∈ M.conformingSpace (dirichletSubspace S) := by
  apply M.nodalLp_mem_dirichletConformingSpace hS hc hM hB
  intro i k hk
  rw [hf i k hk,mul_zero]

end Carleman.SimplicialPartition
