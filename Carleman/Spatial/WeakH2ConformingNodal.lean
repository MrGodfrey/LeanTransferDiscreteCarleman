module

public import Carleman.Spatial.H2NodalCellError

/-! Every original weak H²∩H¹₀ state has one genuine conforming nodal
interpolant and one actual H¹₀ error jet, with both local estimates on every
cell. Representatives and boundary data are supplied internally. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}
  (M : Carleman.SimplicialPartition S ι) [IsFiniteMeasure (volume.restrict S)]

theorem exists_weak_h2_conforming_nodal_error
    (hS : IsOpen S) (hc : Convex ℝ S) (hb : Bornology.IsBounded S) (hd : d ≤ 3)
    (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (u : WeakSobolevJet d 2 (volume.restrict S) S)
    (hu : WeakSobolevJet.value u ∈ dirichletSubspace S) :
    ∃ f : SpatialCoordinates d → ℝ, ContinuousOn f (closure S) ∧
      f =ᵐ[volume.restrict S] WeakSobolevJet.value u ∧ (∀ x ∈ frontier S, f x=0) ∧
      M.nodalLp hS.measurableSet hM f ∈ M.conformingSpace (dirichletSubspace S) ∧
      ∃ e : WeakSobolevJet d 1 (volume.restrict S) S, e ∈ dirichletJetSpace S ∧
        WeakSobolevJet.value e=WeakSobolevJet.value u-M.nodalLp hS.measurableSet hM f ∧
        ∀ (i : ι) (a : SpatialCoordinates d) (r D κ : ℝ), 0 < r → 0 ≤ D →
          (Metric.ball a r ⊆ M.cell i) → D ≤ κ*r →
          (∀ x ∈ M.cell i, ∀ y ∈ M.cell i, dist x y ≤ D) →
          ((∫ x in M.cell i, (WeakSobolevJet.value e x)^2) ≤
            16*D^4*(tensorCoordinateBound d 2)^2*(d:ℝ)^2*
              (∫ x in M.cell i, ‖WeakSobolevJet.field 2 u x‖^2)) ∧
          ((∫ x in M.cell i, ‖WeakSobolevJet.field 1 e x‖^2) ≤
            ((2:ℝ)^d*(d:ℝ)+128*κ^2*‖derivativeOneFiber (d := d)‖^2)*D^2*
              (tensorCoordinateBound d 2)^2*(d:ℝ)^2*
                (∫ x in M.cell i, ‖WeakSobolevJet.field 2 u x‖^2)) := by
  obtain ⟨f,hf,hfu,hzero⟩ := WeakSobolevJet.exists_dirichlet_closure_representative hS hc hb hd u hu
  have hz : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k)=0 :=
    fun i k hk => hzero _ hk
  refine ⟨f,hf,hfu,hzero,M.nodalLp_mem_dirichletConformingSpace hS hc hM hB f hz,
    M.nodalH2ErrorJet hS hM hB u f hz,M.nodalH2ErrorJet_mem_dirichlet hS hc hM hB u hu f hz,
    M.nodalH2ErrorJet_value hS hM hB u f hz,?_⟩
  intro i a r D κ hr hD hball hshape hdiam
  exact M.nodalH2ErrorJet_cell_integral_bounds hS hc hb hd hM hB u f hz hf hfu i hr hD hball hshape hdiam

end Carleman.SimplicialPartition
