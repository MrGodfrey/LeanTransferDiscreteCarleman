module

public import Carleman.Spatial.ConformingLipschitzRepresentative

/-! Converse nodal representation for the original full H¹₀ piecewise affine
space, with genuine shared point values and zero boundary nodes. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem continuous_zeroExtend_zero_compl (hS : IsOpen S) (hc : Convex ℝ S)
    (u : Lp ℝ 2 (volume.restrict S)) (f : SpatialCoordinates d → ℝ) (hf : Continuous f)
    (he : zeroExtendLp hS.measurableSet u =ᵐ[volume] f) : ∀ x ∉ S, f x=0 := by
  have hreg : interior (closure S)=S := by
    by_cases hs : S.Nonempty
    · rw [hc.interior_closure_eq_interior_of_nonempty_interior (hS.interior_eq.symm ▸ hs),hS.interior_eq]
    · rw [Set.not_nonempty_iff_eq_empty.mp hs,closure_empty,interior_empty]
  have hae : f =ᵐ[volume.restrict (closure S)ᶜ] (fun _ => (0:ℝ)) := by
    filter_upwards [he.filter_mono ae_restrict_le,
      (zeroExtendLp_ae hS.measurableSet u).filter_mono ae_restrict_le,
      ae_restrict_mem isClosed_closure.isOpen_compl.measurableSet] with x hx hy hz
    rw [← hx,hy,indicator_of_notMem (fun h => hz (subset_closure h))]
  have hz := Measure.eqOn_open_of_ae_eq hae isClosed_closure.isOpen_compl
    hf.continuousOn continuous_const.continuousOn
  have hh : closure (closure S)ᶜ ⊆ {x | f x=0} :=
    closure_minimal hz (isClosed_eq hf continuous_const)
  rw [closure_compl,hreg] at hh
  exact fun x hx => hh hx

namespace SimplicialPartition
variable {ι : Type*} [Fintype ι] (M : SimplicialPartition S ι)
  [IsFiniteMeasure (volume.restrict S)]

theorem conforming_representative_affine_on_cells (hS : IsOpen S) (hc : Convex ℝ S)
    (V : Submodule ℝ (Lp ℝ 2 (volume.restrict S)))
    (u : WeakSobolevJet d 1 (volume.restrict S) S)
    (hu : WeakSobolevJet.value u ∈ M.conformingSpace V)
    (f : SpatialCoordinates d → ℝ) (hf : Continuous f)
    (he : WeakSobolevJet.value u =ᵐ[volume.restrict S] f) :
    ∀ i, ∃ p : SpatialCoordinates d →ᵃ[ℝ] ℝ, (M.cell i).EqOn f p := by
  intro i
  obtain ⟨p,hp,_⟩ := M.conforming_local_polynomial hS hc V u hu i
  refine ⟨p,Measure.eqOn_of_ae_eq
    ((he.filter_mono (ae_mono (M.cell_measure_le_domain hS hc i))).symm.trans hp)
    hf.continuousOn p.continuous_of_finiteDimensional.continuousOn
    (simplexCell_subset_closure_interior (M.simplex i))⟩

theorem conforming_dirichlet_nodal_representation (hS : IsOpen S) (hc : Convex ℝ S)
    (hM : M.FaceMatching) (z : Lp ℝ 2 (volume.restrict S))
    (hz : z ∈ M.conformingSpace (dirichletSubspace S)) :
    ∃ f : SpatialCoordinates d → ℝ,
      (∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k)=0) ∧
      z=M.nodalLp hS.measurableSet hM f := by
  have hV := ((M.mem_conformingSpace_iff hS.measurableSet (dirichletSubspace S) z).mp hz).1
  obtain ⟨u,hu,he⟩ := hV
  have hp : WeakSobolevJet.value u ∈ M.conformingSpace (dirichletSubspace S) := by rw [he]; exact hz
  obtain ⟨C,f,hf,hfull⟩ := M.conforming_dirichlet_lipschitz_representative hS hc u hu hp
  have hae : WeakSobolevJet.value u =ᵐ[volume.restrict S] f :=
    (zeroExtendLp_ae_restrict hS.measurableSet _).symm.trans (hfull.filter_mono ae_restrict_le)
  have hlocal := M.conforming_representative_affine_on_cells hS hc (dirichletSubspace S) u hp f hf.continuous hae
  have hzero := continuous_zeroExtend_zero_compl hS hc (WeakSobolevJet.value u) f hf.continuous hfull
  refine ⟨f,?_,?_⟩
  · intro i k hk
    apply hzero
    intro hin
    exact hk.2 (hS.interior_eq.symm ▸ hin)
  · rw [← he]
    apply Lp.ext
    filter_upwards [hae,M.nodalLp_ae hS.measurableSet hM f,M.ae_partition hS.measurableSet] with x hx hy hz
    obtain ⟨i,hi,_⟩ := hz
    rw [hx,hy]
    exact (M.nodalFunction_unique hM f f hlocal (fun _ _ => rfl) i hi).symm

end SimplicialPartition
end Carleman
