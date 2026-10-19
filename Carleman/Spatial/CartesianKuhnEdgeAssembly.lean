module

public import Carleman.Spatial.CartesianLatticeDifferences
public import Carleman.Geometry.KuhnCellVolume

/-! Exact coordinate-edge assembly. Finite zero-boundary shifts remove the
permutation-dependent prefix, and the true sum of permutation volumes supplies
the physical grid weight. No equal-volume or edge-count assumption is added. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

theorem cartesianKuhn_step_sum (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f g : CartesianInteriorIndex N → ℝ)
    (π : Equiv.Perm (Fin d)) (k : Fin d) :
    (∑ z : ∀ j, Fin (N j), cartesianKuhnCellDifference o δ hδ N f (z,π) k*
      cartesianKuhnCellDifference o δ hδ N g (z,π) k)=
    ∑ z : ∀ j, Fin (N j), cartesianAxisDifference o δ N f (fun j => ((z j).val:ℤ)) (π k)*
      cartesianAxisDifference o δ N g (fun j => ((z j).val:ℤ)) (π k) := by
  classical
  let J := Finset.univ.filter (fun j : Fin d => (π.symm j).val < k.val)
  let F : (Fin d → ℤ) → ℝ := fun z => cartesianAxisDifference o δ N f z (π k)*cartesianAxisDifference o δ N g z (π k)
  have hF : ∀ j ∈ J, ∀ z : Fin d → ℤ, z j=0 ∨ z j=(N j:ℤ) → F z=0 := by
    intro j hj z hz
    have hn : j ≠ π k := by
      intro he
      have ht := (Finset.mem_filter.mp hj).2
      rw [he,Equiv.symm_apply_apply] at ht
      exact (lt_irrefl _) ht
    exact mul_eq_zero_of_left (cartesianAxisDifference_zero_transverse o δ hδ N f z j (π k) hn hz) _
  have he := cartesian_sum_face_zero_shift N J F hF
  have hv (z : ∀ j, Fin (N j)) : kuhnVertexIndex (fun j => ((z j).val:ℤ)) π k.castSucc=
      (fun j => ((z j).val:ℤ)+if j ∈ J then 1 else 0) := by
    funext j
    simp only [kuhnVertexIndex,Fin.val_castSucc,J,Finset.mem_filter,Finset.mem_univ,true_and]
  simp only [cartesianKuhnCellDifference_eq_axis,cartesianCellLatticeIndex]
  simp_rw [hv]
  exact he

theorem cartesianKuhn_permutation_step_sum (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f g : CartesianInteriorIndex N → ℝ) (π : Equiv.Perm (Fin d)) :
    (∑ z : ∀ j, Fin (N j), ∑ k : Fin d, cartesianKuhnCellDifference o δ hδ N f (z,π) k*
      cartesianKuhnCellDifference o δ hδ N g (z,π) k)=
    ∑ z : ∀ j, Fin (N j), ∑ r : Fin d, cartesianAxisDifference o δ N f (fun j => ((z j).val:ℤ)) r*
      cartesianAxisDifference o δ N g (fun j => ((z j).val:ℤ)) r := by
  rw [Finset.sum_comm]
  simp_rw [cartesianKuhn_step_sum o δ hδ N f g π]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  exact Equiv.sum_comp π (fun r => cartesianAxisDifference o δ N f (fun j => ((z j).val:ℤ)) r*
    cartesianAxisDifference o δ N g (fun j => ((z j).val:ℤ)) r)

theorem cartesianKuhnReconstruction_weakGradientPairing_edges (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f g : CartesianInteriorIndex N → ℝ) :
    weakGradientPairing (cartesianKuhnReconstructionJet o δ hδ N f) (cartesianKuhnReconstructionJet o δ hδ N g)=
      (∏ j, δ j)*∑ z : ∀ j, Fin (N j), ∑ r : Fin d,
        cartesianAxisDifference o δ N f (fun j => ((z j).val:ℤ)) r*
        cartesianAxisDifference o δ N g (fun j => ((z j).val:ℤ)) r := by
  rw [cartesianKuhnReconstruction_weakGradientPairing_cells]
  simp only [CartesianCellIndex,Fintype.sum_prod_type,cartesianFiniteSimplex,
    cartesianKuhnSimplex_volume_translation]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,cartesianKuhn_permutation_step_sum o δ hδ N f g]
  rw [← Finset.sum_mul,cartesianKuhnSimplex_sum_permutation_volume]

theorem cartesianKuhnReconstruction_scalarForm_edges (hd : 0 < d)
    (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (f g : CartesianInteriorIndex N → ℝ) :
    (boundedDirichletOriginalForm (openCoordinateBox_isOpen _ _) hd
      (openCoordinateBox_isBounded o (fun j => o j+(N j:ℝ)*δ j))).scalarForm
      ⟨cartesianKuhnReconstructionLp o δ hδ N f,cartesianKuhnReconstructionLp_mem_dirichlet o δ hδ N f⟩
      ⟨cartesianKuhnReconstructionLp o δ hδ N g,cartesianKuhnReconstructionLp_mem_dirichlet o δ hδ N g⟩=
      (∏ j, δ j)*∑ z : ∀ j, Fin (N j), ∑ r : Fin d,
        cartesianAxisDifference o δ N f (fun j => ((z j).val:ℤ)) r*
        cartesianAxisDifference o δ N g (fun j => ((z j).val:ℤ)) r := by
  refine (dirichlet_scalarForm_eq (openCoordinateBox_isOpen _ _) hd (openCoordinateBox_isBounded _ _) _ _
    (cartesianKuhnReconstructionJet o δ hδ N f) (cartesianKuhnReconstructionJet o δ hδ N g)
    (cartesianKuhnReconstructionJet_value o δ hδ N f) (cartesianKuhnReconstructionJet_value o δ hδ N g)).trans ?_
  exact cartesianKuhnReconstruction_weakGradientPairing_edges o δ hδ N f g

end Carleman
