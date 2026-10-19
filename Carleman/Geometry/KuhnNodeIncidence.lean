module

public import Carleman.Geometry.KuhnReflection

/-! For an actual interior grid node, each coordinate permutation and
vertex position determines exactly one incident finite grid cell. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

theorem cartesianKuhn_origin_eq_of_vertex_eq (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z z' : Fin d → ℤ) (π : Equiv.Perm (Fin d)) (k : Fin (d+1))
    (he : (cartesianKuhnSimplex o δ hδ z π).points k=
      (cartesianKuhnSimplex o δ hδ z' π).points k) : z=z' := by
  funext j
  have h := congrArg (fun x : SpatialCoordinates d => x j) he
  rw [cartesianKuhnSimplex_points,cartesianKuhnSimplex_points] at h
  have hm := (mul_left_inj' (hδ j).ne').mp (add_left_cancel h)
  have hr : (z j:ℝ)=(z' j:ℝ) := add_right_cancel hm
  exact_mod_cast hr

theorem cartesianFiniteSimplex_fixed_vertex_injective (o δ : Fin d → ℝ)
    (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ) (π : Equiv.Perm (Fin d)) (k : Fin (d+1)) :
    Function.Injective (fun b : ∀ j, Fin (N j) => (cartesianFiniteSimplex o δ hδ N (b,π)).points k) := by
  intro b b' he
  have hz := cartesianKuhn_origin_eq_of_vertex_eq o δ hδ _ _ π k he
  funext j
  apply Fin.ext
  have hj := congrFun hz j
  change ((b j).val:ℤ)=((b' j).val:ℤ) at hj
  exact_mod_cast hj

theorem cartesianKuhn_node_incidence_unique (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ)
    (ha : cartesianGridPoint o δ a ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))
    (π : Equiv.Perm (Fin d)) (k : Fin (d+1)) :
    ∃! b : ∀ j, Fin (N j), (cartesianFiniteSimplex o δ hδ N (b,π)).points k=
      cartesianGridPoint o δ a := by
  let z : Fin d → ℤ := fun j => a j-if (π.symm j).val < k.val then 1 else 0
  have hz : kuhnVertexIndex z π k=a := by
    funext j
    simp only [kuhnVertexIndex,z,sub_add_cancel]
  have hv : (cartesianKuhnSimplex o δ hδ z π).points k=cartesianGridPoint o δ a := by
    rw [cartesianKuhnSimplex_points_eq_gridPoint,hz]
  obtain ⟨i,hi⟩ := cartesianKuhn_incident_finite_index o δ hδ N a ha z π ⟨k,hv⟩
  have hidx : cartesianCellLatticeIndex N (i.1,π)=(z,π) := by
    apply Prod.ext
    · have hh := congrArg (fun p : (Fin d → ℤ) × Equiv.Perm (Fin d) => p.1) hi
      exact hh
    · rfl
  have hb : (cartesianFiniteSimplex o δ hδ N (i.1,π)).points k=cartesianGridPoint o δ a := by
    rw [cartesianFiniteSimplex_of_latticeIndex o δ hδ N (i.1,π) z π hidx]
    exact hv
  refine ⟨i.1,hb,?_⟩
  intro b hb'
  exact cartesianFiniteSimplex_fixed_vertex_injective o δ hδ N π k (hb'.trans hb.symm)

theorem cartesianKuhn_node_incidence_sum (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ)
    (ha : cartesianGridPoint o δ a ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))
    (m : Equiv.Perm (Fin d) → ℝ) :
    (∑ i : CartesianCellIndex N, ∑ k : Fin (d+1),
      if (cartesianFiniteSimplex o δ hδ N i).points k=cartesianGridPoint o δ a then m i.2 else 0)=
      ∑ π : Equiv.Perm (Fin d), (d+1:ℝ)*m π := by
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro π _
  rw [Finset.sum_comm]
  have hsum (k : Fin (d+1)) : (∑ b : ∀ j, Fin (N j),
      if (cartesianFiniteSimplex o δ hδ N (b,π)).points k=cartesianGridPoint o δ a
      then m π else 0)=m π := by
    obtain ⟨b,hb,hunique⟩ := cartesianKuhn_node_incidence_unique o δ hδ N a ha π k
    rw [Finset.sum_eq_single b]
    · exact ite_eq_left hb
    · intro b' _ hne
      exact ite_eq_right (fun he => hne (hunique b' he))
    · simp
  simp_rw [hsum]
  simp [nsmul_eq_mul]

end Carleman
