module

public import Carleman.Geometry.CartesianKuhnSimplex

/-! The actual union of all Kuhn cells sharing a vertex with a fixed cell is
contained in a fixed Cartesian patch, including boundary vertices. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem cartesianKuhn_shared_vertex_index_bound (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z z' : Fin d → ℤ) (π π' : Equiv.Perm (Fin d)) (k l : Fin (d+1))
    (hp : (cartesianKuhnSimplex o δ hδ z π).points k =
      (cartesianKuhnSimplex o δ hδ z' π').points l) (j : Fin d) :
    z j-1 ≤ z' j ∧ z' j ≤ z j+1 := by
  have he := congrArg (fun x : SpatialCoordinates d => x j) hp
  rw [cartesianKuhnSimplex_points,cartesianKuhnSimplex_points] at he
  have hc : (z j:ℝ)+(if (π.symm j).val < k.val then 1 else 0) =
      (z' j:ℝ)+(if (π'.symm j).val < l.val then 1 else 0) :=
    (mul_left_inj' (hδ j).ne').mp (add_left_cancel he)
  have hb : (z j:ℝ)-1 ≤ (z' j:ℝ) ∧ (z' j:ℝ) ≤ (z j:ℝ)+1 := by
    split_ifs at hc <;> constructor <;> linarith
  exact_mod_cast hb

theorem cartesianKuhn_shared_vertex_cell_subset (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z z' : Fin d → ℤ) (π π' : Equiv.Perm (Fin d)) (k l : Fin (d+1))
    (hp : (cartesianKuhnSimplex o δ hδ z π).points k =
      (cartesianKuhnSimplex o δ hδ z' π').points l) :
    simplicialCell (cartesianKuhnSimplex o δ hδ z' π').points ⊆
      closedCoordinateBox (fun j => o j+((z j:ℝ)-1)*δ j)
        (fun j => o j+((z j:ℝ)+2)*δ j) := by
  intro x hx j
  have hxj := cartesianKuhnSimplex_cell_subset_box o δ hδ z' π' hx j
  have hz := cartesianKuhn_shared_vertex_index_bound o δ hδ z z' π π' k l hp j
  have hl : (z j:ℝ)-1 ≤ (z' j:ℝ) := by exact_mod_cast hz.1
  have hu : (z' j:ℝ) ≤ (z j:ℝ)+1 := by exact_mod_cast hz.2
  have hlow := mul_le_mul_of_nonneg_right hl (hδ j).le
  have hupp := mul_le_mul_of_nonneg_right hu (hδ j).le
  constructor <;> nlinarith [hxj.1,hxj.2]

def cartesianKuhnStarPatch (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) : Set (SpatialCoordinates d) :=
  {x | ∃ (z' : Fin d → ℤ) (π' : Equiv.Perm (Fin d)) (k l : Fin (d+1)),
    (cartesianKuhnSimplex o δ hδ z π).points k =
      (cartesianKuhnSimplex o δ hδ z' π').points l ∧
    x ∈ simplicialCell (cartesianKuhnSimplex o δ hδ z' π').points}

theorem cartesianKuhnStarPatch_subset_patch (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) :
    cartesianKuhnStarPatch o δ hδ z π ⊆ cartesianPatch o δ 2 z := by
  rintro x ⟨z',π',k,l,hp,hx⟩ j
  have hb := cartesianKuhn_shared_vertex_cell_subset o δ hδ z z' π π' k l hp hx j
  change o j+((z j:ℝ)-(2:ℕ))*δ j < x j ∧ x j < o j+((z j:ℝ)+(2:ℕ)+1)*δ j
  constructor <;> norm_num at * <;> linarith [hδ j]

theorem cartesianKuhnStarPatch_multiplicity_le {ι : Type*} [Fintype ι]
    (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (index : ι → (Fin d → ℤ) × Equiv.Perm (Fin d)) (hinj : Function.Injective index)
    (x : SpatialCoordinates d) :
    finiteCoverMultiplicity (fun i => cartesianKuhnStarPatch o δ hδ (index i).1 (index i).2) x ≤
      5^d*d.factorial := by
  simpa using cartesianPatch_permutation_multiplicity_le o δ hδ 2 index hinj
    (fun i => cartesianKuhnStarPatch o δ hδ (index i).1 (index i).2)
    (fun i => cartesianKuhnStarPatch_subset_patch o δ hδ (index i).1 (index i).2) x

theorem cartesianKuhn_cell_subset_starPatch (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) :
    simplicialCell (cartesianKuhnSimplex o δ hδ z π).points ⊆ cartesianKuhnStarPatch o δ hδ z π :=
  fun _ hx => ⟨z,π,0,0,rfl,hx⟩

theorem cartesianKuhnStarPatch_eq_finite_union (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) :
    cartesianKuhnStarPatch o δ hδ z π =
      ⋃ z' ∈ Fintype.piFinset (fun j => Finset.Icc (z j-1) (z j+1)),
        ⋃ π' : Equiv.Perm (Fin d),
          if ∃ k l, (cartesianKuhnSimplex o δ hδ z π).points k =
            (cartesianKuhnSimplex o δ hδ z' π').points l
          then simplicialCell (cartesianKuhnSimplex o δ hδ z' π').points else ∅ := by
  classical
  ext x
  constructor
  · rintro ⟨z',π',k,l,hp,hx⟩
    apply mem_iUnion.mpr
    refine ⟨z',mem_iUnion.mpr ⟨?_,mem_iUnion.mpr ⟨π',?_⟩⟩⟩
    · exact Fintype.mem_piFinset.mpr fun j => Finset.mem_Icc.mpr
        (cartesianKuhn_shared_vertex_index_bound o δ hδ z z' π π' k l hp j)
    · simpa only [ite_eq_left (show ∃ k l, (cartesianKuhnSimplex o δ hδ z π).points k =
        (cartesianKuhnSimplex o δ hδ z' π').points l from ⟨k,l,hp⟩)] using hx
  · intro hx
    rcases mem_iUnion.mp hx with ⟨z',hx⟩
    rcases mem_iUnion.mp hx with ⟨_,hx⟩
    rcases mem_iUnion.mp hx with ⟨π',hx⟩
    split_ifs at hx with hp
    · obtain ⟨k,l,hp⟩ := hp
      exact ⟨z',π',k,l,hp,hx⟩
    · exact False.elim hx

theorem cartesianKuhnStarPatch_compact (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) :
    IsCompact (cartesianKuhnStarPatch o δ hδ z π) := by
  classical
  rw [cartesianKuhnStarPatch_eq_finite_union]
  apply Finset.isCompact_biUnion
  intro z' _
  apply isCompact_iUnion
  intro π'
  split_ifs
  · exact simplicialCell_compact _
  · exact isCompact_empty

theorem cartesianKuhnStarPatch_measurable (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) :
    MeasurableSet (cartesianKuhnStarPatch o δ hδ z π) :=
  (cartesianKuhnStarPatch_compact o δ hδ z π).isClosed.measurableSet

end Carleman
