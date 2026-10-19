module

public import Carleman.Geometry.KuhnLatticeCoordinates
public import Carleman.Spatial.SimplicialNodalGluing

/-! The actual Cartesian Kuhn cells meet in the convex hull of their common
vertices. This supplies face matching to the existing continuous P1 gluing. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

theorem cartesianKuhn_gridPoint_is_vertex (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) (a : Fin d → ℤ)
    (hx : cartesianGridPoint o δ a ∈ simplicialCell (cartesianKuhnSimplex o δ hδ z π).points) :
    cartesianGridPoint o δ a ∈ Set.range (cartesianKuhnSimplex o δ hδ z π).points := by
  have hp : ∃ k, 0 < simplexBarycentric (cartesianKuhnSimplex o δ hδ z π) k
      (cartesianGridPoint o δ a) := by
    by_contra hn
    push Not at hn
    have hsum := Finset.sum_nonpos (fun k (_ : k ∈ Finset.univ) => hn k)
    rw [simplexBarycentric_sum] at hsum
    norm_num at hsum
  obtain ⟨k,hk⟩ := hp
  have he : kuhnVertexIndex z π k=a := by
    funext j
    apply le_antisymm
    · exact cartesianKuhn_positive_vertex_upper o δ hδ z π hx k hk j (a j)
        (le_of_eq (cartesianGridCoordinate_point o δ hδ a j))
    · exact cartesianKuhn_positive_vertex_lower o δ hδ z π hx k hk j (a j)
        (le_of_eq (cartesianGridCoordinate_point o δ hδ a j).symm)
  refine ⟨k,?_⟩
  rw [cartesianKuhnSimplex_points_eq_gridPoint,he]

theorem cartesianKuhn_positive_vertex_mem_other (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z z' : Fin d → ℤ) (π π' : Equiv.Perm (Fin d)) {x : SpatialCoordinates d}
    (hx : x ∈ simplicialCell (cartesianKuhnSimplex o δ hδ z π).points)
    (hx' : x ∈ simplicialCell (cartesianKuhnSimplex o δ hδ z' π').points)
    (k : Fin (d+1)) (hk : 0 < simplexBarycentric (cartesianKuhnSimplex o δ hδ z π) k x) :
    (cartesianKuhnSimplex o δ hδ z π).points k ∈
      simplicialCell (cartesianKuhnSimplex o δ hδ z' π').points := by
  have hother := (cartesianKuhnSimplex_mem_iff o δ hδ z' π' x).mp hx'
  apply (cartesianKuhnSimplex_mem_iff o δ hδ z' π' _).mpr
  simp_rw [← cartesianGridCoordinate_apply,cartesianGridCoordinate_vertex o δ hδ]
  constructor
  · intro j
    have hlo : (z' j:ℝ) ≤ cartesianGridCoordinate o δ j x := by
      rw [cartesianGridCoordinate_apply]
      linarith [(hother.1 j).1]
    have hup : cartesianGridCoordinate o δ j x ≤ ((z' j+1:ℤ):ℝ) := by
      rw [cartesianGridCoordinate_apply]
      push_cast
      linarith [(hother.1 j).2]
    have hl := cartesianKuhn_positive_vertex_lower o δ hδ z π hx k hk j (z' j) hlo
    have hu := cartesianKuhn_positive_vertex_upper o δ hδ z π hx k hk j (z' j+1) hup
    have hlr : (z' j:ℝ) ≤ (kuhnVertexIndex z π k j:ℝ) := by exact_mod_cast hl
    have hur : (kuhnVertexIndex z π k j:ℝ) ≤ (z' j:ℝ)+1 := by exact_mod_cast hu
    constructor <;> linarith
  · intro i j hij
    have hb : cartesianGridCoordinate o δ (π' j) x-cartesianGridCoordinate o δ (π' i) x ≤
        ((z' (π' j)-z' (π' i):ℤ):ℝ) := by
      simp only [cartesianGridCoordinate_apply,Int.cast_sub]
      linarith [hother.2 hij]
    have hh := cartesianKuhn_positive_vertex_difference o δ hδ z π hx k hk
      (π' j) (π' i) (z' (π' j)-z' (π' i)) hb
    have hr : (kuhnVertexIndex z π k (π' j):ℝ)-(kuhnVertexIndex z π k (π' i):ℝ) ≤
        (z' (π' j):ℝ)-(z' (π' i):ℝ) := by exact_mod_cast hh
    linarith

theorem cartesianKuhn_cells_common_face (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z z' : Fin d → ℤ) (π π' : Equiv.Perm (Fin d)) :
    simplicialCell (cartesianKuhnSimplex o δ hδ z π).points ∩
      simplicialCell (cartesianKuhnSimplex o δ hδ z' π').points ⊆
      convexHull ℝ (Set.range (cartesianKuhnSimplex o δ hδ z π).points ∩
        Set.range (cartesianKuhnSimplex o δ hδ z' π').points) := by
  rintro x ⟨hx,hx'⟩
  apply simplex_mem_convexHull_positive_support _ hx
  intro k hk
  refine ⟨Set.mem_range_self k,?_⟩
  have hm := cartesianKuhn_positive_vertex_mem_other o δ hδ z z' π π' hx hx' k hk
  rw [cartesianKuhnSimplex_points_eq_gridPoint] at hm ⊢
  exact cartesianKuhn_gridPoint_is_vertex o δ hδ z' π' _ hm

def cartesianKuhnPartition (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ) :
    SimplicialPartition (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))
      (CartesianCellIndex N) where
  simplex := cartesianFiniteSimplex o δ hδ N
  inside := by
    intro i x hx
    have hN (j : Fin d) : 0 < (N j:ℝ) := by
      have hi := (i.1 j).isLt
      have hn : 0 < N j := by omega
      exact_mod_cast hn
    rw [closure_openCoordinateBox o _ (fun j => by linarith [mul_pos (hN j) (hδ j)])]
    have hb := cartesianKuhnSimplex_cell_subset_box o δ hδ
      (cartesianCellLatticeIndex N i).1 i.2 hx
    intro j
    have hl : (0:ℝ) ≤ ((i.1 j).val:ℝ) := Nat.cast_nonneg _
    have hu : ((i.1 j).val:ℝ)+1 ≤ (N j:ℝ) := by exact_mod_cast (i.1 j).isLt
    have hm := mul_le_mul_of_nonneg_right hu (hδ j).le
    have hp := mul_nonneg hl (hδ j).le
    have hbj := hb j
    change o j+((i.1 j).val:ℝ)*δ j ≤ x j ∧
      x j ≤ o j+(((i.1 j).val:ℝ)+1)*δ j at hbj
    constructor <;> linarith
  cover := cartesianFiniteSimplex_cover o δ hδ N
  disjoint := cartesianFiniteSimplex_interiors_disjoint o δ hδ N

theorem cartesianKuhnPartition_faceMatching (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) : (cartesianKuhnPartition o δ hδ N).FaceMatching := by
  intro i j
  exact cartesianKuhn_cells_common_face o δ hδ _ _ i.2 j.2

end Carleman
