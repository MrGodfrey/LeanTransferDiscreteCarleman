module

public import Carleman.Geometry.KuhnOrderedCell
public import Mathlib.Order.Interval.Finset.Fin

/-! Coordinate rounding inside a Kuhn simplex selects one of that same simplex's vertices. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem antitone_threshold_cut (a : Fin d → ℝ) (ha : Antitone a) (c : ℝ) :
    ∃ k : Fin (d+1), ∀ j : Fin d, j.val < k.val ↔ c < a j := by
  classical
  let s := Finset.univ.filter (fun j => c < a j)
  have hs : s.card ≤ d := by
    have hh : s ⊆ (Finset.univ : Finset (Fin d)) := Finset.filter_subset _ _
    simpa using Finset.card_le_card hh
  let k : Fin (d+1) := ⟨s.card,by omega⟩
  refine ⟨k,?_⟩
  intro j
  change j.val < s.card ↔ c < a j
  constructor
  · intro hj
    by_contra hn
    have hsub : s ⊆ Finset.Iio j := by
      intro i hi
      have hci : c < a i := (Finset.mem_filter.mp hi).2
      apply Finset.mem_Iio.mpr
      by_contra hij
      have he := ha (le_of_not_gt hij)
      linarith
    have he := Finset.card_le_card hsub
    rw [Fin.card_Iio] at he
    omega
  · intro hj
    have hsub : Finset.Iic j ⊆ s := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj.trans_le (ha (Finset.mem_Iic.mp hi))⟩
    have he := Finset.card_le_card hsub
    rw [Fin.card_Iic] at he
    omega

theorem kuhnOrderedCube_nearest_vertex (x : SpatialCoordinates d) (hx : x ∈ kuhnOrderedCube d)
    (hne : ∀ j, x j ≠ (1:ℝ)/2) :
    ∃ k : Fin (d+1), ∀ j, |x j-(kuhnReferenceSimplex d).points k j| < (1:ℝ)/2 := by
  obtain ⟨k,hk⟩ := antitone_threshold_cut x hx.2 ((1:ℝ)/2)
  refine ⟨k,?_⟩
  intro j
  rw [kuhnReferenceSimplex_points]
  by_cases hj : j.val < k.val
  · rw [ite_eq_left hj,abs_of_nonpos (by linarith [(hx.1 j).2])]
    linarith [(hk j).mp hj]
  · rw [ite_eq_right hj,sub_zero,abs_of_nonneg (hx.1 j).1]
    have he := not_lt.mp (fun h => hj ((hk j).mpr h))
    exact lt_of_le_of_ne he (hne j)

theorem cartesianKuhnSimplex_nearest_vertex (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) {x : SpatialCoordinates d}
    (hx : x ∈ simplicialCell (cartesianKuhnSimplex o δ hδ z π).points)
    (hne : ∀ j, x j ≠ o j+((z j:ℝ)+(1:ℝ)/2)*δ j) :
    ∃ k : Fin (d+1), ∀ j,
      |x j-(cartesianKuhnSimplex o δ hδ z π).points k j| < δ j/2 := by
  rw [cartesianKuhnSimplex_cell_eq_chart] at hx
  obtain ⟨y,hy,rfl⟩ := hx
  have hyn : ∀ j, y j ≠ (1:ℝ)/2 := by
    intro j hj
    apply hne (π j)
    rw [cartesianKuhnChart_apply,π.symm_apply_apply,hj]
  obtain ⟨k,hk⟩ := kuhnOrderedCube_nearest_vertex y hy hyn
  refine ⟨k,?_⟩
  intro j
  rw [cartesianKuhnChart_apply,cartesianKuhnSimplex_points]
  have he : o j+((z j:ℝ)+y (π.symm j))*δ j-
      (o j+((z j:ℝ)+(if (π.symm j).val < k.val then 1 else 0))*δ j)=
      (y (π.symm j)-(kuhnReferenceSimplex d).points k (π.symm j))*δ j := by
    rw [kuhnReferenceSimplex_points]
    ring
  rw [he,abs_mul,abs_of_pos (hδ j)]
  nlinarith [mul_lt_mul_of_pos_right (hk (π.symm j)) (hδ j)]

end Carleman
