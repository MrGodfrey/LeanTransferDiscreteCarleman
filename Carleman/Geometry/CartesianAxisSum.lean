module

public import Carleman.Geometry.CartesianInteriorNodes
public import Mathlib.Logic.Equiv.Prod

/-! Exact Fubini decomposition of a finite Cartesian grid into coordinate lines. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

def cartesianAxisFill (N : Fin d → ℕ) (r : Fin d)
    (w : ∀ j : {j // j ≠ r}, Fin (N j)) (k : ℕ) : Fin d → ℕ :=
  fun j => if h : j=r then k else (w ⟨j,h⟩).val

theorem cartesianAxisFill_self (N : Fin d → ℕ) (r : Fin d)
    (w : ∀ j : {j // j ≠ r}, Fin (N j)) (k : ℕ) :
    cartesianAxisFill N r w k r=k := by simp [cartesianAxisFill]

theorem cartesianAxisFill_update (N : Fin d → ℕ) (r : Fin d)
    (w : ∀ j : {j // j ≠ r}, Fin (N j)) (k t : ℕ) :
    Function.update (cartesianAxisFill N r w k) r t=cartesianAxisFill N r w t := by
  funext j
  by_cases hj : j=r
  · subst j; simp [cartesianAxisFill]
  · simp [cartesianAxisFill,hj]

theorem cartesian_sum_axis (N : Fin d → ℕ) (r : Fin d) (F : (Fin d → ℕ) → ℝ) :
    (∑ z : ∀ j, Fin (N j), F (fun j => (z j).val)) =
      ∑ w : ∀ j : {j // j ≠ r}, Fin (N j),
        ∑ k ∈ Finset.range (N r), F (cartesianAxisFill N r w k) := by
  classical
  rw [← (Equiv.piSplitAt r (fun j => Fin (N j))).symm.sum_comp
    (fun z => F (fun j => (z j).val)),Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  funext j
  by_cases hj : j=r
  · subst j; simp [Equiv.piSplitAt,cartesianAxisFill]
  · simp [Equiv.piSplitAt,cartesianAxisFill,hj]

end Carleman
