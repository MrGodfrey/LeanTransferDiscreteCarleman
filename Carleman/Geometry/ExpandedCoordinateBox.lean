module

public import Carleman.Geometry.UpperReflectedBox

/-! A fixed finite family of enlarged boxes, independent of the Poisson state.
Each processed coordinate has both original faces strictly inside. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

def expandedBoxLower (a b : Fin d → ℝ) (s : Finset (Fin d)) (i : Fin d) : ℝ :=
  if i ∈ s then 2*a i-b i else a i

def expandedBoxUpper (a b : Fin d → ℝ) (s : Finset (Fin d)) (i : Fin d) : ℝ :=
  if i ∈ s then 3*b i-2*a i else b i

theorem expandedBox_positive (a b : Fin d → ℝ) (hpos : ∀ i, a i < b i) (s : Finset (Fin d)) :
    ∀ i, expandedBoxLower a b s i < expandedBoxUpper a b s i := by
  intro i
  by_cases hi : i ∈ s <;> simp only [expandedBoxLower,expandedBoxUpper,hi,ite_true,ite_false]
  · linarith [hpos i]
  · exact hpos i

theorem expandedBox_contains (a b : Fin d → ℝ) (s : Finset (Fin d)) :
    openCoordinateBox a b ⊆ openCoordinateBox (expandedBoxLower a b s) (expandedBoxUpper a b s) := by
  intro x hx i
  by_cases hi : i ∈ s <;> simp only [expandedBoxLower,expandedBoxUpper,hi,ite_true,ite_false]
  · constructor <;> linarith [(hx i).1,(hx i).2]
  · exact hx i

theorem expandedBoxLower_insert (a b : Fin d → ℝ) (s : Finset (Fin d)) (r : Fin d) (hr : r ∉ s) :
    Function.update (expandedBoxLower a b s) r (2*expandedBoxLower a b s r-expandedBoxUpper a b s r)=
      expandedBoxLower a b (insert r s) := by
  ext j
  by_cases hj : j=r
  · subst j; simp [expandedBoxLower,expandedBoxUpper,hr]
  · simp [expandedBoxLower,hj]

theorem expandedBoxUpper_insert (a b : Fin d → ℝ) (s : Finset (Fin d)) (r : Fin d) (hr : r ∉ s) :
    Function.update (expandedBoxUpper a b s) r
      (2*expandedBoxUpper a b s r-expandedBoxLower a b (insert r s) r)=
      expandedBoxUpper a b (insert r s) := by
  ext j
  by_cases hj : j=r
  · subst j; simp only [expandedBoxLower,expandedBoxUpper,Finset.mem_insert_self,ite_true,
      hr,ite_false,Function.update_self]; ring
  · simp [expandedBoxUpper,hj]

theorem expandedBox_closure_inside (a b : Fin d → ℝ) (hpos : ∀ i, a i < b i) :
    closure (openCoordinateBox a b) ⊆
      openCoordinateBox (expandedBoxLower a b Finset.univ) (expandedBoxUpper a b Finset.univ) := by
  rw [closure_openCoordinateBox a b hpos]
  intro x hx i
  simp only [expandedBoxLower,expandedBoxUpper,Finset.mem_univ,ite_true]
  constructor <;> linarith [(hx i).1,(hx i).2,hpos i]

end Carleman
