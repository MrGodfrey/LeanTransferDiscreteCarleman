module

public import Carleman.Geometry.LowerReflectedBox

/-! Reflection across an upper face of the actual original coordinate box. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

def upperReflectedBox (a b : Fin d → ℝ) (r : Fin d) : Set (SpatialCoordinates d) :=
  openCoordinateBox a (Function.update b r (2*b r-a r))

theorem upperReflectedBox_boundary_exclusion (a b : Fin d → ℝ) (hpos : ∀ j, a j < b j)
    (r : Fin d) {x : SpatialCoordinates d}
    (hx : x ∈ frontier (openCoordinateBox a b)) (hr : x r ≠ b r) :
    x ∉ upperReflectedBox a b r ∧ coordinateReflection r (b r) x ∉ upperReflectedBox a b r := by
  have hclosed : x ∈ closedCoordinateBox a b := by
    rw [← closure_openCoordinateBox a b hpos]
    exact hx.1
  have hnot : x ∉ openCoordinateBox a b := by
    simpa only [(openCoordinateBox_isOpen a b).interior_eq] using hx.2
  have hhi : x r < b r := lt_of_le_of_ne (hclosed r).2 hr
  constructor
  · intro ht
    apply hnot
    intro j
    by_cases hj : j=r
    · subst j; exact ⟨(ht r).1,hhi⟩
    · simpa only [Function.update_of_ne hj] using ht j
  · intro ht
    apply hnot
    intro j
    have hjt := ht j
    by_cases hj : j=r
    · subst j
      simp only [coordinateReflection_apply,ite_true,Function.update_self] at hjt
      exact ⟨by linarith [hjt.2],hhi⟩
    · simpa only [coordinateReflection_apply,ite_eq_right_iff.mpr (fun h => (hj h).elim),
        Function.update_of_ne hj] using hjt

theorem upperReflectedBox_no_original_overlap (a b : Fin d → ℝ) (r : Fin d)
    {x : SpatialCoordinates d} (hx : x ∈ openCoordinateBox a b) :
    coordinateReflection r (b r) x ∉ openCoordinateBox a b := by
  intro hh
  have hn := (hh r).2
  simp only [coordinateReflection_apply,ite_true] at hn
  linarith [(hx r).2]

theorem upperReflectedBox_contains_original (a b : Fin d → ℝ) (hpos : ∀ j, a j < b j)
    (r : Fin d) : openCoordinateBox a b ⊆ upperReflectedBox a b r := by
  intro x hx j
  by_cases hj : j=r
  · subst j
    rw [Function.update_self]
    exact ⟨(hx r).1,by linarith [(hx r).2,hpos r]⟩
  · simpa only [Function.update_of_ne hj] using hx j

theorem upperReflectedBox_contains_reflection (a b : Fin d → ℝ)
    (r : Fin d) : (coordinateReflection r (b r)) ⁻¹' openCoordinateBox a b ⊆ upperReflectedBox a b r := by
  intro x hx j
  have hjx := hx j
  by_cases hj : j=r
  · subst j
    simp only [coordinateReflection_apply,ite_true] at hjx
    rw [Function.update_self]
    constructor <;> linarith [hjx.1,hjx.2]
  · simpa only [coordinateReflection_apply,ite_eq_right_iff.mpr (fun h => (hj h).elim),
      Function.update_of_ne hj] using hjx

end Carleman
