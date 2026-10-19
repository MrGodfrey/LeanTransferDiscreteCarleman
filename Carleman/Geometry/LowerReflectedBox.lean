module

public import Carleman.Geometry.CoordinateReflection
public import Carleman.Geometry.CoordinateBoxConvexity

/-! Reflection across a lower face of the actual original coordinate box. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

def lowerReflectedBox (a b : Fin d → ℝ) (r : Fin d) : Set (SpatialCoordinates d) :=
  openCoordinateBox (Function.update a r (2*a r-b r)) b

theorem coordinateReflection_fixed_plane (r : Fin d) (c : ℝ)
    {x : SpatialCoordinates d} (hx : x r=c) : coordinateReflection r c x=x := by
  ext j
  rw [coordinateReflection_apply]
  by_cases hj : j=r
  · subst j; simp only [ite_true,hx]; ring
  · simp [hj]

theorem lowerReflectedBox_boundary_exclusion (a b : Fin d → ℝ) (hpos : ∀ j, a j < b j)
    (r : Fin d) {x : SpatialCoordinates d}
    (hx : x ∈ frontier (openCoordinateBox a b)) (hr : x r ≠ a r) :
    x ∉ lowerReflectedBox a b r ∧ coordinateReflection r (a r) x ∉ lowerReflectedBox a b r := by
  have hclosed : x ∈ closedCoordinateBox a b := by
    rw [← closure_openCoordinateBox a b hpos]
    exact hx.1
  have hnot : x ∉ openCoordinateBox a b := by
    simpa only [(openCoordinateBox_isOpen a b).interior_eq] using hx.2
  have hlo : a r < x r := lt_of_le_of_ne (hclosed r).1 hr.symm
  constructor
  · intro ht
    apply hnot
    intro j
    by_cases hj : j=r
    · subst j; exact ⟨hlo,(ht r).2⟩
    · simpa only [Function.update_of_ne hj] using ht j
  · intro ht
    apply hnot
    intro j
    have hjt := ht j
    by_cases hj : j=r
    · subst j
      simp only [coordinateReflection_apply,ite_true,Function.update_self] at hjt
      exact ⟨hlo,by linarith [hjt.1]⟩
    · simpa only [coordinateReflection_apply,ite_eq_right_iff.mpr (fun h => (hj h).elim),
        Function.update_of_ne hj] using hjt

theorem lowerReflectedBox_no_original_overlap (a b : Fin d → ℝ) (r : Fin d)
    {x : SpatialCoordinates d} (hx : x ∈ openCoordinateBox a b) :
    coordinateReflection r (a r) x ∉ openCoordinateBox a b := by
  intro hh
  have hn := (hh r).1
  simp only [coordinateReflection_apply,ite_true] at hn
  linarith [(hx r).1]

theorem lowerReflectedBox_contains_original (a b : Fin d → ℝ) (hpos : ∀ j, a j < b j)
    (r : Fin d) : openCoordinateBox a b ⊆ lowerReflectedBox a b r := by
  intro x hx j
  by_cases hj : j=r
  · subst j
    rw [Function.update_self]
    exact ⟨by linarith [(hx r).1,hpos r],(hx r).2⟩
  · simpa only [Function.update_of_ne hj] using hx j

theorem lowerReflectedBox_contains_reflection (a b : Fin d → ℝ)
    (r : Fin d) : (coordinateReflection r (a r)) ⁻¹' openCoordinateBox a b ⊆ lowerReflectedBox a b r := by
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
