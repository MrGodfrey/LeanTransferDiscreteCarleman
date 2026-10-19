module

public import Carleman.Spatial.FiniteCellMultiplier
public import Carleman.Geometry.CartesianDualCells

/-! The original zero-extended cell reconstruction takes the value of its nearest lattice node. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem cartesian_lattice_unique_nearest (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z w : Fin d → ℤ) (x : SpatialCoordinates d)
    (hz : ∀ j, |x j-cartesianGridPoint o δ z j| < δ j/2)
    (hw : ∀ j, |x j-cartesianGridPoint o δ w j| < δ j/2) : z=w := by
  funext j
  have h1 := abs_lt.mp (hz j)
  have h2 := abs_lt.mp (hw j)
  change -(δ j/2) < x j-(o j+(z j:ℝ)*δ j) ∧ x j-(o j+(z j:ℝ)*δ j) < δ j/2 at h1
  change -(δ j/2) < x j-(o j+(w j:ℝ)*δ j) ∧ x j-(o j+(w j:ℝ)*δ j) < δ j/2 at h2
  by_contra he
  rcases lt_or_gt_of_ne he with hlt | hlt
  · have hi : z j+1 ≤ w j := by omega
    have hr : (z j:ℝ)+1 ≤ w j := by exact_mod_cast hi
    nlinarith [mul_le_mul_of_nonneg_right hr (hδ j).le]
  · have hi : w j+1 ≤ z j := by omega
    have hr : (w j:ℝ)+1 ≤ z j := by exact_mod_cast hi
    nlinarith [mul_le_mul_of_nonneg_right hr (hδ j).le]

theorem cartesianCellFunction_nearest_value (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) (z : Fin d → ℤ)
    (x : SpatialCoordinates d) (hx : ∀ j, |x j-cartesianGridPoint o δ z j| < δ j/2) :
    finiteCellFunction (cartesianDualCell o δ N) f x=cartesianInteriorData o δ N f (cartesianGridPoint o δ z) := by
  classical
  by_cases ha : ∃ a : CartesianInteriorIndex N, cartesianInteriorPoint o δ N a=cartesianGridPoint o δ z
  · obtain ⟨a,ha⟩ := ha
    have hm : x ∈ cartesianDualCell o δ N a := by
      intro j
      have hh := abs_lt.mp (hx j)
      rw [← ha] at hh
      constructor <;> linarith
    rw [finiteCellFunction_on_cell _ (cartesianDualCell_disjoint o δ hδ N) f a hm,
      ← ha,cartesianInteriorData_at_node o δ hδ N f a]
  · have hout : x ∉ ⋃ a, cartesianDualCell o δ N a := by
      intro hm
      obtain ⟨a,ha'⟩ := mem_iUnion.mp hm
      have hclose : ∀ j, |x j-cartesianGridPoint o δ (cartesianInteriorLatticeIndex N a) j| < δ j/2 := by
        intro j
        apply abs_lt.mpr
        have hh := ha' j
        change cartesianGridPoint o δ (cartesianInteriorLatticeIndex N a) j-δ j/2 < x j ∧
          x j < cartesianGridPoint o δ (cartesianInteriorLatticeIndex N a) j+δ j/2 at hh
        constructor <;> linarith
      have he := cartesian_lattice_unique_nearest o δ hδ _ z x hclose hx
      exact ha ⟨a,by change cartesianGridPoint o δ (cartesianInteriorLatticeIndex N a)=_; rw [he]⟩
    rw [finiteCellFunction_zero_outside _ _ hout]
    simp only [cartesianInteriorData,ite_eq_right (fun he => ha ⟨_,he⟩),Finset.sum_const_zero]

end Carleman
