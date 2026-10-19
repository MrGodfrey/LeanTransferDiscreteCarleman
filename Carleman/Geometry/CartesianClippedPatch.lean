module

public import Carleman.Geometry.FiniteCartesianKuhnCover

/-! Concrete open rectangular patches clipped to the physical domain.
Their widths lie between one and five mesh steps and overlap uniformly. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

def cartesianClippedPatchLower (o δ : Fin d → ℝ) (N : Fin d → ℕ) (i : CartesianCellIndex N) : Fin d → ℝ :=
  fun j => max (o j) (o j+(((i.1 j).val:ℝ)-2)*δ j)

def cartesianClippedPatchUpper (o δ : Fin d → ℝ) (N : Fin d → ℕ) (i : CartesianCellIndex N) : Fin d → ℝ :=
  fun j => min (o j+(N j:ℝ)*δ j) (o j+(((i.1 j).val:ℝ)+3)*δ j)

def cartesianClippedPatch (o δ : Fin d → ℝ) (N : Fin d → ℕ) (i : CartesianCellIndex N) :
    Set (SpatialCoordinates d) :=
  openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j) ∩
    cartesianPatch o δ 2 (cartesianCellLatticeIndex N i).1

theorem cartesianClippedPatch_eq_box (o δ : Fin d → ℝ) (N : Fin d → ℕ) (i : CartesianCellIndex N) :
    cartesianClippedPatch o δ N i=
      openCoordinateBox (cartesianClippedPatchLower o δ N i) (cartesianClippedPatchUpper o δ N i) := by
  ext x
  change ((∀ j, o j < x j ∧ x j < o j+(N j:ℝ)*δ j) ∧
    (∀ j, o j+(((i.1 j).val:ℝ)-2)*δ j < x j ∧ x j < o j+(((i.1 j).val:ℝ)+2+1)*δ j)) ↔
    (∀ j, max (o j) (o j+(((i.1 j).val:ℝ)-2)*δ j) < x j ∧
      x j < min (o j+(N j:ℝ)*δ j) (o j+(((i.1 j).val:ℝ)+3)*δ j))
  constructor
  · rintro ⟨hS,hP⟩ j
    exact ⟨max_lt (hS j).1 (hP j).1,lt_min (hS j).2 (by linarith [(hP j).2])⟩
  · intro hx
    constructor <;> intro j
    · exact ⟨(max_lt_iff.mp (hx j).1).1,(lt_min_iff.mp (hx j).2).1⟩
    · exact ⟨(max_lt_iff.mp (hx j).1).2,by linarith [(lt_min_iff.mp (hx j).2).2]⟩

theorem cartesianClippedPatch_width_bounds (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (i : CartesianCellIndex N) (j : Fin d) :
    δ j ≤ cartesianClippedPatchUpper o δ N i j-cartesianClippedPatchLower o δ N i j ∧
    cartesianClippedPatchUpper o δ N i j-cartesianClippedPatchLower o δ N i j ≤ 5*δ j := by
  have hz : (0:ℝ) ≤ (i.1 j).val := Nat.cast_nonneg _
  have hN : ((i.1 j).val:ℝ)+1 ≤ N j := by exact_mod_cast (i.1 j).isLt
  have hl : cartesianClippedPatchLower o δ N i j ≤ o j+((i.1 j).val:ℝ)*δ j := by
    apply max_le <;> nlinarith [hδ j]
  have hu : o j+(((i.1 j).val:ℝ)+1)*δ j ≤ cartesianClippedPatchUpper o δ N i j := by
    apply le_min <;> nlinarith [hδ j]
  have hl' : o j+(((i.1 j).val:ℝ)-2)*δ j ≤ cartesianClippedPatchLower o δ N i j := le_max_right _ _
  have hu' : cartesianClippedPatchUpper o δ N i j ≤ o j+(((i.1 j).val:ℝ)+3)*δ j := min_le_right _ _
  constructor <;> nlinarith

theorem cartesianClippedPatch_isOpen (o δ : Fin d → ℝ) (N : Fin d → ℕ) (i : CartesianCellIndex N) :
    IsOpen (cartesianClippedPatch o δ N i) :=
  (openCoordinateBox_isOpen _ _).inter (cartesianPatch_isOpen o δ 2 _)

theorem cartesianClippedPatch_subset_domain (o δ : Fin d → ℝ) (N : Fin d → ℕ) (i : CartesianCellIndex N) :
    cartesianClippedPatch o δ N i ⊆ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j) := inter_subset_left

theorem cartesianClippedPatch_contains_cell (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (i : CartesianCellIndex N) :
    simplicialCell (cartesianFiniteSimplex o δ hδ N i).points ∩
      openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j) ⊆ cartesianClippedPatch o δ N i := by
  intro x hx
  exact ⟨hx.2,cartesianKuhnStarPatch_subset_patch o δ hδ _ _
    (cartesianKuhn_cell_subset_starPatch o δ hδ _ _ hx.1)⟩

theorem cartesianClippedPatch_multiplicity_le (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (x : SpatialCoordinates d) :
    finiteCoverMultiplicity (cartesianClippedPatch o δ N) x ≤ 5^d*d.factorial := by
  simpa using cartesianPatch_permutation_multiplicity_le o δ hδ 2
    (cartesianCellLatticeIndex N) (cartesianCellLatticeIndex_injective N)
    (cartesianClippedPatch o δ N) (fun _ => inter_subset_right) x

end Carleman
