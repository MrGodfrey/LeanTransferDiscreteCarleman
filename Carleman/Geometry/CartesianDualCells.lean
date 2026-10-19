module

public import Carleman.Geometry.CartesianInteriorNodes
public import Carleman.Geometry.KuhnCellVolume

/-! The original interior dual cells, including the uncovered boundary strip. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

def cartesianDualCell (o δ : Fin d → ℝ) (N : Fin d → ℕ) (a : CartesianInteriorIndex N) :
    Set (SpatialCoordinates d) :=
  openCoordinateBox (fun j => cartesianInteriorPoint o δ N a j-δ j/2)
    (fun j => cartesianInteriorPoint o δ N a j+δ j/2)

theorem cartesianDualCell_measurable (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (a : CartesianInteriorIndex N) : MeasurableSet (cartesianDualCell o δ N a) :=
  (openCoordinateBox_isOpen _ _).measurableSet

theorem cartesianDualCell_subset (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : CartesianInteriorIndex N) :
    cartesianDualCell o δ N a ⊆ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j) := by
  intro x hx j
  have hxj := hx j
  have ha0 : (0:ℝ) ≤ (a j).val := Nat.cast_nonneg _
  have hau : (a j).val+1 < N j := by have := (a j).isLt; omega
  have hau' : ((a j).val:ℝ)+1 < N j := by exact_mod_cast hau
  change o j+(((a j).val:ℤ)+1:ℤ)*δ j-δ j/2 < x j ∧
    x j < o j+(((a j).val:ℤ)+1:ℤ)*δ j+δ j/2 at hxj
  push_cast at hxj
  have hau2 : ((a j).val:ℝ)+2 ≤ N j := by exact_mod_cast hau
  constructor <;> nlinarith [mul_nonneg ha0 (hδ j).le,
    mul_le_mul_of_nonneg_right hau2 (hδ j).le]

theorem cartesianDualCell_disjoint (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) : Pairwise fun a b : CartesianInteriorIndex N =>
      Disjoint (cartesianDualCell o δ N a) (cartesianDualCell o δ N b) := by
  intro a b hab
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hab
  apply Set.disjoint_left.mpr
  intro x hxa hxb
  have ha := hxa j
  have hb := hxb j
  change o j+(((a j).val:ℤ)+1:ℤ)*δ j-δ j/2 < x j ∧
    x j < o j+(((a j).val:ℤ)+1:ℤ)*δ j+δ j/2 at ha
  change o j+(((b j).val:ℤ)+1:ℤ)*δ j-δ j/2 < x j ∧
    x j < o j+(((b j).val:ℤ)+1:ℤ)*δ j+δ j/2 at hb
  push_cast at ha hb
  have hv : (a j).val ≠ (b j).val := fun h => hj (Fin.ext h)
  rcases lt_or_gt_of_ne hv with hlt | hlt
  · have hh : ((a j).val:ℝ)+1 ≤ (b j).val := by exact_mod_cast hlt
    nlinarith [mul_le_mul_of_nonneg_right hh (hδ j).le]
  · have hh : ((b j).val:ℝ)+1 ≤ (a j).val := by exact_mod_cast hlt
    nlinarith [mul_le_mul_of_nonneg_right hh (hδ j).le]

theorem cartesianDualCell_volume (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : CartesianInteriorIndex N) :
    volume.real (cartesianDualCell o δ N a)=∏ j, δ j := by
  rw [cartesianDualCell,openCoordinateBox_volume_real _ _ (fun j => by linarith [hδ j])]
  apply Finset.prod_congr rfl
  intro j _
  ring

theorem cartesianDualCell_restrict_volume (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : CartesianInteriorIndex N) :
    (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))).real
      (cartesianDualCell o δ N a)=∏ j, δ j := by
  rw [Measure.real,Measure.restrict_apply (cartesianDualCell_measurable o δ N a),
    Set.inter_eq_left.mpr (cartesianDualCell_subset o δ hδ N a)]
  exact cartesianDualCell_volume o δ hδ N a

end Carleman
