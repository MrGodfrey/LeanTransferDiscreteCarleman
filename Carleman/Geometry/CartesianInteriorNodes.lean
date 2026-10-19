module

public import Carleman.Geometry.KuhnNodeIncidence

/-! The original full finite set of interior Cartesian nodes, with values
extended to physical points only by evaluation at this finite node set. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

abbrev CartesianInteriorIndex (N : Fin d → ℕ) := ∀ j, Fin (N j-1)

def cartesianInteriorLatticeIndex (N : Fin d → ℕ) (a : CartesianInteriorIndex N) : Fin d → ℤ :=
  fun j => (a j).val+1

def cartesianInteriorPoint (o δ : Fin d → ℝ) (N : Fin d → ℕ) (a : CartesianInteriorIndex N) :
    SpatialCoordinates d := cartesianGridPoint o δ (cartesianInteriorLatticeIndex N a)

theorem cartesianInteriorPoint_mem (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : CartesianInteriorIndex N) :
    cartesianInteriorPoint o δ N a ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j) := by
  intro j
  have hj := (a j).isLt
  have hi : 0 < (a j).val+1 := Nat.succ_pos _
  have hu : (a j).val+1 < N j := by omega
  have hi' : (0:ℝ) < (a j).val+1 := by exact_mod_cast hi
  have hu' : ((a j).val:ℝ)+1 < N j := by exact_mod_cast hu
  change o j < o j+(((a j).val:ℤ)+1:ℤ)*δ j ∧ o j+(((a j).val:ℤ)+1:ℤ)*δ j < o j+(N j:ℝ)*δ j
  push_cast
  constructor
  · linarith [mul_pos hi' (hδ j)]
  · nlinarith [mul_lt_mul_of_pos_right hu' (hδ j)]

theorem cartesianInteriorPoint_injective (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) : Function.Injective (cartesianInteriorPoint o δ N) := by
  intro a b he
  funext j
  apply Fin.ext
  have hj := congrArg (fun x : SpatialCoordinates d => x j) he
  change o j+(((a j).val:ℤ)+1:ℤ)*δ j=o j+(((b j).val:ℤ)+1:ℤ)*δ j at hj
  have hmul := (mul_left_inj' (hδ j).ne').mp (add_left_cancel hj)
  push_cast at hmul
  have hval : ((a j).val:ℝ)=(b j).val := add_right_cancel hmul
  exact_mod_cast hval

def cartesianInteriorData (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (f : CartesianInteriorIndex N → ℝ) (x : SpatialCoordinates d) : ℝ := by
  classical
  exact ∑ a : CartesianInteriorIndex N, if cartesianInteriorPoint o δ N a=x then f a else 0

theorem cartesianInteriorData_at_node (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) (a : CartesianInteriorIndex N) :
    cartesianInteriorData o δ N f (cartesianInteriorPoint o δ N a)=f a := by
  classical
  simp only [cartesianInteriorData,(cartesianInteriorPoint_injective o δ hδ N).eq_iff,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]

end Carleman
