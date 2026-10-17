module

public import Carleman.Periodic.CellIntegral
public import Mathlib.Algebra.Field.Periodic

/-! Closed-cell anchors retain the endpoint T before reducing the node modulo N. -/
@[expose] public noncomputable section
open Set
open Fin.NatCast Fin.IntCast
namespace Carleman.TimeGrid
variable (g : Carleman.TimeGrid)

theorem node_value_of_periodic_endpoints {E : Type*} (f : ℝ → E)
    (hend : f 0 = f g.period) (n : ℤ) (hn : 0 ≤ n) (hN : n ≤ g.steps) :
    f ((n:ℝ)*g.dt) = f (g.nodeTime (Fin.intCast n)) := by
  lift n to ℕ using hn with k
  have hk : k ≤ g.steps := by exact_mod_cast hN
  rcases lt_or_eq_of_le hk with hk | rfl
  · have hi : (Fin.intCast (k:ℤ) : g.Index) = ⟨k, hk⟩ := by
      simp only [Fin.intCast, Int.natCast_nonneg, ite_eq_left, Int.natAbs_natCast]
      exact Fin.natCast_eq_mk hk
    rw [hi]
    simp only [nodeTime, Int.cast_natCast]
  · simpa [Fin.intCast, nodeTime, period] using hend.symm

theorem cellTime_mem (n : ℕ) (hn : n ≤ g.steps) : g.cellTime n ∈ Icc 0 g.period := by
  constructor
  · exact mul_nonneg (Nat.cast_nonneg n) g.dt_pos.le
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) g.dt_pos.le

/-- Unwrapped right endpoint of the cell after i, including the periodic final cell. -/
theorem next_node_value {E : Type*} (f : ℝ → E) (hend : f 0 = f g.period) (i : g.Index) :
    f (g.cellTime (i.val+1)) = f (g.nodeTime (g.next i)) := by
  have hn : (i.val+1:ℤ) ≤ g.steps := by exact_mod_cast Nat.succ_le_of_lt i.isLt
  have he := g.node_value_of_periodic_endpoints f hend (i.val+1)
    (by omega) hn
  have hi : (Fin.intCast (i.val+1 : ℤ) : g.Index) = g.next i := by
    change (Fin.intCast (↑(i.val+1 : ℕ)) : g.Index) = g.next i
    simp only [Fin.intCast, Int.natCast_nonneg, ite_eq_left, Int.natAbs_natCast, Fin.ofNat_eq_cast]
    simp only [Nat.cast_add, Nat.cast_one, Fin.cast_val_eq_self, g.next_eq_add_one]
  rw [hi] at he
  simpa only [cellTime, Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_natCast, Int.cast_one] using he

end Carleman.TimeGrid

namespace Carleman.Orientation
variable (s : Orientation) (g : TimeGrid)

def cellNumber (t : ℝ) : ℤ := match s with
  | .plus => ⌈t/g.dt⌉
  | .minus => ⌊t/g.dt⌋

def anchor (t : ℝ) : ℝ := (s.cellNumber g t : ℝ) * g.dt

theorem extension_eq_cellNumber {E : Type*} (u : g.Sequence E) (t : ℝ) :
    s.extension g u t = u (Fin.intCast (s.cellNumber g t)) := by cases s <;> rfl

theorem cellNumber_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ s.cellNumber g t := by
  have hd : 0 ≤ t/g.dt := div_nonneg ht g.dt_pos.le
  cases s
  · exact Int.ceil_nonneg hd
  · exact Int.floor_nonneg.mpr hd

theorem cellNumber_le_steps {t : ℝ} (ht : t ≤ g.period) : s.cellNumber g t ≤ g.steps := by
  have hd : t/g.dt ≤ (g.steps:ℝ) := (div_le_iff₀ g.dt_pos).mpr ht
  cases s
  · exact Int.ceil_le.mpr (by simpa only [Int.cast_natCast] using hd)
  · have hh := (Int.floor_le (t/g.dt)).trans hd
    exact_mod_cast hh

theorem anchor_mem {t : ℝ} (ht : t ∈ Icc 0 g.period) : s.anchor g t ∈ Icc 0 g.period := by
  have hn : (0:ℝ) ≤ s.cellNumber g t := by exact_mod_cast s.cellNumber_nonneg g ht.1
  have hN : (s.cellNumber g t : ℝ) ≤ g.steps := by exact_mod_cast s.cellNumber_le_steps g ht.2
  exact ⟨mul_nonneg hn g.dt_pos.le, mul_le_mul_of_nonneg_right hN g.dt_pos.le⟩

theorem anchor_distance (t : ℝ) : |t - s.anchor g t| ≤ g.dt := by
  cases s
  · have hl := (div_le_iff₀ g.dt_pos).mp (Int.le_ceil (t/g.dt))
    have hu := mul_lt_mul_of_pos_right (Int.ceil_lt_add_one (t/g.dt)) g.dt_pos
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt g.dt_pos), one_mul] at hu
    change |t - (↑⌈t/g.dt⌉ * g.dt)| ≤ g.dt
    exact abs_le.mpr ⟨by linarith, by linarith [g.dt_pos]⟩
  · have hl := (le_div_iff₀ g.dt_pos).mp (Int.floor_le (t/g.dt))
    have hu := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (t/g.dt)) g.dt_pos
    rw [div_mul_cancel₀ _ (ne_of_gt g.dt_pos), add_mul, one_mul] at hu
    change |t - (↑⌊t/g.dt⌋ * g.dt)| ≤ g.dt
    exact abs_le.mpr ⟨by linarith [g.dt_pos], by linarith⟩

theorem anchor_value_eq_extension {E : Type*} (f : ℝ → E)
    (hend : f 0 = f g.period) {t : ℝ} (ht : t ∈ Icc 0 g.period) :
    f (s.anchor g t) = s.extension g (fun i => f (g.nodeTime i)) t := by
  rw [s.extension_eq_cellNumber]
  exact g.node_value_of_periodic_endpoints f hend _
    (s.cellNumber_nonneg g ht.1) (s.cellNumber_le_steps g ht.2)

/-- Every finite sequence extends periodically on the whole real line. -/
theorem extension_periodic {E : Type*} (u : g.Sequence E) :
    Function.Periodic (s.extension g u) g.period := by
  have hi (z : ℤ) : (Fin.intCast (z+(g.steps:ℤ)) : g.Index) = Fin.intCast z := by
    apply Fin.ext
    change (↑(↑(z+(g.steps:ℤ)) : g.Index) : ℕ) = (↑(↑z : g.Index) : ℕ)
    simp only [Fin.val_intCast, Int.add_emod, Int.emod_self, add_zero, Int.emod_emod]
  have hd (t : ℝ) : (t+g.period)/g.dt = t/g.dt + (g.steps:ℤ) := by
    simp [TimeGrid.period, add_div, ne_of_gt g.dt_pos]
  cases s <;> intro t
  · change u (Fin.intCast ⌈(t+g.period)/g.dt⌉) = u (Fin.intCast ⌈t/g.dt⌉)
    rw [hd, Int.ceil_add_intCast, hi]
  · change u (Fin.intCast ⌊(t+g.period)/g.dt⌋) = u (Fin.intCast ⌊t/g.dt⌋)
    rw [hd, Int.floor_add_intCast, hi]
end Carleman.Orientation
