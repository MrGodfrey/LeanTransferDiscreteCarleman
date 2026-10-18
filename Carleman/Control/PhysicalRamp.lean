module

public import Carleman.Control.PhysicalCutoff
public import Mathlib.Algebra.Order.Group.MinMax

/-! A concrete Lipschitz cutoff, sufficient for the discrete argument.
Replacing the manuscript's smooth cutoff preserves its node values,
support widths and difference-quotient bounds. -/
@[expose] public noncomputable section
namespace Carleman.Physical

def clipUnit (x : ℝ) : ℝ := max 0 (min 1 x)

theorem clipUnit_bounds (x : ℝ) : 0 ≤ clipUnit x ∧ clipUnit x ≤ 1 :=
  ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

theorem clipUnit_zero {x : ℝ} (hx : x ≤ 0) : clipUnit x = 0 :=
  max_eq_left ((min_le_right _ _).trans hx)

theorem clipUnit_one {x : ℝ} (hx : 1 ≤ x) : clipUnit x = 1 := by
  rw [clipUnit,min_eq_left hx,max_eq_right (by norm_num : (0:ℝ) ≤ 1)]

theorem clipUnit_lipschitz (x y : ℝ) : |clipUnit x-clipUnit y| ≤ |x-y| := by
  calc
    _ ≤ max |(0:ℝ)-0| |min 1 x-min 1 y| := abs_max_sub_max_le_max _ _ _ _
    _ ≤ max |(0:ℝ)-0| (max |(1:ℝ)-1| |x-y|) :=
      max_le_max le_rfl (abs_min_sub_min_le_max _ _ _ _)
    _ = |x-y| := by simp

def endpointDistance (T t : ℝ) : ℝ := min t (T-t)

theorem endpointDistance_lipschitz (T t s : ℝ) :
    |endpointDistance T t-endpointDistance T s| ≤ |t-s| := by
  have he : T-t-(T-s) = -(t-s) := by ring
  exact (abs_min_sub_min_le_max t (T-t) s (T-s)).trans_eq (by rw [he,abs_neg,max_self])

def physicalCutoff (T a t : ℝ) : ℝ := clipUnit ((endpointDistance T t-a)/a)

theorem physicalCutoff_bounds (T a t : ℝ) :
    0 ≤ physicalCutoff T a t ∧ physicalCutoff T a t ≤ 1 := clipUnit_bounds _

theorem physicalCutoff_zero {T a t : ℝ} (ha : 0 < a) (ht : endpointDistance T t ≤ a) :
    physicalCutoff T a t = 0 :=
  clipUnit_zero (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) ha.le)

theorem physicalCutoff_one {T a t : ℝ} (ha : 0 < a) (ht : 2*a ≤ endpointDistance T t) :
    physicalCutoff T a t = 1 := by
  apply clipUnit_one
  apply (le_div_iff₀ ha).mpr
  linarith only [ht]

theorem physicalCutoff_endpoints (T a : ℝ) (ha : 0 < a) :
    physicalCutoff T a 0 = 0 ∧ physicalCutoff T a T = 0 := by
  constructor
  · exact physicalCutoff_zero ha ((min_le_left _ _).trans ha.le)
  · apply physicalCutoff_zero ha
    exact (min_le_right _ _).trans (by simpa only [sub_self] using ha.le)

theorem physicalCutoff_lipschitz (T a t s : ℝ) (ha : 0 < a) :
    |physicalCutoff T a t-physicalCutoff T a s| ≤ |t-s|/a := by
  have he : (endpointDistance T t-a)/a-(endpointDistance T s-a)/a =
      (endpointDistance T t-endpointDistance T s)/a := by ring
  exact (clipUnit_lipschitz _ _).trans (by
    rw [he,abs_div,abs_of_pos ha]
    exact div_le_div_of_nonneg_right (endpointDistance_lipschitz T t s) ha.le)

def cutoffNodes (g : TimeGrid) (a : ℝ) : Fin (g.steps+1) → ℝ :=
  fun n => physicalCutoff g.period a ((n.val:ℝ)*g.dt)

theorem cutoffNodes_endpoints (g : TimeGrid) (a : ℝ) (ha : 0 < a) :
    cutoffNodes g a 0 = 0 ∧ cutoffNodes g a (Fin.last g.steps) = 0 := by
  simpa only [cutoffNodes,Fin.val_zero,Nat.cast_zero,zero_mul,Fin.val_last,TimeGrid.period] using
    physicalCutoff_endpoints g.period a ha

theorem cutoffNodes_difference (g : TimeGrid) (a : ℝ) (ha : 0 < a) (i : Fin g.steps) :
    |(cutoffNodes g a i.succ-cutoffNodes g a i.castSucc)/g.dt| ≤ 1/a := by
  have hh := physicalCutoff_lipschitz g.period a ((i.val+1)*g.dt) (i.val*g.dt) ha
  have he : ((i.val:ℝ)+1)*g.dt-i.val*g.dt = g.dt := by ring
  rw [he,abs_of_pos g.dt_pos] at hh
  rw [abs_div,abs_of_pos g.dt_pos]
  apply (div_le_iff₀ g.dt_pos).mpr
  simpa only [cutoffNodes,Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one,one_div,
    div_eq_mul_inv,mul_comm,mul_one] using hh

theorem cutoffNodes_transition_location (g : TimeGrid) (a : ℝ) (ha : 0 < a)
    (i : Fin g.steps) (hi : cutoffNodes g a i.succ ≠ cutoffNodes g a i.castSucc) :
    (i.val:ℝ)*g.dt ≤ 2*a+g.dt ∨ g.period-(i.val:ℝ)*g.dt ≤ 2*a+g.dt := by
  by_contra hn
  push Not at hn
  have h0 : 2*a ≤ endpointDistance g.period ((i.val:ℝ)*g.dt) :=
    le_min (by linarith [g.dt_pos]) (by linarith [g.dt_pos])
  have h1 : 2*a ≤ endpointDistance g.period (((i.val:ℝ)+1)*g.dt) := by
    apply le_min <;> nlinarith [g.dt_pos]
  apply hi
  simp only [cutoffNodes,Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one]
  rw [physicalCutoff_one ha h0,physicalCutoff_one ha h1]

end Carleman.Physical
