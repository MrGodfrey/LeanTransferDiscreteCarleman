module

public import Carleman.Periodic.LinearMap

/-! The nonnegative discrete time energy, used for uniqueness of the shifted scheme. -/

public section

namespace Carleman.TimeGrid

open scoped BigOperators

variable (g : Carleman.TimeGrid)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The cyclic boundary term vanishes, leaving half the sum of squared increments. -/
theorem pairing_dPlus_self (u : g.Sequence H) :
    g.pairing (g.dPlus u) u =
      (∑ i, inner ℝ (u i - u (g.prev i)) (u i - u (g.prev i))) / 2 := by
  have hsum : (∑ i, inner ℝ (u (g.prev i)) (u (g.prev i))) =
      ∑ i, inner ℝ (u i) (u i) := Equiv.sum_comp g.prev (fun i => inner ℝ (u i) (u i))
  simp only [pairing, dPlus, real_inner_smul_left, ← Finset.mul_sum,
    ← mul_assoc, mul_inv_cancel₀ (ne_of_gt g.dt_pos), one_mul]
  simp only [inner_sub_left, inner_sub_right, Finset.sum_sub_distrib, hsum]
  have hcomm : (∑ i, inner ℝ (u i) (u (g.prev i))) =
      ∑ i, inner ℝ (u (g.prev i)) (u i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact real_inner_comm _ _
  rw [hcomm]
  ring

theorem pairing_dPlus_self_nonneg (u : g.Sequence H) :
    0 ≤ g.pairing (g.dPlus u) u := by
  rw [g.pairing_dPlus_self]
  exact div_nonneg (Finset.sum_nonneg fun _ _ => real_inner_self_nonneg) (by norm_num)

theorem pairing_dMinus_self_nonneg (u : g.Sequence H) :
    0 ≤ g.pairing (g.dMinus u) u := by
  rw [g.pairing_dMinus, g.pairing_comm]
  exact g.pairing_dPlus_self_nonneg u

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem dPlus_sub (u v : g.Sequence E) : g.dPlus (u - v) = g.dPlus u - g.dPlus v := by
  funext i
  simp only [dPlus, Pi.sub_apply, smul_sub]
  abel

theorem dMinus_sub (u v : g.Sequence E) : g.dMinus (u - v) = g.dMinus u - g.dMinus v := by
  funext i
  simp only [dMinus, Pi.sub_apply, smul_sub]
  abel

end Carleman.TimeGrid
