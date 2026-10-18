module

public import Carleman.Transfer.ScaleExponents

/-! Positive scale thresholds and real-power budget bounds, including the
separate zero-exponent case. -/
@[expose] public noncomputable section
namespace Carleman

theorem exists_small_rpow {p ε : ℝ} (hp : 0 < p) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ x : ℝ, 0 ≤ x → x ≤ δ → x^p ≤ ε := by
  refine ⟨min 1 (ε^p⁻¹),lt_min zero_lt_one (Real.rpow_pos_of_pos hε _),min_le_left _ _,?_⟩
  intro x hx hxδ
  exact (Real.le_rpow_inv_iff_of_pos hx hε.le hp).mp (hxδ.trans (min_le_right _ _))

/-- A scale rule controls a monomial whenever its exponent budget is valid. -/
theorem scale_monomial_le {x Q κ α p ν : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) (hQ : 0 ≤ Q) (hκ : 0 ≤ κ) (hν : 0 ≤ ν)
    (hp : α*ν ≤ p) (hscale : Q ≤ κ*x^(-α)) : x^p*Q^ν ≤ κ^ν := by
  have hh := Real.rpow_le_rpow hQ hscale hν
  rw [Real.mul_rpow hκ (Real.rpow_nonneg hx.le _),← Real.rpow_mul hx.le] at hh
  calc
    x^p*Q^ν ≤ x^p*(κ^ν*x^(-α*ν)) := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hx.le _)
    _ = κ^ν*(x^p*x^(-α*ν)) := by ring
    _ = κ^ν*x^(p-α*ν) := by rw [← Real.rpow_add hx]; congr 2; ring
    _ ≤ κ^ν := mul_le_of_le_one_right (Real.rpow_nonneg hκ _) (Real.rpow_le_one hx.le hx1 (sub_nonneg.mpr hp))

end Carleman
