module

public import Carleman.Transfer.ScaleRates

/-! Both exact transfer defects are bounded by the original budget powers. -/
@[expose] public noncomputable section
namespace Carleman.ErrorScales
variable (e : ErrorScales) (g : TimeGrid) (a : CarlemanExponents) (Q : ℝ)

theorem defects_le_budget (hQ : 1 ≤ Q) :
    e.loadDefect g a Q ≤ (e.energy g)^2*Q^a.nuEnergy+(e.l2 g)^2*Q^a.nuL2 ∧
    e.stateDefect g a Q ≤ (e.energy g)^2*Q^a.nuEnergy+(e.l2 g)^2*Q^a.nuL2 := by
  have hE : Q^a.dStar ≤ Q^a.nuEnergy := Real.rpow_le_rpow_of_exponent_le hQ (le_max_left _ _)
  have h0 : Q^a.bStar ≤ Q^a.nuL2 := Real.rpow_le_rpow_of_exponent_le hQ (le_max_left _ _)
  have hzE : max 1 (Q^(4*a.m+a.dStar-a.c₀)) ≤ Q^a.nuEnergy :=
    max_le (Real.one_le_rpow hQ a.nuEnergy_nonneg)
      (Real.rpow_le_rpow_of_exponent_le hQ ((le_max_left _ _).trans (le_max_right _ _)))
  have hz0 : max 1 (Q^(4*a.m+a.bStar-a.c₀)) ≤ Q^a.nuL2 :=
    max_le (Real.one_le_rpow hQ a.nuL2_pos.le)
      (Real.rpow_le_rpow_of_exponent_le hQ ((le_max_left _ _).trans (le_max_right _ _)))
  exact ⟨add_le_add (mul_le_mul_of_nonneg_left hE (sq_nonneg _))
    (mul_le_mul_of_nonneg_left h0 (sq_nonneg _)),
    add_le_add (mul_le_mul_of_nonneg_left hzE (sq_nonneg _))
      (mul_le_mul_of_nonneg_left hz0 (sq_nonneg _))⟩

end Carleman.ErrorScales
