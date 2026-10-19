module

public import Carleman.Weights.HeatRemainderBound

/-! Choosing the manuscript's beta and q threshold before all temporal data. -/
@[expose] public noncomputable section
namespace Carleman

theorem exists_heat_absorption_parameters {m C : ℝ} (hm : 0 < m) (hC : 0 < C) :
    ∃ β qc : ℝ, 0 < β ∧ β ≤ 1 ∧ 1 ≤ qc ∧ ∀ Q : ℝ, qc ≤ Q →
      C*(Q^2+(β+β^2)*Q^3) ≤ (m/2)*Q^3 := by
  let β := min 1 (m/(8*C))
  let qc := max 1 (4*C/m)
  have hβ : 0 < β := lt_min (by norm_num) (by positivity)
  have hβ1 : β ≤ 1 := min_le_left _ _
  have hβm : β*(8*C) ≤ m := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  refine ⟨β,qc,hβ,hβ1,le_max_left _ _,?_⟩
  intro Q hQ
  have hQ1 : 1 ≤ Q := (le_max_left _ _).trans hQ
  have hQ0 : 0 ≤ Q := by linarith
  have hCQ : 4*C ≤ Q*m := (div_le_iff₀ hm).mp ((le_max_right _ _).trans hQ)
  have hβsq : β^2 ≤ β := by nlinarith
  have hsmall : C*(β+β^2) ≤ m/4 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_right hCQ (sq_nonneg Q)
  have h2 := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ Q^3 by positivity)
  nlinarith

end Carleman
