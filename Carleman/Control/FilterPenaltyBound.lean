module

public import Carleman.Control.FilteredControl

/-! The complementary penalty decays at the original rate, uniformly in the terminal subspace. -/
@[expose] public noncomputable section
namespace Carleman.Physical

def filterTerminalFactor (T M : ℝ) : ℝ :=
  Real.sqrt (1+2*(Real.exp (2*M*T))^2)*Real.exp (M*T+M^2*T^2/2)

theorem filterTerminalFactor_nonneg (T M : ℝ) : 0 ≤ filterTerminalFactor T M :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le

theorem filter_terminal_constant_budget (T M C0 : ℝ) (hC : 0 ≤ C0)
    (hbudget : 2*(filterTerminalFactor T M)^2 ≤ C0) :
    Real.sqrt (2*C0)*filterTerminalFactor T M ≤ C0 := by
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (filterTerminalFactor_nonneg T M)) hC).mp
  rw [mul_pow,Real.sq_sqrt (by positivity)]
  have hh := mul_le_mul_of_nonneg_left hbudget hC
  nlinarith only [hh]

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

theorem filterRayleigh_nonneg (A : X →L[ℝ] X) (hA : ∀ x, 0 ≤ inner ℝ (A x) x)
    (F : Submodule ℝ X) : 0 ≤ filterRayleigh A F := by
  by_cases hF : F = ⊥
  · rw [hF,filterRayleigh_bot]
  · obtain ⟨x,hx,hx0⟩ := F.ne_bot_iff.mp hF
    have hr : 0 ≤ rayleigh A.toLinearMap x := div_nonneg (hA x) (sq_nonneg _)
    exact hr.trans (rayleigh_le_filterRayleigh A F x hx hx0)

theorem filterConstant_ge_one (T M Λ : ℝ) (hT : 0 ≤ T) (hM : 0 ≤ M) (hΛ : 0 ≤ Λ) :
    1 ≤ filterConstant T M Λ := Real.one_le_exp_iff.mpr (by
      exact add_nonneg (add_nonneg (mul_nonneg hT hΛ) (mul_nonneg hM hT))
        (div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (by norm_num)))

theorem complementaryPenalty_le (ε L K : ℝ) (hε : 0 ≤ ε) (hK : 1 ≤ K) :
    complementaryPenalty ε L K ≤ ε*Real.sqrt (1+2*L^2)*K := by
  have hroot : Real.sqrt (1+2*L^2*K^2) ≤ Real.sqrt (1+2*L^2)*K := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (zero_le_one.trans hK))).mp
    rw [Real.sq_sqrt (by positivity),mul_pow,Real.sq_sqrt (by positivity)]
    nlinarith only [sq_nonneg (K-1),hK]
  have hh := mul_le_mul_of_nonneg_left hroot hε
  simpa only [complementaryPenalty,mul_assoc] using hh

theorem filter_penalty_decay (T M Λ θ d S : ℝ) (hT : 0 ≤ T) (hM : 0 ≤ M) (hΛ0 : 0 ≤ Λ)
    (hΛ : T*Λ ≤ θ*d*S) :
    complementaryPenalty (Real.exp (-d*S)) (Real.exp (2*M*T)) (filterConstant T M Λ) ≤
      Real.sqrt (1+2*(Real.exp (2*M*T))^2)*Real.exp (M*T+M^2*T^2/2)*
        Real.exp (-(1-θ)*d*S) := by
  have hh := complementaryPenalty_le (Real.exp (-d*S)) (Real.exp (2*M*T)) (filterConstant T M Λ)
    (Real.exp_pos _).le (filterConstant_ge_one T M Λ hT hM hΛ0)
  have he : Real.exp (-d*S)*filterConstant T M Λ ≤
      Real.exp (M*T+M^2*T^2/2)*Real.exp (-(1-θ)*d*S) := by
    rw [filterConstant,← Real.exp_add,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hΛ]
  have hmul := mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg (1+2*(Real.exp (2*M*T))^2))
  exact hh.trans (by nlinarith only [hmul])

end Carleman.Physical
