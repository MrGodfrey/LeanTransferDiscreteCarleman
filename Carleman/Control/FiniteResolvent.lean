module

public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! The physical, nonperiodic backward-Euler step on the full state space. -/
@[expose] public noncomputable section
namespace Carleman.Physical
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- One physical step, before imposing either the initial or terminal datum. -/
def step (dt : ℝ) (L : X →ₗ[ℝ] X) : X →ₗ[ℝ] X := LinearMap.id + dt • L

theorem step_apply (dt : ℝ) (L : X →ₗ[ℝ] X) (x : X) :
    step dt L x = x+dt • L x := rfl

theorem one_sub_mul_exp_ge_one {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1/2) :
    1 ≤ (1-r)*Real.exp (2*r) := by
  have he := Real.add_one_le_exp (2*r)
  have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 1-r by linarith)
  nlinarith [mul_nonneg hr (show 0 ≤ 1-2*r by linarith)]

theorem step_norm_lower (dt M : ℝ) (hdt : 0 ≤ dt)
    (L : X →ₗ[ℝ] X) (hL : ∀ x, -M*‖x‖^2 ≤ inner ℝ (L x) x) (x : X) :
    (1-dt*M)*‖x‖ ≤ ‖step dt L x‖ := by
  change (1-dt*M)*‖x‖ ≤ ‖x+dt • L x‖
  have hl := mul_le_mul_of_nonneg_left (hL x) hdt
  have hc := real_inner_le_norm (step dt L x) x
  rw [step_apply,inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq] at hc
  by_cases hx : ‖x‖ = 0
  · simp only [hx,mul_zero]; exact norm_nonneg _
  · have hp : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
    nlinarith

theorem step_inverse_bound (dt M : ℝ) (hdt : 0 ≤ dt) (hM : 0 ≤ M) (hsmall : dt*M ≤ 1/2)
    (L : X →ₗ[ℝ] X) (hL : ∀ x, -M*‖x‖^2 ≤ inner ℝ (L x) x) (x : X) :
    ‖x‖ ≤ Real.exp (2*dt*M)*‖step dt L x‖ := by
  have hh := step_norm_lower dt M hdt L hL x
  have he := one_sub_mul_exp_ge_one (mul_nonneg hdt hM) hsmall
  have hp := Real.exp_pos (2*dt*M)
  have hm := mul_le_mul_of_nonneg_left hh hp.le
  have hx := mul_le_mul_of_nonneg_right he (norm_nonneg x)
  rw [show 2*(dt*M) = 2*dt*M by ring] at hx
  nlinarith only [hm,hx]

theorem step_bijective [FiniteDimensional ℝ X] (dt M : ℝ)
    (hdt : 0 ≤ dt) (hsmall : dt*M ≤ 1/2)
    (L : X →ₗ[ℝ] X) (hL : ∀ x, -M*‖x‖^2 ≤ inner ℝ (L x) x) :
    Function.Bijective (step dt L) := by
  have hi : Function.Injective (step dt L) := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have hh := step_norm_lower dt M hdt L hL x
    rw [hx,norm_zero] at hh
    have hp : 0 < 1-dt*M := by linarith
    have hn : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
    exact norm_eq_zero.mp hn
  exact ⟨hi,LinearMap.surjective_of_injective hi⟩

/-- Original nonnegative stiffness plus a norm-bounded potential supplies
exactly the quadratic lower bound used by the resolvent. -/
theorem stiffness_potential_lower (A V : X →ₗ[ℝ] X) (M : ℝ)
    (hA : ∀ x, 0 ≤ inner ℝ (A x) x) (hV : ∀ x, ‖V x‖ ≤ M*‖x‖) (x : X) :
    -M*‖x‖^2 ≤ inner ℝ ((A+V) x) x := by
  have hh := (abs_le.mp (abs_real_inner_le_norm (V x) x)).1
  have hb := mul_le_mul_of_nonneg_right (hV x) (norm_nonneg x)
  simp only [LinearMap.add_apply,inner_add_left]
  nlinarith only [hh,hb,hA x]

end Carleman.Physical
