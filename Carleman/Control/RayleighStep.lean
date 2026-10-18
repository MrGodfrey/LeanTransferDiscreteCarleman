module

public import Carleman.Control.PhysicalLemma

/-! One-step Rayleigh growth from the original nonnegative stiffness and
bounded self-adjoint potential. Auxiliary development for Lemma 7.4. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1000000
namespace Carleman.Physical
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

def rayleigh (A : X →ₗ[ℝ] X) (x : X) : ℝ := inner ℝ (A x) x/‖x‖^2

theorem rayleigh_nonneg (A : X →ₗ[ℝ] X) (hA : ∀ x, 0 ≤ inner ℝ (A x) x) (x : X) :
    0 ≤ rayleigh A x := div_nonneg (hA x) (sq_nonneg _)

/-- The normalized algebraic inequality underlying the original quotient step. -/
theorem rayleigh_step_normalized (dt M : ℝ) (hdt : 0 ≤ dt) (hM : 0 ≤ M)
    (hsmall : dt*M ≤ 1/2) (A V : X →ₗ[ℝ] X) (hAs : A.IsSymmetric)
    (hA : ∀ x, 0 ≤ inner ℝ (A x) x) (hV : ∀ x, ‖V x‖ ≤ M*‖x‖)
    (z : X) (hz : ‖z‖ = 1) :
    inner ℝ (A z) z * ‖step dt (A+V) z‖^2 ≤
      inner ℝ (A (step dt (A+V) z)) (step dt (A+V) z)+dt*M^2*‖step dt (A+V) z‖^2 := by
  let r := inner ℝ (A z) z
  let b := inner ℝ (V z) z
  let v := A z-r • z
  let w := V z-b • z
  let ξ := v+w
  let γ := 1+dt*(r+b)
  have hr : 0 ≤ r := hA z
  have hVz : ‖V z‖ ≤ M := by simpa only [hz,mul_one] using hV z
  have hb : -M ≤ b := by
    have hh := (abs_le.mp (abs_real_inner_le_norm (V z) z)).1
    rw [hz,mul_one] at hh
    dsimp only [b]
    linarith only [hh,hVz]
  have hv : inner ℝ v z = 0 := by simp [v,r,inner_sub_left,real_inner_smul_left,hz]
  have hw : inner ℝ w z = 0 := by simp [w,b,inner_sub_left,real_inner_smul_left,hz]
  have hξ : inner ℝ ξ z = 0 := by simp only [ξ,inner_add_left,hv,hw,add_zero]
  have hξ' : inner ℝ z ξ = 0 := (real_inner_comm z ξ).symm.trans hξ
  have hw2 : ‖w‖^2 ≤ M^2 := by
    have hh : ‖w‖^2 = ‖V z‖^2-b^2 := by
      rw [show w = V z-b • z from rfl,norm_sub_sq_real,real_inner_smul_right]
      simp only [norm_smul,Real.norm_eq_abs,hz,mul_one,sq_abs]
      dsimp only [b]
      ring
    rw [hh]
    nlinarith [norm_nonneg (V z),sq_nonneg b]
  have hγ : 0 ≤ γ := by dsimp [γ]; nlinarith [mul_nonneg hdt hr,mul_le_mul_of_nonneg_left hb hdt]
  have hD : 1 ≤ 2*γ-dt*r := by dsimp [γ]; nlinarith [mul_nonneg hdt hr,mul_le_mul_of_nonneg_left hb hdt]
  have hx : step dt (A+V) z = γ • z+dt • ξ := by
    simp only [step_apply,LinearMap.add_apply,γ,ξ,v,w,add_smul,smul_add,smul_sub,smul_smul,one_smul]
    module
  have hx2 : ‖step dt (A+V) z‖^2 = γ^2+dt^2*‖ξ‖^2 := by
    rw [hx,norm_add_sq_real,real_inner_smul_left,real_inner_smul_right,real_inner_comm,hξ]
    simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hz,mul_one,mul_zero,add_zero]
  have hAz : inner ℝ (A z) ξ = ‖ξ‖^2-inner ℝ w ξ := by
    have he : A z = ξ-w+r • z := by dsimp [ξ,v]; abel
    rw [he,inner_add_left,inner_sub_left,real_inner_smul_left,hξ',mul_zero,add_zero,real_inner_self_eq_norm_sq]
  have hAz' : inner ℝ ξ (A z) = ‖ξ‖^2-inner ℝ w ξ := (real_inner_comm ξ (A z)).symm.trans hAz
  have hAx : inner ℝ (A (step dt (A+V) z)) (step dt (A+V) z) =
      γ^2*r+2*γ*dt*(‖ξ‖^2-inner ℝ w ξ)+dt^2*inner ℝ (A ξ) ξ := by
    rw [hx]
    simp only [map_add,map_smul,inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right]
    rw [hAs ξ z,hAz,hAz']
    dsimp [r]
    ring
  have hs := sq_nonneg ‖ξ-γ • w‖
  rw [norm_sub_sq_real,real_inner_smul_right,real_inner_comm w ξ,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at hs
  have hsq : γ^2*‖w‖^2 ≤ γ^2*M^2 := mul_le_mul_of_nonneg_left hw2 (sq_nonneg γ)
  have hcomp : -γ^2*M^2 ≤ (2*γ-dt*r)*‖ξ‖^2-2*γ*inner ℝ w ξ := by
    have hpos := mul_nonneg (sub_nonneg.mpr hD) (sq_nonneg ‖ξ‖)
    nlinarith only [hs,hsq,hpos]
  have hc := mul_le_mul_of_nonneg_left hcomp hdt
  have ha := mul_nonneg (sq_nonneg dt) (hA ξ)
  have hnx : γ^2 ≤ ‖step dt (A+V) z‖^2 := by rw [hx2]; exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg dt) (sq_nonneg ‖ξ‖))
  have hm := mul_le_mul_of_nonneg_left hnx (mul_nonneg hdt (sq_nonneg M))
  rw [hAx,hx2] at *
  nlinarith only [hc,ha,hm]

theorem rayleigh_smul (A : X →ₗ[ℝ] X) (c : ℝ) (hc : c ≠ 0) (z : X) :
    rayleigh A (c • z) = rayleigh A z := by
  simp only [rayleigh,map_smul,real_inner_smul_left,real_inner_smul_right,
    norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [show c*(c*inner ℝ (A z) z) = c^2*inner ℝ (A z) z by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hc)

theorem rayleigh_step (dt M : ℝ) (hdt : 0 ≤ dt) (hM : 0 ≤ M)
    (hsmall : dt*M ≤ 1/2) (A V : X →ₗ[ℝ] X) (hAs : A.IsSymmetric)
    (hA : ∀ x, 0 ≤ inner ℝ (A x) x) (hV : ∀ x, ‖V x‖ ≤ M*‖x‖)
    (z : X) (hz : z ≠ 0) :
    rayleigh A z ≤ rayleigh A (step dt (A+V) z)+dt*M^2 := by
  let u := ‖z‖⁻¹ • z
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hc : ‖z‖⁻¹ ≠ 0 := inv_ne_zero hn
  have hu : ‖u‖ = 1 := by
    simp only [u,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg z),inv_mul_cancel₀ hn]
  have hs := step_norm_lower dt M hdt (A+V) (stiffness_potential_lower A V M hA hV) u
  rw [hu,mul_one] at hs
  have hx : 0 < ‖step dt (A+V) u‖^2 := sq_pos_of_pos (by linarith)
  have hq := rayleigh_step_normalized dt M hdt hM hsmall A V hAs hA hV u hu
  have hb : rayleigh A u ≤ rayleigh A (step dt (A+V) u)+dt*M^2 := by
    rw [rayleigh,hu,one_pow,div_one]
    calc
      inner ℝ (A u) u ≤ (inner ℝ (A (step dt (A+V) u)) (step dt (A+V) u)+
          dt*M^2*‖step dt (A+V) u‖^2)/‖step dt (A+V) u‖^2 := (le_div_iff₀ hx).mpr hq
      _ = _ := by rw [add_div,mul_div_cancel_right₀ _ (ne_of_gt hx)]; rfl
  dsimp only [u] at hb
  rw [rayleigh_smul A _ hc,map_smul,rayleigh_smul A _ hc] at hb
  exact hb

end Carleman.Physical
