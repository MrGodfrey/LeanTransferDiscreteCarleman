module

public import Carleman.Control.RayleighStep
public import Mathlib.Algebra.QuadraticDiscriminant

/-! The spectral lower bound needed for Lemma 7.4, proved directly from
the positive quadratic form, without choosing an eigenbasis. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1200000
namespace Carleman.Physical
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

theorem positive_form_cauchy (B : X →ₗ[ℝ] X) (hBs : B.IsSymmetric)
    (hB : ∀ x, 0 ≤ inner ℝ (B x) x) (x y : X) :
    (inner ℝ (B x) y)^2 ≤ inner ℝ (B x) x*inner ℝ (B y) y := by
  have hh (t : ℝ) : 0 ≤ inner ℝ (B x) x*(t*t)+
      (2*inner ℝ (B x) y)*t+inner ℝ (B y) y := by
    have hp := hB (t • x+y)
    simp only [map_add,map_smul,inner_add_left,inner_add_right,
      real_inner_smul_left,real_inner_smul_right] at hp
    rw [hBs y x,real_inner_comm (B x) y] at hp
    nlinarith only [hp]
  have hd := discrim_le_zero hh
  unfold discrim at hd
  nlinarith only [hd]

theorem positive_resolvent_lower (dt : ℝ) (hdt : 0 ≤ dt)
    (A : X →ₗ[ℝ] X) (hAs : A.IsSymmetric) (hA : ∀ x, 0 ≤ inner ℝ (A x) x)
    (x y : X) (hx : x ≠ 0) (hy : step dt A y = x) :
    ‖x‖ ≤ (1+dt*rayleigh A x)*‖y‖ := by
  have hBs : (step dt A).IsSymmetric := LinearMap.IsSymmetric.id.add (hAs.smul rfl)
  have hB (z : X) : 0 ≤ inner ℝ (step dt A z) z := by
    rw [step_apply,inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq]
    exact add_nonneg (sq_nonneg _) (mul_nonneg hdt (hA z))
  have hc := positive_form_cauchy (step dt A) hBs hB y x
  rw [hy,real_inner_self_eq_norm_sq] at hc
  have hn := real_inner_le_norm x y
  have hb := mul_le_mul_of_nonneg_right hn (hB x)
  have hbx : inner ℝ (step dt A x) x = ‖x‖^2+dt*inner ℝ (A x) x := by
    rw [step_apply,inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq]
  rw [hbx] at hc hb
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have he : ‖x‖*‖y‖*(‖x‖^2+dt*inner ℝ (A x) x) =
      ‖x‖^3*((1+dt*rayleigh A x)*‖y‖) := by
    unfold rayleigh
    field_simp
  have hh : ‖x‖^3*‖x‖ ≤ ‖x‖^3*((1+dt*rayleigh A x)*‖y‖) := by
    rw [← he]
    nlinarith only [hc,hb]
  exact (mul_le_mul_iff_right₀ (pow_pos hxnorm 3)).mp hh

/-- The norm-ratio step uses the quotient of the incoming value x. -/
theorem perturbed_resolvent_lower [FiniteDimensional ℝ X]
    (dt M : ℝ) (hdt : 0 ≤ dt) (_hM : 0 ≤ M)
    (A V : X →ₗ[ℝ] X) (hAs : A.IsSymmetric) (hA : ∀ x, 0 ≤ inner ℝ (A x) x)
    (hV : ∀ x, ‖V x‖ ≤ M*‖x‖) (x z : X) (hx : x ≠ 0) (hz : step dt (A+V) z = x) :
    ‖x‖ ≤ (1+dt*M)*(1+dt*rayleigh A x)*‖z‖ := by
  have hA0 (v : X) : -(0:ℝ)*‖v‖^2 ≤ inner ℝ (A v) v := by simpa only [neg_zero,zero_mul] using hA v
  let E := LinearEquiv.ofBijective (step dt A) (step_bijective dt 0 hdt (by simp) A hA0)
  let y := E.symm x
  let w := E.symm (V z)
  have hy : step dt A y = x := E.apply_symm_apply x
  have hw : step dt A w = V z := E.apply_symm_apply (V z)
  have hwy : y = z+dt • w := by
    apply E.injective
    change step dt A y = step dt A (z+dt • w)
    rw [hy,map_add,map_smul,hw,← hz]
    simp only [step_apply,LinearMap.add_apply,smul_add]
    abel
  have hSw : ‖w‖ ≤ ‖V z‖ := by
    have hh := step_norm_lower dt 0 hdt A hA0 w
    simpa only [mul_zero,sub_zero,one_mul,hw] using hh
  have hn := norm_add_le z (dt • w)
  rw [← hwy,norm_smul,Real.norm_eq_abs,abs_of_nonneg hdt] at hn
  have hwybound : ‖y‖ ≤ (1+dt*M)*‖z‖ := by
    have hh := mul_le_mul_of_nonneg_left (hSw.trans (hV z)) hdt
    nlinarith only [hn,hh]
  have hr : 0 ≤ 1+dt*rayleigh A x := add_nonneg zero_le_one (mul_nonneg hdt (rayleigh_nonneg A hA x))
  have hh := (positive_resolvent_lower dt hdt A hAs hA x y hx hy).trans
    (mul_le_mul_of_nonneg_left hwybound hr)
  nlinarith only [hh]

end Carleman.Physical
