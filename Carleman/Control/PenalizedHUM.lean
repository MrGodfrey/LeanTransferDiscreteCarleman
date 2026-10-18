module

public import Carleman.Control.PhysicalFlow

/-! Finite-dimensional penalized HUM from a relaxed observation estimate.
This is an auxiliary conditional implication; it does not supply Theorem 7.2. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1200000
namespace Carleman.Physical
variable {X U : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

def humOperator (O : X →L[ℝ] U) (ε : ℝ) : X →L[ℝ] X := O.adjoint.comp O+ε^2 • ContinuousLinearMap.id ℝ X

theorem humOperator_pairing (O : X →L[ℝ] U) (ε : ℝ) (x y : X) :
    inner ℝ (humOperator O ε x) y = inner ℝ (O x) (O y)+ε^2*inner ℝ x y := by
  simp only [humOperator,add_apply,smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,inner_add_left,real_inner_smul_left]
  rw [O.adjoint_inner_left]

theorem humOperator_bijective (O : X →L[ℝ] U) (ε : ℝ) (hε : 0 < ε) :
    Function.Bijective (humOperator O ε) := by
  have hi : Function.Injective (humOperator O ε).toLinearMap := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro x hx
    change humOperator O ε x = 0 at hx
    have hh := humOperator_pairing O ε x x
    change inner ℝ (humOperator O ε x) x = _ at hh
    rw [hx,inner_zero_left,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hh
    have hp : 0 < ε^2 := sq_pos_of_pos hε
    have hle : ε^2*‖x‖^2 ≤ 0 := by nlinarith only [hh,sq_nonneg ‖O x‖]
    have hn : ‖x‖ = 0 := by
      by_contra hn
      have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hn)
      exact (not_lt_of_ge hle) (mul_pos hp (sq_pos_of_pos hxpos))
    exact norm_eq_zero.mp hn
  exact ⟨hi,LinearMap.surjective_of_injective hi⟩

theorem hum_optimality (R : X →L[ℝ] X) (O : X →L[ℝ] U) (ε : ℝ) (hε : 0 < ε) (y : X) :
    ∃! z : X, ∀ v : X, inner ℝ (O z) (O v)+ε^2*inner ℝ z v = inner ℝ y (R v) := by
  have hb := humOperator_bijective O ε hε
  obtain ⟨z,hz⟩ := hb.2 (R.adjoint y)
  have he (v : X) : inner ℝ (O z) (O v)+ε^2*inner ℝ z v = inner ℝ y (R v) := by
    rw [← humOperator_pairing,hz,R.adjoint_inner_left]
  refine ⟨z,he,?_⟩
  intro w hw
  apply hb.1
  apply ext_inner_right ℝ
  intro v
  rw [humOperator_pairing,humOperator_pairing,hw,he]

theorem penalized_hum_control (R : X →L[ℝ] X) (O : X →L[ℝ] U) (ε C : ℝ)
    (hε : 0 < ε) (hC : 0 ≤ C)
    (hobs : ∀ z, ‖R z‖^2 ≤ C*(‖O z‖^2+ε^2*‖z‖^2)) (y : X) :
    ∃ u : U, ‖u‖ ≤ Real.sqrt C*‖y‖ ∧
      ‖R.adjoint y+O.adjoint u‖ ≤ ε*Real.sqrt C*‖y‖ := by
  obtain ⟨z,hz,_⟩ := hum_optimality R O ε hε y
  let Q := ‖O z‖^2+ε^2*‖z‖^2
  have hQ : 0 ≤ Q := add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hpair : Q = inner ℝ y (R z) := by
    simpa only [real_inner_self_eq_norm_sq] using hz z
  have hle : Q ≤ ‖y‖*‖R z‖ := hpair.le.trans (real_inner_le_norm y (R z))
  have hs : Q^2 ≤ (‖y‖*‖R z‖)^2 := (sq_le_sq₀ hQ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hle
  have ho := mul_le_mul_of_nonneg_left (hobs z) (sq_nonneg ‖y‖)
  have henergy : Q ≤ C*‖y‖^2 := by
    change ‖y‖^2*‖R z‖^2 ≤ ‖y‖^2*(C*Q) at ho
    have hprod : Q*(Q-C*‖y‖^2) ≤ 0 := by nlinarith only [hs,ho]
    by_contra hn
    have hlt : C*‖y‖^2 < Q := lt_of_not_ge hn
    have hp : 0 < Q := lt_of_le_of_lt (mul_nonneg hC (sq_nonneg _)) hlt
    exact (not_lt_of_ge hprod) (mul_pos hp (sub_pos.mpr hlt))
  have hroot : (Real.sqrt C*‖y‖)^2 = C*‖y‖^2 := by rw [mul_pow,Real.sq_sqrt hC]
  have hqO : ‖O z‖ ≤ Real.sqrt C*‖y‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [hroot]
    dsimp only [Q] at henergy
    nlinarith [mul_nonneg (sq_nonneg ε) (sq_nonneg ‖z‖)]
  have hqz : ε*‖z‖ ≤ Real.sqrt C*‖y‖ := by
    apply (sq_le_sq₀ (mul_nonneg hε.le (norm_nonneg _))
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [hroot,mul_pow]
    dsimp only [Q] at henergy
    nlinarith [sq_nonneg ‖O z‖]
  have heq : R.adjoint y+O.adjoint (-O z) = ε^2 • z := by
    apply ext_inner_right ℝ
    intro v
    rw [inner_add_left,map_neg,inner_neg_left,R.adjoint_inner_left,O.adjoint_inner_left,real_inner_smul_left]
    linarith only [hz v]
  refine ⟨-O z,by simpa only [norm_neg] using hqO,?_⟩
  rw [heq,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ε)]
  have hh := mul_le_mul_of_nonneg_left hqz hε.le
  nlinarith only [hh]

end Carleman.Physical
