module

public import Carleman.Control.PenalizedHUM
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! Actual complementary orthogonal penalty: the retained terminal component vanishes exactly. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1200000
namespace Carleman.Physical
variable {X U : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

def complementaryHumOperator (O : X →L[ℝ] U) (F : Submodule ℝ X) (η : ℝ) : X →L[ℝ] X :=
  O.adjoint.comp O+η^2 • Fᗮ.starProjection

theorem complementaryHumOperator_pairing (O : X →L[ℝ] U) (F : Submodule ℝ X) (η : ℝ) (x y : X) :
    inner ℝ (complementaryHumOperator O F η x) y =
      inner ℝ (O x) (O y)+η^2*inner ℝ (Fᗮ.starProjection x) (Fᗮ.starProjection y) := by
  have hid : Fᗮ.starProjection (Fᗮ.starProjection x) = Fᗮ.starProjection x :=
    Submodule.starProjection_eq_self_iff.mpr (Fᗮ.starProjection_apply_mem x)
  have he := Fᗮ.inner_starProjection_left_eq_right (Fᗮ.starProjection x) y
  rw [hid] at he
  simp only [complementaryHumOperator,add_apply,smul_apply,ContinuousLinearMap.comp_apply,
    inner_add_left,real_inner_smul_left,O.adjoint_inner_left,he]

theorem complementaryHumOperator_bijective (R : X →L[ℝ] X) (O : X →L[ℝ] U)
    (F : Submodule ℝ X) (η C : ℝ) (hR : Function.Injective R)
    (hobs : ∀ z, ‖R z‖^2 ≤ C*(‖O z‖^2+η^2*‖Fᗮ.starProjection z‖^2)) :
    Function.Bijective (complementaryHumOperator O F η) := by
  have hi : Function.Injective (complementaryHumOperator O F η).toLinearMap := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have hh := complementaryHumOperator_pairing O F η x x
    change complementaryHumOperator O F η x = 0 at hx
    rw [hx,inner_zero_left,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hh
    have ho := hobs x
    rw [← hh,mul_zero] at ho
    have hz : R x = 0 := norm_eq_zero.mp (by nlinarith only [ho,norm_nonneg (R x)])
    exact hR (hz.trans (R.map_zero).symm)
  exact ⟨hi,LinearMap.surjective_of_injective hi⟩

theorem complementary_hum_optimality (R : X →L[ℝ] X) (O : X →L[ℝ] U)
    (F : Submodule ℝ X) (η C : ℝ) (hR : Function.Injective R)
    (hobs : ∀ z, ‖R z‖^2 ≤ C*(‖O z‖^2+η^2*‖Fᗮ.starProjection z‖^2)) (y : X) :
    ∃! z : X, ∀ v : X,
      inner ℝ (O z) (O v)+η^2*inner ℝ (Fᗮ.starProjection z) (Fᗮ.starProjection v) =
        inner ℝ y (R v) := by
  have hb := complementaryHumOperator_bijective R O F η C hR hobs
  obtain ⟨z,hz⟩ := hb.2 (R.adjoint y)
  have he (v : X) :
      inner ℝ (O z) (O v)+η^2*inner ℝ (Fᗮ.starProjection z) (Fᗮ.starProjection v) =
        inner ℝ y (R v) := by
    rw [← complementaryHumOperator_pairing,hz,R.adjoint_inner_left]
  refine ⟨z,he,?_⟩
  intro w hw
  apply hb.1
  apply ext_inner_right ℝ
  intro v
  rw [complementaryHumOperator_pairing,complementaryHumOperator_pairing,hw,he]

theorem complementary_hum_control (R : X →L[ℝ] X) (O : X →L[ℝ] U) (F : Submodule ℝ X) (ε C : ℝ)
    (hε : 0 < ε) (hC : 0 ≤ C) (hR : Function.Injective R)
    (hobs : ∀ z, ‖R z‖^2 ≤ C*(‖O z‖^2+ε^2*‖Fᗮ.starProjection z‖^2)) (y : X) :
    ∃ u : U, ‖u‖ ≤ Real.sqrt C*‖y‖ ∧
      F.starProjection (R.adjoint y+O.adjoint u) = 0 ∧
      ‖R.adjoint y+O.adjoint u‖ ≤ ε*Real.sqrt C*‖y‖ := by
  obtain ⟨z,hz,_⟩ := complementary_hum_optimality R O F ε C hR hobs y
  let Q := ‖O z‖^2+ε^2*‖Fᗮ.starProjection z‖^2
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
    nlinarith [mul_nonneg (sq_nonneg ε) (sq_nonneg ‖Fᗮ.starProjection z‖)]
  have hqz : ε*‖Fᗮ.starProjection z‖ ≤ Real.sqrt C*‖y‖ := by
    apply (sq_le_sq₀ (mul_nonneg hε.le (norm_nonneg _))
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [hroot,mul_pow]
    dsimp only [Q] at henergy
    nlinarith [sq_nonneg ‖O z‖]
  have heq : R.adjoint y+O.adjoint (-O z) = ε^2 • Fᗮ.starProjection z := by
    apply ext_inner_right ℝ
    intro v
    rw [inner_add_left,map_neg,inner_neg_left,R.adjoint_inner_left,O.adjoint_inner_left,real_inner_smul_left]
    have hid : Fᗮ.starProjection (Fᗮ.starProjection z) = Fᗮ.starProjection z :=
      Submodule.starProjection_eq_self_iff.mpr (Fᗮ.starProjection_apply_mem z)
    have he := Fᗮ.inner_starProjection_left_eq_right (Fᗮ.starProjection z) v
    rw [hid] at he
    rw [he]
    linarith only [hz v]
  refine ⟨-O z,by simpa only [norm_neg] using hqO,?_,?_⟩
  · rw [heq,map_smul]
    have hzF : F.starProjection (Fᗮ.starProjection z) = 0 :=
      F.starProjection_apply_eq_zero_iff.mpr (Fᗮ.starProjection_apply_mem z)
    rw [hzF,smul_zero]
  · rw [heq,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ε)]
    have hh := mul_le_mul_of_nonneg_left hqz hε.le
    nlinarith only [hh]

end Carleman.Physical
