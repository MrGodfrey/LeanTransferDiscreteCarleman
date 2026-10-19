module

public import Carleman.Control.ComplementaryHUM

/-! The actual orthogonal complementary penalty, with constants independent of the retained subspace. -/
@[expose] public noncomputable section
namespace Carleman.Physical

def complementaryPenalty (ε L K : ℝ) : ℝ := ε*Real.sqrt (1+2*L^2*K^2)

theorem complementaryPenalty_sq (ε L K : ℝ) :
    (complementaryPenalty ε L K)^2 = ε^2*(1+2*L^2*K^2) := by
  rw [complementaryPenalty,mul_pow,Real.sq_sqrt (by positivity)]

theorem complementaryPenalty_pos (ε L K : ℝ) (hε : 0 < ε) :
    0 < complementaryPenalty ε L K := mul_pos hε (Real.sqrt_pos.mpr (by positivity))

variable {X U : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

theorem complementary_terminal_bound (R : X →L[ℝ] X) (F : Submodule ℝ X)
    (L K : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hR : ∀ x, ‖R x‖ ≤ L*‖x‖) (hrev : ∀ x ∈ F, ‖x‖ ≤ K*‖R x‖) (z : X) :
    ‖z‖^2 ≤ 2*K^2*‖R z‖^2+(1+2*L^2*K^2)*‖Fᗮ.starProjection z‖^2 := by
  let p := F.starProjection z
  let q := Fᗮ.starProjection z
  have hrp : R p = R z-R q := by
    rw [← map_sub]
    congr 1
    change F.starProjection z = z-Fᗮ.starProjection z
    rw [Submodule.starProjection_orthogonal_val]
    abel
  have hr : ‖R p‖ ≤ ‖R z‖+L*‖q‖ := by
    rw [hrp]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl (hR q))
  have hp : ‖p‖ ≤ K*(‖R z‖+L*‖q‖) :=
    (hrev p (F.starProjection_apply_mem z)).trans (mul_le_mul_of_nonneg_left hr hK)
  have hs := (sq_le_sq₀ (norm_nonneg p)
    (mul_nonneg hK (add_nonneg (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))))).mpr hp
  have he : ‖z‖^2 = ‖p‖^2+‖q‖^2 := Submodule.norm_sq_eq_add_norm_sq_starProjection z F
  have hcross := mul_nonneg (sq_nonneg K) (sq_nonneg (‖R z‖-L*‖q‖))
  change ‖z‖^2 ≤ 2*K^2*‖R z‖^2+(1+2*L^2*K^2)*‖q‖^2
  nlinarith only [hs,he,hcross]

theorem complementary_observation_of_relaxed (R : X →L[ℝ] X) (O : X →L[ℝ] U)
    (F : Submodule ℝ X) (ε C0 L K : ℝ) (hC : 0 ≤ C0) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hR : ∀ x, ‖R x‖ ≤ L*‖x‖) (hrev : ∀ x ∈ F, ‖x‖ ≤ K*‖R x‖)
    (hobs : ∀ x, ‖R x‖^2 ≤ C0*(‖O x‖^2+ε^2*‖x‖^2))
    (hbudget : 4*C0*ε^2*K^2 ≤ 1) (z : X) :
    ‖R z‖^2 ≤ 2*C0*(‖O z‖^2+(complementaryPenalty ε L K)^2*‖Fᗮ.starProjection z‖^2) := by
  have hz := complementary_terminal_bound R F L K hL hK hR hrev z
  have h1 := mul_le_mul_of_nonneg_left hz (mul_nonneg hC (sq_nonneg ε))
  have h2 := mul_le_mul_of_nonneg_right hbudget (sq_nonneg ‖R z‖)
  have ho := hobs z
  rw [complementaryPenalty_sq]
  nlinarith only [h1,h2,ho]

end Carleman.Physical
