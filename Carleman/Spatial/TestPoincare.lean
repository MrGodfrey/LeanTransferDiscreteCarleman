module

public import Carleman.Spatial.SpatialTestSobolev

/-! Poincare's inequality for actual compactly supported smooth functions
in a slab. The estimate follows from the exact weak integration identity. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SpatialTest
variable {d : ℕ} {S : Set (SpatialCoordinates d)} (φ : SpatialTest S)

def linearMul (L : SpatialCoordinates d →L[ℝ] ℝ) : SpatialTest S where
  value x := L x * φ.value x
  smooth := L.contDiff.mul φ.smooth
  compact := φ.compact.mul_left
  support := tsupport_mul_subset_right.trans φ.support

theorem linearMul_derivative (L : SpatialCoordinates d →L[ℝ] ℝ)
    (e x : SpatialCoordinates d) :
    fderiv ℝ (φ.linearMul L).value x e = L e * φ.value x + L x * fderiv ℝ φ.value x e := by
  have hh := (L.hasFDerivAt (x := x)).mul
    ((φ.smooth.differentiable (by simp)).differentiableAt.hasFDerivAt)
  change (fderiv ℝ ((L : SpatialCoordinates d → ℝ) * φ.value) x) e = _
  rw [hh.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

theorem weakDerivative (e : SpatialCoordinates d) :
    IsWeakSpatialDerivative (volume.restrict S) S e
      (φ.toLp (volume.restrict S)) (φ.derivativeLp (volume.restrict S) e) := by
  obtain ⟨C,hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport φ.compact φ.smooth (by simp)
  apply weakSpatialDerivative_of_lipschitz hC _ _ _ (φ.toLp_ae _)
  filter_upwards [φ.derivativeLp_ae (volume.restrict S) e] with x hx
  exact hx.trans ((φ.smooth.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv).symm

theorem linearMul_norm_le (hS : IsOpen S) (L : SpatialCoordinates d →L[ℝ] ℝ)
    {R : ℝ} (hR : ∀ x ∈ S, |L x| ≤ R) :
    ‖(φ.linearMul L).toLp (volume.restrict S)‖ ≤ R * ‖φ.toLp (volume.restrict S)‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(φ.linearMul L).toLp_ae (volume.restrict S),φ.toLp_ae (volume.restrict S),
    ae_restrict_mem hS.measurableSet] with x hx hy hxs
  rw [hx,hy]
  change ‖L x * φ.value x‖ ≤ _
  rw [norm_mul,Real.norm_eq_abs (L x)]
  exact mul_le_mul_of_nonneg_right (hR x hxs) (norm_nonneg _)

theorem poincare_slab (hS : IsOpen S) (L : SpatialCoordinates d →L[ℝ] ℝ)
    (e : SpatialCoordinates d) (he : L e = 1) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ x ∈ S, |L x| ≤ R) :
    ‖φ.toLp (volume.restrict S)‖ ≤ 2*R*‖φ.derivativeLp (volume.restrict S) e‖ := by
  let u := φ.toLp (volume.restrict S)
  let v := φ.derivativeLp (volume.restrict S) e
  let ψ := φ.linearMul L
  let w := ψ.toLp (volume.restrict S)
  have identity : inner ℝ u (ψ.derivativeLp (volume.restrict S) e) =
      inner ℝ u u + inner ℝ v w := by
    simp only [L2.inner_def]
    rw [← integral_add (L2.integrable_inner u u) (L2.integrable_inner v w)]
    apply integral_congr_ae
    filter_upwards [φ.toLp_ae (volume.restrict S),φ.derivativeLp_ae (volume.restrict S) e,
      ψ.toLp_ae (volume.restrict S),ψ.derivativeLp_ae (volume.restrict S) e] with x hu hv hw hd
    dsimp only [u,v,w]
    rw [hu,hv,hw,hd]
    change (fderiv ℝ (φ.linearMul L).value x e) * φ.value x =
      φ.value x * φ.value x + (L x * φ.value x) * fderiv ℝ φ.value x e
    rw [φ.linearMul_derivative,he]
    ring
  have weak := φ.weakDerivative e ψ
  change inner ℝ u (ψ.derivativeLp (volume.restrict S) e) = -inner ℝ v w at weak
  rw [identity,real_inner_self_eq_norm_sq] at weak
  have bound := φ.linearMul_norm_le hS L hR
  change ‖w‖ ≤ R*‖u‖ at bound
  have cs := abs_real_inner_le_norm v w
  have lower := neg_abs_le (inner ℝ v w)
  have major : ‖v‖*‖w‖ ≤ ‖v‖*(R*‖u‖) := mul_le_mul_of_nonneg_left bound (norm_nonneg _)
  by_cases hz : ‖u‖ = 0
  · rw [hz]
    positivity
  · have hp : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

end Carleman.SpatialTest
