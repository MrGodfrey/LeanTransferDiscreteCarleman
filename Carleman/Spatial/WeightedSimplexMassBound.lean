module

public import Carleman.Spatial.SimplexMassIntegral

/-! Actual weighted simplex polynomial integrals controlled by nodal coefficient energy. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} (T : Affine.Simplex ℝ (SpatialCoordinates d) d)

theorem weighted_simplexNodal_integrable (w : BoundedMultiplier (volume.restrict (simplicialCell T.points)))
    (c : Fin (d+1) → ℝ) :
    Integrable (fun x => |w.value x|^2*(simplexNodalInterpolant T c x)^2)
      (volume.restrict (simplicialCell T.points)) := by
  apply (w.integrable_density (simplexNodalLp T c)).congr
  filter_upwards [simplexNodalLp_ae T c] with x hx
  simp only [hx,Real.norm_eq_abs,sq_abs]

theorem weighted_simplexNodal_coefficient_bound
    (w : BoundedMultiplier (volume.restrict (simplicialCell T.points)))
    (c : Fin (d+1) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᵐ x ∂volume.restrict (simplicialCell T.points), |w.value x| ≤ B) :
    (∫ x in simplicialCell T.points, |w.value x|^2*(simplexNodalInterpolant T c x)^2) ≤
      B^2*(d+2)*volume.real (simplicialCell T.points)/((d+1:ℝ)*(d+2))*(∑ i, (c i)^2) := by
  have hi : Integrable (fun x => B^2*(simplexNodalInterpolant T c x)^2)
      (volume.restrict (simplicialCell T.points)) :=
    (continuous_const.mul ((simplexNodalInterpolant T c).continuous_of_finiteDimensional.pow 2)).continuousOn.integrableOn_compact
      (simplicialCell_compact _)
  calc
    _ ≤ ∫ x in simplicialCell T.points, B^2*(simplexNodalInterpolant T c x)^2 := by
      apply integral_mono_ae (weighted_simplexNodal_integrable T w c) hi
      filter_upwards [hb] with x hx
      exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (abs_nonneg _) hB).mpr hx) (sq_nonneg _)
    _ = B^2*(∫ x in simplicialCell T.points, (simplexNodalInterpolant T c x)^2) := integral_const_mul _ _
    _ ≤ B^2*(volume.real (simplicialCell T.points)/((d+1:ℝ)*(d+2))*(d+2)*(∑ i, (c i)^2)) :=
      mul_le_mul_of_nonneg_left (integral_simplexNodalInterpolant_sq_bounds T c).2 (sq_nonneg B)
    _ = _ := by ring

theorem weighted_simplex_state_bound
    (w : BoundedMultiplier (volume.restrict (simplicialCell T.points)))
    (c ω : Fin (d+1) → ℝ) {θ a : ℝ} (hθ : 0 < θ) (ha : 0 < a)
    (hω : ∀ i, a/θ ≤ ω i)
    (hb : ∀ᵐ x ∂volume.restrict (simplicialCell T.points), |w.value x| ≤ θ*a) :
    (∫ x in simplicialCell T.points, |w.value x|^2*(simplexNodalInterpolant T c x)^2) ≤
      θ^4*(d+2)*(volume.real (simplicialCell T.points)/((d+1:ℝ)*(d+2))*
        (∑ i, (ω i*c i)^2)) := by
  have hs : a^2*(∑ i, (c i)^2) ≤ θ^2*(∑ i, (ω i*c i)^2) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hw := (div_le_iff₀ hθ).mp (hω i)
    have hp : 0 ≤ θ*ω i := ha.le.trans (by simpa only [mul_comm] using hw)
    have hh := (sq_le_sq₀ ha.le hp).mpr (by simpa only [mul_comm] using hw)
    have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg (c i))
    simpa only [mul_pow,mul_assoc] using hh'
  have h := weighted_simplexNodal_coefficient_bound T w c (mul_nonneg hθ.le ha.le) hb
  apply h.trans
  have hh := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ θ^2*(d+2)*(volume.real (simplicialCell T.points)/((d+1:ℝ)*(d+2))) by positivity)
  convert hh using 1 <;> ring

theorem weighted_simplex_test_bound
    (w : BoundedMultiplier (volume.restrict (simplicialCell T.points)))
    (c ω : Fin (d+1) → ℝ) {θ a : ℝ} (hθ : 0 < θ) (ha : 0 < a)
    (hω : ∀ i, 0 ≤ ω i) (hωa : ∀ i, ω i ≤ a)
    (hb : ∀ᵐ x ∂volume.restrict (simplicialCell T.points), |w.value x| ≤ θ/a) :
    (∫ x in simplicialCell T.points, |w.value x|^2*
      (simplexNodalInterpolant T (fun i => (ω i)^2*c i) x)^2) ≤
      θ^2*(d+2)*(volume.real (simplicialCell T.points)/((d+1:ℝ)*(d+2))*
        (∑ i, (ω i*c i)^2)) := by
  have hs : (∑ i, ((ω i)^2*c i)^2) ≤ a^2*(∑ i, (ω i*c i)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hh := mul_le_mul_of_nonneg_right ((sq_le_sq₀ (hω i) ha.le).mpr (hωa i))
      (sq_nonneg (ω i*c i))
    convert hh using 1
    ring
  have h := weighted_simplexNodal_coefficient_bound T w (fun i => (ω i)^2*c i)
    (div_nonneg hθ.le ha.le) hb
  apply h.trans
  have hh := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ (θ/a)^2*(d+2)*(volume.real (simplicialCell T.points)/((d+1:ℝ)*(d+2))) by positivity)
  convert hh using 1
  · ring
  · field_simp

end Carleman
