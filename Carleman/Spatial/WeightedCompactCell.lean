module

public import Carleman.Spatial.WeightedSimplexMassBound

/-! Actual weighted integrals on a compact simplex compare to a positive
local anchor. These helpers do not assume a polynomial norm estimate. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} (T : Affine.Simplex ℝ (SpatialCoordinates d) d)

theorem simplex_continuous_memLp (f : SpatialCoordinates d → ℝ) (hf : Continuous f) :
    MemLp f 2 (volume.restrict (simplicialCell T.points)) := by
  obtain ⟨B,hB⟩ := (simplicialCell_compact T.points).exists_bound_of_continuousOn hf.continuousOn
  let : IsFiniteMeasure (volume.restrict (simplicialCell T.points)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (simplicialCell_compact T.points).measure_lt_top⟩
  apply MemLp.of_bound hf.aestronglyMeasurable B
  filter_upwards [ae_restrict_mem (simplicialCell_measurable T.points)] with x hx
  exact hB x hx

theorem simplex_continuous_weighted_integrable
    (w : BoundedMultiplier (volume.restrict (simplicialCell T.points)))
    (f : SpatialCoordinates d → ℝ) (hf : Continuous f) :
    Integrable (fun x => |w.value x|^2*(f x)^2) (volume.restrict (simplicialCell T.points)) := by
  let h := simplex_continuous_memLp T f hf
  apply (w.integrable_density (h.toLp f)).congr
  filter_upwards [h.coeFn_toLp] with x hx
  simp only [hx,Real.norm_eq_abs,sq_abs]

theorem simplex_weighted_sq_anchor
    (w : BoundedMultiplier (volume.restrict (simplicialCell T.points)))
    (f : SpatialCoordinates d → ℝ) (hf : Continuous f) (W s : ℝ) (hW : 0 < W) (hs : 0 < s)
    (hw : ∀ᵐ x ∂volume.restrict (simplicialCell T.points), |w.value x| ≤ W*s ∧ s ≤ W*|w.value x|) :
    (∫ x in simplicialCell T.points, |w.value x|^2*(f x)^2) ≤
      W^2*s^2*(∫ x in simplicialCell T.points, (f x)^2) ∧
    s^2*(∫ x in simplicialCell T.points, (f x)^2) ≤
      W^2*(∫ x in simplicialCell T.points, |w.value x|^2*(f x)^2) := by
  have hi : IntegrableOn (fun x => (f x)^2) (simplicialCell T.points) :=
    (hf.pow 2).continuousOn.integrableOn_compact (simplicialCell_compact _)
  have hwf := simplex_continuous_weighted_integrable T w f hf
  constructor
  · calc
      _ ≤ ∫ x in simplicialCell T.points, (W*s)^2*(f x)^2 := by
        apply integral_mono_ae hwf (hi.const_mul _)
        filter_upwards [hw] with x hx
        exact mul_le_mul_of_nonneg_right
          ((sq_le_sq₀ (abs_nonneg _) (mul_nonneg hW.le hs.le)).mpr hx.1) (sq_nonneg _)
      _ = _ := by rw [integral_const_mul,mul_pow,mul_assoc]
  · calc
      _ = ∫ x in simplicialCell T.points, s^2*(f x)^2 := (integral_const_mul _ _).symm
      _ ≤ ∫ x in simplicialCell T.points, W^2*(|w.value x|^2*(f x)^2) := by
        apply integral_mono_ae (hi.const_mul _) (hwf.const_mul _)
        filter_upwards [hw] with x hx
        have h := mul_le_mul_of_nonneg_right
          ((sq_le_sq₀ hs.le (mul_nonneg hW.le (abs_nonneg _))).mpr hx.2) (sq_nonneg (f x))
        simpa only [mul_pow,mul_assoc] using h
      _ = _ := integral_const_mul _ _

end Carleman
