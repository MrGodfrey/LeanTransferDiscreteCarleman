module

public import Carleman.Spatial.FullSpaceInterpolation
public import Carleman.Spatial.CompactLipschitzSobolev
public import Mathlib.Topology.MetricSpace.Thickening

/-! Bounds and exact support control for genuine convolution with a
nonnegative unit-mass smooth compact kernel. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped Convolution ContDiff NNReal
namespace Carleman.SpatialTest
variable {d : ℕ} (κ : SpatialTest (univ : Set (SpatialCoordinates d)))

theorem convolution_norm_bound (hκ : ∀ x, 0 ≤ κ.value x) (hunit : ∫ x, κ.value x = 1)
    {f : SpatialCoordinates d → ℝ} {B : ℝ} (hf : ∀ x, ‖f x‖ ≤ B) (x : SpatialCoordinates d) :
    ‖(κ.value ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x‖ ≤ B := by
  have hk : Integrable κ.value volume := κ.smooth.continuous.integrable_of_hasCompactSupport κ.compact
  calc
    _ ≤ ∫ y, κ.value y * B := by
      apply norm_integral_le_of_norm_le (hk.mul_const B)
      filter_upwards with y
      change ‖κ.value y * f (x-y)‖ ≤ _
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hκ y)]
      exact mul_le_mul_of_nonneg_left (hf (x-y)) (hκ y)
    _ = B := by rw [integral_mul_const,hunit,one_mul]

theorem convolution_lipschitz (hκ : ∀ x, 0 ≤ κ.value x) (hunit : ∫ x, κ.value x = 1)
    {f : SpatialCoordinates d → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f) :
    LipschitzWith C (κ.value ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) := by
  have hk : Integrable κ.value volume := κ.smooth.continuous.integrable_of_hasCompactSupport κ.compact
  have hi := κ.compact.convolutionExists_left (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ)
    κ.smooth.continuous hf.continuous.locallyIntegrable
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  change ‖(∫ t, κ.value t * f (x-t)) - ∫ t, κ.value t * f (y-t)‖ ≤ _
  have hix : Integrable (fun t => κ.value t * f (x-t)) volume := hi x
  have hiy : Integrable (fun t => κ.value t * f (y-t)) volume := hi y
  rw [← integral_sub hix hiy]
  calc
    _ ≤ ∫ t, κ.value t * ((C:ℝ)*dist x y) := by
      apply norm_integral_le_of_norm_le (hk.mul_const _)
      filter_upwards with t
      rw [← mul_sub,norm_mul,Real.norm_eq_abs,abs_of_nonneg (hκ t)]
      apply mul_le_mul_of_nonneg_left _ (hκ t)
      simpa only [← dist_eq_norm,dist_sub_right] using hf.dist_le_mul (x-t) (y-t)
    _ = (C:ℝ)*dist x y := by rw [integral_mul_const,hunit,one_mul]

theorem convolution_tsupport_subset_thickening {f : SpatialCoordinates d → ℝ} {r : ℝ}
    (hκ : tsupport κ.value ⊆ Metric.closedBall 0 r) :
    tsupport (κ.value ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) ⊆
      Metric.cthickening r (tsupport f) := by
  apply closure_minimal _ Metric.isClosed_cthickening
  intro x hx
  obtain ⟨y,hy,z,hz,rfl⟩ := support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) hx
  apply Metric.mem_cthickening_of_dist_le (y+z) z r (tsupport f) (subset_tsupport f hz)
  simpa only [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_right,sub_zero] using hκ (subset_tsupport κ.value hy)

theorem convolution_smooth {f : SpatialCoordinates d → ℝ} (hf : Continuous f) :
    ContDiff ℝ ∞ (κ.value ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) :=
  κ.compact.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) κ.smooth hf.locallyIntegrable

theorem convolution_compact {f : SpatialCoordinates d → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (κ.value ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) := κ.compact.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf

end Carleman.SpatialTest
