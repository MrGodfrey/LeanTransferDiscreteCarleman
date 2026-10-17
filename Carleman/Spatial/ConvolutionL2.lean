module

public import Carleman.Spatial.WeakConvolution
public import Carleman.Spatial.RealL2Integral

/-! L² contraction by a nonnegative smooth compactly supported unit-mass
kernel, proved from weighted Cauchy--Schwarz and the actual convolution integral. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff Convolution ENNReal
namespace Carleman.SpatialTest
variable {d : ℕ} (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
  (hκ : ∀ x, 0 ≤ κ.value x) (hunit : ∫ x, κ.value x = 1)

include hκ hunit
theorem convolution_square_le (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))
    (x : SpatialCoordinates d) :
    ((κ.value ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x)^2 ≤
      (κ.value ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => (u y)^2)) x := by
  let r := fun y => Real.sqrt (κ.value y)
  have hr : Continuous r := κ.smooth.continuous.sqrt
  have hrc : HasCompactSupport r := κ.compact.comp_left Real.sqrt_zero
  have hr₂ : MemLp r 2 volume := hr.memLp_of_hasCompactSupport hrc
  have hrInf : MemLp r ∞ volume := hr.memLp_of_hasCompactSupport hrc
  have hu : MemLp (fun y => u (x-y)) 2 volume :=
    (Lp.memLp u).comp_measurePreserving (Measure.measurePreserving_sub_left volume x)
  have hv : MemLp (fun y => r y*u (x-y)) 2 volume := hrInf.mul hu
  have hsq : ∀ y, r y^2 = κ.value y := fun y => Real.sq_sqrt (hκ y)
  have hh := integral_mul_sq_le hr₂ hv
  have he : (fun y => r y*(r y*u (x-y))) = (fun y => κ.value y*u (x-y)) := by
    funext y
    rw [← mul_assoc, ← pow_two, hsq]
  have he₂ : (fun y => (r y*u (x-y))^2) = (fun y => κ.value y*(u (x-y))^2) := by
    funext y
    rw [mul_pow, hsq]
  simp only [he, he₂, hsq, hunit, one_mul] at hh
  exact hh

theorem convolution_memLp_norm_le (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    MemLp (κ.value ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) 2 volume ∧
      bochnerL2Norm volume (κ.value ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) ≤ ‖u‖ := by
  have hk : Integrable κ.value volume := κ.smooth.continuous.integrable_of_hasCompactSupport κ.compact
  have hu := (Lp.memLp u).integrable_sq
  have hconv := hk.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hu
  have hmeas := κ.smooth.continuous.aestronglyMeasurable.convolution
    (ContinuousLinearMap.lsmul ℝ ℝ) (Lp.aestronglyMeasurable u)
  have hsq : Integrable (fun x =>
      ((κ.value ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x)^2) volume := by
    apply hconv.mono' (hmeas.pow 2)
    exact Filter.Eventually.of_forall fun x => by
      change ‖((κ.value ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x)^2‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact κ.convolution_square_le hκ hunit u x
  have hm := (memLp_two_iff_integrable_sq hmeas).mpr hsq
  refine ⟨hm, ?_⟩
  have hh := integral_mono_ae hsq hconv
    (Filter.Eventually.of_forall (κ.convolution_square_le hκ hunit u))
  rw [integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hk hu] at hh
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, hunit, one_mul] at hh
  rw [integral_sq_eq_bochnerL2Norm_sq hm,
    integral_sq_eq_bochnerL2Norm_sq (Lp.memLp u)] at hh
  change (bochnerL2Norm volume _)^2 ≤ ‖u‖^2 at hh
  exact (sq_le_sq₀ (bochnerL2Norm_nonneg _) (norm_nonneg u)).mp hh

end Carleman.SpatialTest
