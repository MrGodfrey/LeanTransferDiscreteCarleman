module

public import Carleman.Spatial.SobolevJet
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! Full-space mollification commutes with the actual distributional spatial
derivative. The exchange is proved by testing against the reflected kernel. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff Convolution
namespace Carleman
variable {d : ℕ}

namespace SpatialTest
variable (κ : SpatialTest (univ : Set (SpatialCoordinates d)))

def reflected (x : (SpatialCoordinates d)) : SpatialTest (univ : Set (SpatialCoordinates d)) where
  value y := κ.value (x-y)
  smooth := κ.smooth.comp (contDiff_const.sub contDiff_id)
  compact := κ.compact.comp_homeomorph (Homeomorph.subLeft x)
  support := subset_univ _

theorem reflected_derivative (x y e : (SpatialCoordinates d)) :
    fderiv ℝ (κ.reflected x).value y e = -fderiv ℝ κ.value (x-y) e := by
  have hκ := κ.smooth.differentiable (by simp)
  have hh := (hκ (x-y)).hasFDerivAt.comp y
    ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
  change fderiv ℝ (κ.value ∘ (fun y => x-y)) y e = _
  rw [hh.fderiv]
  simp

end SpatialTest

namespace IsWeakSpatialDerivative
variable {e : (SpatialCoordinates d)} {u v : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))}
  (h : IsWeakSpatialDerivative volume univ e u v) (κ : SpatialTest (univ : Set (SpatialCoordinates d)))

include h

/-- Distributional integration by parts, with no pointwise derivative of u. -/
theorem convolution_exchange (x : (SpatialCoordinates d)) :
    (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (fun y => fderiv ℝ κ.value y e)) x =
      (v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) x := by
  have hh := IsWeakSpatialDerivative.iff_integral.mp h (κ.reflected x)
  simp_rw [κ.reflected_derivative x _ e, neg_mul, integral_neg] at hh
  have he := neg_injective hh
  simpa only [convolution, ContinuousLinearMap.lsmul_apply, smul_eq_mul, SpatialTest.reflected, mul_comm] using he

theorem fderiv_convolution (x : (SpatialCoordinates d)) :
    fderiv ℝ (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) x e =
      (v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) x := by
  have hu := (Lp.memLp u).locallyIntegrable (by norm_num)
  have hd := κ.compact.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    hu (κ.smooth.of_le (by simp)) x
  rw [hd.fderiv]
  change (∫ y, ((ContinuousLinearMap.lsmul ℝ ℝ).precompR (SpatialCoordinates d)) (u y)
    (fderiv ℝ κ.value (x-y))) e = _
  have hi := (κ.compact.fderiv ℝ).convolutionExists_right
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompR (SpatialCoordinates d)) hu
    (κ.smooth.continuous_fderiv (by simp)) x
  rw [ContinuousLinearMap.integral_apply hi]
  simpa only [convolution, ContinuousLinearMap.precompR, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
    h.convolution_exchange κ x

end IsWeakSpatialDerivative

theorem SpatialTest.smooth_convolution (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    ContDiff ℝ ∞ (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) :=
  κ.compact.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    ((Lp.memLp u).locallyIntegrable (by norm_num)) κ.smooth

end Carleman
