module

public import Carleman.Spatial.WeakConvolution
public import Carleman.Spatial.ZeroExtensionLp

/-! Local convolution of actual domain L² classes. The reflected kernel is
an admissible test only when its whole support stays in the domain. The zero
extension is never asserted to have a global weak Sobolev derivative. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped Convolution ContDiff
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem IsWeakSpatialDerivative.zeroExtend (hS : MeasurableSet S)
    {e : SpatialCoordinates d}
    {u v : Lp ℝ 2 ((volume : Measure (SpatialCoordinates d)).restrict S)}
    (h : IsWeakSpatialDerivative (volume.restrict S) S e u v) :
    IsWeakSpatialDerivative volume S e (zeroExtendLp hS u) (zeroExtendLp hS v) := by
  apply IsWeakSpatialDerivative.iff_integral.mpr
  intro φ
  rw [integral_mul_zeroExtendLp,integral_mul_zeroExtendLp]
  exact IsWeakSpatialDerivative.iff_integral.mp h φ

namespace SpatialTest
variable (κ : SpatialTest (univ : Set (SpatialCoordinates d)))

def reflectedWithin (x : SpatialCoordinates d)
    (hinside : ∀ y ∈ tsupport κ.value, x-y ∈ S) : SpatialTest S where
  value := (κ.reflected x).value
  smooth := (κ.reflected x).smooth
  compact := (κ.reflected x).compact
  support := by
    intro z hz
    have hz' : x-z ∈ tsupport κ.value := by
      change z ∈ tsupport (κ.value ∘ (Homeomorph.subLeft x)) at hz
      rw [tsupport_comp_eq_preimage] at hz
      exact hz
    simpa only [sub_sub_cancel] using hinside (x-z) hz'

/-- Differentiation of a genuine full-space L² convolution; no derivative of
the state is assumed. Local weak derivatives will identify the right side. -/
theorem fderiv_convolution_integral (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))
    (x e : SpatialCoordinates d) :
    fderiv ℝ (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) x e =
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => fderiv ℝ κ.value y e)) x := by
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
  rfl
end SpatialTest

namespace IsWeakSpatialDerivative
variable {e : SpatialCoordinates d}
  {u v : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))}
  (h : IsWeakSpatialDerivative volume S e u v)
  (κ : SpatialTest (univ : Set (SpatialCoordinates d)))

include h
theorem convolution_exchange_local (x : SpatialCoordinates d)
    (hinside : ∀ y ∈ tsupport κ.value, x-y ∈ S) :
    (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (fun y => fderiv ℝ κ.value y e)) x =
      (v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) x := by
  have hh := IsWeakSpatialDerivative.iff_integral.mp h (κ.reflectedWithin x hinside)
  change (∫ y, fderiv ℝ (κ.reflected x).value y e*u y) =
    -(∫ y, (κ.reflected x).value y*v y) at hh
  simp_rw [κ.reflected_derivative x _ e,neg_mul,integral_neg] at hh
  simpa only [convolution,ContinuousLinearMap.lsmul_apply,smul_eq_mul,
    SpatialTest.reflected,mul_comm] using neg_injective hh

theorem fderiv_convolution_local (x : SpatialCoordinates d)
    (hinside : ∀ y ∈ tsupport κ.value, x-y ∈ S) :
    fderiv ℝ (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) x e =
      (v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) x := by
  rw [κ.fderiv_convolution_integral]
  exact h.convolution_exchange_local κ x hinside
end IsWeakSpatialDerivative
end Carleman
