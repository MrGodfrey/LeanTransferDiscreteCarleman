module

public import Carleman.Spatial.DomainConvolution
public import Carleman.Spatial.TensorCoordinateNorm
public import Carleman.Spatial.MollifiedInterpolation

/-! Genuine mixed second derivatives of a local convolution, using the
original weak derivative chain only where the reflected kernel is admissible.
Zero extensions are never asserted to have global weak derivatives. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped Convolution ContDiff
namespace Carleman
variable {d : ℕ}

namespace SpatialTest

def directionalKernel (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (e : SpatialCoordinates d) : SpatialTest (univ : Set (SpatialCoordinates d)) where
  value x := fderiv ℝ κ.value x e
  smooth := (κ.smooth.fderiv_right (by simp)).clm_apply contDiff_const
  compact := κ.compact.fderiv_apply ℝ e
  support := subset_univ _

theorem directionalKernel_support (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (e : SpatialCoordinates d) : tsupport (κ.directionalKernel e).value ⊆ tsupport κ.value :=
  tsupport_fderiv_apply_subset ℝ e

end SpatialTest

namespace IsWeakSpatialDerivative
variable {S : Set (SpatialCoordinates d)}
  {e₀ e₁ : SpatialCoordinates d} {u v z : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))}

theorem mixed_fderiv_convolution_local
    (huv : IsWeakSpatialDerivative volume S e₀ u v)
    (hvz : IsWeakSpatialDerivative volume S e₁ v z)
    (κ : SpatialTest (univ : Set (SpatialCoordinates d))) (x : SpatialCoordinates d)
    (hinside : ∀ y ∈ tsupport κ.value, x-y ∈ S) :
    fderiv ℝ (fun y => fderiv ℝ
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) y e₁) x e₀ =
      (z ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) x := by
  have he : (fun y => fderiv ℝ (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) y e₁) =
      u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (κ.directionalKernel e₁).value := by
    funext y
    exact κ.fderiv_convolution_integral u y e₁
  rw [he,(κ.directionalKernel e₁).fderiv_convolution_integral]
  rw [huv.convolution_exchange_local (κ.directionalKernel e₁) x
    (fun y hy => hinside y (κ.directionalKernel_support e₁ hy))]
  change (v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => fderiv ℝ κ.value y e₁)) x = _
  rw [← κ.fderiv_convolution_integral]
  exact hvz.fderiv_convolution_local κ x hinside

theorem second_tensor_convolution_local
    (huv : IsWeakSpatialDerivative volume S e₀ u v)
    (hvz : IsWeakSpatialDerivative volume S e₁ v z)
    (κ : SpatialTest (univ : Set (SpatialCoordinates d))) (x : SpatialCoordinates d)
    (hinside : ∀ y ∈ tsupport κ.value, x-y ∈ S) :
    iteratedFDeriv ℝ 2 (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) x ![e₀,e₁] =
      (z ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) x := by
  let U := u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value
  have hs : ContDiff ℝ 2 U := (κ.smooth_convolution u).of_le (by simp)
  have hdf : ContDiff ℝ 1 (fderiv ℝ U) := hs.fderiv_right (by norm_num)
  have he := fderiv_clm_apply (hdf.differentiable (by simp) x) (differentiableAt_const e₁)
  simp only [fderiv_const_apply,ContinuousLinearMap.comp_zero,zero_add] at he
  have happly := congrArg (fun A : SpatialCoordinates d →L[ℝ] ℝ => A e₀) he
  rw [iteratedFDeriv_two_apply]
  change fderiv ℝ (fderiv ℝ U) x e₀ e₁ = _
  change fderiv ℝ (fun y => fderiv ℝ U y e₁) x e₀ = fderiv ℝ (fderiv ℝ U) x e₀ e₁ at happly
  exact happly.symm.trans (huv.mixed_fderiv_convolution_local hvz κ x hinside)

end IsWeakSpatialDerivative
end Carleman
