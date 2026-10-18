module

public import Carleman.Spatial.CompactConvolution

/-! Actual Frechet derivatives of mollified compact Lipschitz functions are
the convolutions of their genuine a.e. derivative fields. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Convolution NNReal
namespace Carleman
variable {d : ℕ} {f : SpatialCoordinates d → ℝ} {C : ℝ≥0}

theorem compactLipschitz_weakDerivative (hC : LipschitzWith C f) (hf : HasCompactSupport f)
    (e : SpatialCoordinates d) :
    IsWeakSpatialDerivative volume univ e (compactLipschitzLp hC hf)
      ((OperatorMultiplier.const (ContinuousLinearMap.apply ℝ ℝ e)).map
        (compactLipschitzDerivativeLp hC hf)) := by
  apply weakSpatialDerivative_of_lipschitz_full hC e _ _ (compactLipschitzLp_ae hC hf)
  filter_upwards [OperatorMultiplier.const_map_ae (ContinuousLinearMap.apply ℝ ℝ e)
      (compactLipschitzDerivativeLp hC hf),compactLipschitzDerivativeLp_ae hC hf,
      hC.ae_differentiableAt (μ := volume)] with x hx ha hd
  rw [hx,ha]
  exact (hd.lineDeriv_eq_fderiv).symm

theorem compactLipschitz_convolution_fderiv (hC : LipschitzWith C f) (hf : HasCompactSupport f)
    (κ : SpatialTest (univ : Set (SpatialCoordinates d))) (x : SpatialCoordinates d) :
    fderiv ℝ (κ.value ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x =
      (κ.value ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fderiv ℝ f)) x := by
  let u := compactLipschitzLp hC hf
  let A := compactLipschitzDerivativeLp hC hf
  have he : (κ.value ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) =
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) := by
    rw [real_convolution_comm (u : SpatialCoordinates d → ℝ)]
    exact convolution_congr _ Filter.EventuallyEq.rfl (compactLipschitzLp_ae hC hf).symm
  rw [he]
  ext e
  let v := (OperatorMultiplier.const (ContinuousLinearMap.apply ℝ ℝ e)).map A
  have hv : (v : SpatialCoordinates d → ℝ) =ᵐ[volume] (fun y => fderiv ℝ f y e) := by
    filter_upwards [OperatorMultiplier.const_map_ae (ContinuousLinearMap.apply ℝ ℝ e) A,
      compactLipschitzDerivativeLp_ae hC hf] with y hy ha
    exact hy.trans (congrArg (fun B : SpatialCoordinates d →L[ℝ] ℝ => B e) ha)
  rw [(compactLipschitz_weakDerivative hC hf e).fderiv_convolution κ x]
  change (v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) x = _
  rw [real_convolution_comm (v : SpatialCoordinates d → ℝ)]
  have hconv := convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ)
    (f := κ.value) Filter.EventuallyEq.rfl hv
  rw [hconv]
  have hi := κ.compact.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    κ.smooth.continuous ((compactLipschitz_fderiv_memLp hC hf).locallyIntegrable (by norm_num)) x
  change (∫ y, κ.value y * fderiv ℝ f (x-y) e) = (∫ y, κ.value y • fderiv ℝ f (x-y)) e
  have hi' : Integrable (fun y => κ.value y • fderiv ℝ f (x-y)) volume := hi
  rw [ContinuousLinearMap.integral_apply hi']
  rfl

end Carleman
