module

public import Carleman.Spatial.StrongMollifierLimit
public import Carleman.Spatial.InteriorWeakPoincare
public import Carleman.Spatial.LocalHessianConvolution

/-! Strong local convergence of actual first and second derivatives of the
same mollified state, identified with the original distributional fields.
Only compact subsets of the original open domain occur in this step. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology Convolution
namespace Carleman
variable {d : ℕ} {S K : Set (SpatialCoordinates d)}

theorem spatialMollifier_L2_error_restrict_tendsto
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) (K : Set (SpatialCoordinates d)) :
    Tendsto (fun n => bochnerL2Norm (volume.restrict K) (fun x =>
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (spatialMollifier d n).value) x-u x)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => bochnerL2Norm_nonneg _) _ (spatialMollifier_L2_error_tendsto u)
  intro n
  have hm := ((spatialMollifier d n).convolution_right_memLp_norm_le
    (spatialMollifier_nonneg n) (spatialMollifier_integral n) u).1.sub (Lp.memLp u)
  exact ENNReal.toReal_mono hm.ne (eLpNorm_mono_measure _ Measure.restrict_le_self)

theorem IsWeakSpatialDerivative.local_mollification_strong_first
    (hS : IsOpen S) (hK : IsCompact K) (hKS : K ⊆ S)
    {u v : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))} {e : SpatialCoordinates d}
    (huv : IsWeakSpatialDerivative volume S e u v) :
    Tendsto (fun n => bochnerL2Norm (volume.restrict K) (fun x =>
      fderiv ℝ (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (spatialMollifier d n).value) x e-v x))
      atTop (𝓝 0) := by
  apply (spatialMollifier_L2_error_restrict_tendsto v K).congr'
  filter_upwards [compact_mollifier_eventually_inside hS hK hKS] with n hn
  apply bochnerL2Norm_congr_ae
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  rw [huv.fderiv_convolution_local (spatialMollifier d n) x (hn x hx)]

theorem IsWeakSpatialDerivative.local_mollification_strong_second
    (hS : IsOpen S) (hK : IsCompact K) (hKS : K ⊆ S)
    {u v z : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))} {e₀ e₁ : SpatialCoordinates d}
    (huv : IsWeakSpatialDerivative volume S e₀ u v)
    (hvz : IsWeakSpatialDerivative volume S e₁ v z) :
    Tendsto (fun n => bochnerL2Norm (volume.restrict K) (fun x =>
      iteratedFDeriv ℝ 2 (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (spatialMollifier d n).value) x ![e₀,e₁]-z x)) atTop (𝓝 0) := by
  apply (spatialMollifier_L2_error_restrict_tendsto z K).congr'
  filter_upwards [compact_mollifier_eventually_inside hS hK hKS] with n hn
  apply bochnerL2Norm_congr_ae
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  rw [huv.second_tensor_convolution_local hvz (spatialMollifier d n) x (hn x hx)]

end Carleman
