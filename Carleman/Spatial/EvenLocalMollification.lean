module

public import Carleman.Spatial.EvenMollifierLimit
public import Carleman.Spatial.LocalStrongMollification

/-! Full local first and second weak-derivative convergence for the even kernels. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology Convolution ContDiff
namespace Carleman
variable {d : ℕ} {S K : Set (SpatialCoordinates d)}

theorem evenSpatialMollifier_tsupport_subset (n : ℕ) :
    tsupport (evenSpatialMollifier d n).value ⊆ tsupport (spatialMollifier d n).value := by
  have h := closure_mono (evenSpatialMollifier_support (d := d) n)
  rw [closure_ball _ (shrinkingBump d n).rOut_pos.ne'] at h
  change tsupport (evenSpatialMollifier d n).value ⊆ tsupport ((shrinkingBump d n).normed volume)
  rwa [(shrinkingBump d n).tsupport_normed_eq]

theorem evenSpatialMollifier_L2_error_restrict_tendsto
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) (K : Set (SpatialCoordinates d)) :
    Tendsto (fun n => bochnerL2Norm (volume.restrict K) (fun x =>
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] (evenSpatialMollifier d n).value) x-u x)) atTop (𝓝 0) := by
  have ht := evenSpatialMollifier_L2_error_tendsto u
  simp only [real_convolution_comm (u : SpatialCoordinates d → ℝ)]
  apply squeeze_zero (fun n => bochnerL2Norm_nonneg _) _ ht
  intro n
  have hm := ((evenSpatialMollifier d n).convolution_memLp_norm_le
    (evenSpatialMollifier_nonneg n) (evenSpatialMollifier_integral n) u).1.sub (Lp.memLp u)
  exact ENNReal.toReal_mono hm.ne (eLpNorm_mono_measure _ Measure.restrict_le_self)

theorem IsWeakSpatialDerivative.local_even_mollification_strong_first
    (hS : IsOpen S) (hK : IsCompact K) (hKS : K ⊆ S)
    {u v : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))} {e : SpatialCoordinates d}
    (huv : IsWeakSpatialDerivative volume S e u v) :
    Tendsto (fun n => bochnerL2Norm (volume.restrict K) (fun x =>
      fderiv ℝ (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] (evenSpatialMollifier d n).value) x e-v x))
      atTop (𝓝 0) := by
  apply (evenSpatialMollifier_L2_error_restrict_tendsto v K).congr'
  filter_upwards [compact_mollifier_eventually_inside hS hK hKS] with n hn
  apply bochnerL2Norm_congr_ae
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  rw [huv.fderiv_convolution_local (evenSpatialMollifier d n) x
    (fun y hy => hn x hx y (evenSpatialMollifier_tsupport_subset n hy))]

theorem IsWeakSpatialDerivative.local_even_mollification_strong_second
    (hS : IsOpen S) (hK : IsCompact K) (hKS : K ⊆ S)
    {u v z : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))} {e₀ e₁ : SpatialCoordinates d}
    (huv : IsWeakSpatialDerivative volume S e₀ u v)
    (hvz : IsWeakSpatialDerivative volume S e₁ v z) :
    Tendsto (fun n => bochnerL2Norm (volume.restrict K) (fun x =>
      iteratedFDeriv ℝ 2 (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume]
        (evenSpatialMollifier d n).value) x ![e₀,e₁]-z x)) atTop (𝓝 0) := by
  apply (evenSpatialMollifier_L2_error_restrict_tendsto z K).congr'
  filter_upwards [compact_mollifier_eventually_inside hS hK hKS] with n hn
  apply bochnerL2Norm_congr_ae
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  rw [huv.second_tensor_convolution_local hvz (evenSpatialMollifier d n) x
    (fun y hy => hn x hx y (evenSpatialMollifier_tsupport_subset n hy))]

end Carleman
