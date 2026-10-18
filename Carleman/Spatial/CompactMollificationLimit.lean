module

public import Carleman.Spatial.CompactConvolutionDerivative
public import Carleman.Spatial.CompactLipschitzLimit

/-! Actual smooth convolution converges in the full H¹ graph norm for every
compactly supported Lipschitz function. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Convolution ContDiff Topology NNReal
namespace Carleman
variable {d : ℕ}

theorem shrinkingBump_radius_tendsto :
    Tendsto (fun n => (shrinkingBump d n).rOut) atTop (𝓝 (0:ℝ)) := by
  have hh := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  convert hh.const_mul 2 using 1 <;> simp [shrinkingBump,div_eq_mul_inv]

theorem shrinkingBump_radius_le_two (n : ℕ) : (shrinkingBump d n).rOut ≤ 2 := by
  change 2/((n:ℝ)+1) ≤ 2
  apply (div_le_iff₀ (by positivity)).mpr
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  linarith

def compactMollification (f : SpatialCoordinates d → ℝ) (n : ℕ) : SpatialCoordinates d → ℝ :=
  (spatialMollifier d n).value ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f

theorem compactMollification_smooth {f : SpatialCoordinates d → ℝ} (hf : Continuous f) (n : ℕ) :
    ContDiff ℝ ∞ (compactMollification f n) := (spatialMollifier d n).convolution_smooth hf

theorem compactMollification_compact {f : SpatialCoordinates d → ℝ} (hf : HasCompactSupport f) (n : ℕ) :
    HasCompactSupport (compactMollification f n) := (spatialMollifier d n).convolution_compact hf

theorem compactMollification_lipschitz {f : SpatialCoordinates d → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (n : ℕ) : LipschitzWith C (compactMollification f n) :=
  (spatialMollifier d n).convolution_lipschitz (spatialMollifier_nonneg n) (spatialMollifier_integral n) hf

theorem compactMollification_support (f : SpatialCoordinates d → ℝ) (n : ℕ) :
    tsupport (compactMollification f n) ⊆ Metric.cthickening (shrinkingBump d n).rOut (tsupport f) := by
  apply (spatialMollifier d n).convolution_tsupport_subset_thickening
  change tsupport ((shrinkingBump d n).normed volume) ⊆ _
  rw [(shrinkingBump d n).tsupport_normed_eq]

theorem compactMollification_tendsto {f : SpatialCoordinates d → ℝ} (hf : Continuous f)
    (x : SpatialCoordinates d) :
    Tendsto (fun n => compactMollification f n x) atTop (𝓝 (f x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous shrinkingBump_radius_tendsto hf x

theorem compactMollification_fderiv_tendsto {f : SpatialCoordinates d → ℝ} {C : ℝ≥0}
    (hC : LipschitzWith C f) (hf : HasCompactSupport f) :
    ∀ᵐ x ∂volume, Tendsto (fun n => fderiv ℝ (compactMollification f n) x)
      atTop (𝓝 (fderiv ℝ f x)) := by
  have hr : ∀ᶠ n in atTop, (shrinkingBump d n).rOut ≤ 2*(shrinkingBump d n).rIn := by
    filter_upwards with n
    simp [shrinkingBump,div_eq_mul_inv]
  have hh := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := (volume : Measure (SpatialCoordinates d))) shrinkingBump_radius_tendsto hr
    ((compactLipschitz_fderiv_memLp hC hf).locallyIntegrable (by norm_num))
  filter_upwards [hh] with x hx
  apply hx.congr'
  filter_upwards with n
  exact (compactLipschitz_convolution_fderiv hC hf (spatialMollifier d n) x).symm

theorem compactMollification_tendsto_H1 {f : SpatialCoordinates d → ℝ} {C : ℝ≥0}
    (hC : LipschitzWith C f) (hf : HasCompactSupport f) :
    Tendsto (fun n => compactLipschitzSobolevJet (compactMollification_lipschitz hC n)
      (compactMollification_compact hf n)) atTop (𝓝 (compactLipschitzSobolevJet hC hf)) := by
  obtain ⟨B,hB⟩ := hf.exists_bound_of_continuous hC.continuous
  have hB0 : 0 ≤ B := (norm_nonneg (f 0)).trans (hB 0)
  apply compactLipschitzSobolevJet_tendsto
    (compactMollification_lipschitz hC) hC (compactMollification_compact hf) hf
    (Metric.cthickening 2 (tsupport f)) hf.cthickening
    (fun n => (compactMollification_support f n).trans
      (Metric.cthickening_mono (shrinkingBump_radius_le_two n) _))
    (Metric.self_subset_cthickening (tsupport f)) B hB0
    (fun n => (spatialMollifier d n).convolution_norm_bound
      (spatialMollifier_nonneg n) (spatialMollifier_integral n) hB)
    hB C C.coe_nonneg (fun _ => le_rfl) le_rfl
    (compactMollification_tendsto hC.continuous) (compactMollification_fderiv_tendsto hC hf)

end Carleman
