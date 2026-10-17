module

public import Carleman.Spatial.MollifiedInterpolation
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! The homogeneous L² interpolation inequality for a full-space weak
derivative chain. The mollifier, its contraction and weak exchange, and the
Fatou passage are all proved; no domain extension is asserted. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Convolution ContDiff Topology ENNReal
namespace Carleman
variable {d : ℕ}

def shrinkingBump (d n : ℕ) : ContDiffBump (0 : SpatialCoordinates d) where
  rIn := 1/((n : ℝ)+1)
  rOut := 2/((n : ℝ)+1)
  rIn_pos := by positivity
  rIn_lt_rOut := by apply div_lt_div_of_pos_right (by norm_num); positivity

def spatialMollifier (d n : ℕ) : SpatialTest (univ : Set (SpatialCoordinates d)) where
  value := (shrinkingBump d n).normed volume
  smooth := (shrinkingBump d n).contDiff_normed
  compact := (shrinkingBump d n).hasCompactSupport_normed
  support := subset_univ _

theorem spatialMollifier_nonneg (n : ℕ) (x : SpatialCoordinates d) :
    0 ≤ (spatialMollifier d n).value x := (shrinkingBump d n).nonneg_normed x

theorem spatialMollifier_integral (n : ℕ) :
    ∫ x, (spatialMollifier d n).value x = 1 := (shrinkingBump d n).integral_normed

theorem spatialMollifier_converges (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    ∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)), Tendsto
      (fun n => (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (spatialMollifier d n).value) x)
      atTop (𝓝 (u x)) := by
  have hout : Tendsto (fun n => (shrinkingBump d n).rOut) atTop (𝓝 0) := by
    have hh := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    convert hh.const_mul 2 using 1 <;> simp [shrinkingBump, div_eq_mul_inv]
  have hratio : ∀ᶠ n in atTop, (shrinkingBump d n).rOut ≤ 2*(shrinkingBump d n).rIn := by
    filter_upwards with n
    simp [shrinkingBump, div_eq_mul_inv]
  have hh := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hout hratio
    ((Lp.memLp u).locallyIntegrable (by norm_num))
  simpa only [real_convolution_comm (u : SpatialCoordinates d → ℝ), spatialMollifier] using hh

/-- The two weak derivatives are in the same arbitrary spatial direction. -/
theorem weak_spatial_chain_norm_sq_le {e : SpatialCoordinates d}
    {u v z : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))}
    (huv : IsWeakSpatialDerivative volume univ e u v)
    (hvz : IsWeakSpatialDerivative volume univ e v z) : ‖v‖^2 ≤ ‖u‖*‖z‖ := by
  let K := Real.sqrt (‖u‖*‖z‖)
  let f := fun n => v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (spatialMollifier d n).value
  have hfin (n : ℕ) : MemLp (f n) 2 volume :=
    ((spatialMollifier d n).convolution_right_memLp_norm_le
      (spatialMollifier_nonneg n) (spatialMollifier_integral n) v).1
  have hbound (n : ℕ) : bochnerL2Norm volume (f n) ≤ K :=
    Real.le_sqrt_of_sq_le ((spatialMollifier d n).weak_chain_convolution_sq_le
      (spatialMollifier_nonneg n) (spatialMollifier_integral n) huv hvz)
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hb : ∀ᶠ n in atTop, eLpNorm (f n) 2 volume ≤ ENNReal.ofReal K := by
    filter_upwards with n
    apply (ENNReal.toReal_le_toReal ((hfin n).eLpNorm_lt_top.ne) ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hK, bochnerL2Norm] using hbound n
  have hlim := Lp.eLpNorm_le_of_ae_tendsto hb (fun n => (hfin n).aestronglyMeasurable)
    (Lp.aestronglyMeasurable v) (spatialMollifier_converges v)
  have hv : ‖v‖ ≤ K := by
    have hh := (ENNReal.toReal_le_toReal (Lp.eLpNorm_ne_top v) ENNReal.ofReal_ne_top).mpr hlim
    simpa only [ENNReal.toReal_ofReal hK, Lp.norm_def] using hh
  exact (Real.le_sqrt (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp hv

end Carleman
