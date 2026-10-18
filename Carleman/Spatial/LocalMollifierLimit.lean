module

public import Carleman.Spatial.FullSpaceInterpolation
public import Carleman.Geometry.InteriorErosion

/-! Fatou on an exhaustion by interior regions. This passes uniform local
estimates for actual mollifications to the original L² equivalence class. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter Metric
open scoped Convolution Topology
namespace Carleman
variable {d : ℕ}

theorem local_mollifier_norm_bound {U : Set (SpatialCoordinates d)} (hU : IsOpen U)
    (v : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n, bochnerL2Norm
      (volume.restrict (interiorRegion U (shrinkingBump d n).rOut))
      (v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (spatialMollifier d n).value) ≤ C) :
    bochnerL2Norm (volume.restrict U) v ≤ C := by
  let A := fun n => interiorRegion U (shrinkingBump d n).rOut
  let V := fun n => v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (spatialMollifier d n).value
  let f := fun n => (A n).indicator (V n)
  have hA (n : ℕ) : MeasurableSet (A n) := (isOpen_interiorRegion _ _).measurableSet
  have hm (n : ℕ) : MemLp (f n) 2 volume :=
    (((spatialMollifier d n).convolution_right_memLp_norm_le
      (spatialMollifier_nonneg n) (spatialMollifier_integral n) v).1).indicator (hA n).nullMeasurableSet
  have hbound : ∀ᶠ n in atTop, eLpNorm (f n) 2 volume ≤ ENNReal.ofReal C := by
    filter_upwards with n
    apply (ENNReal.toReal_le_toReal (hm n).eLpNorm_lt_top.ne ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hC,show f n = (A n).indicator (V n) from rfl,
      eLpNorm_indicator_eq_eLpNorm_restrict (hA n).nullMeasurableSet]
    exact hb n
  have hε : Tendsto (fun n => (shrinkingBump d n).rOut) atTop (𝓝 0) := by
    convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2 using 1 <;>
      simp [shrinkingBump,div_eq_mul_inv]
  have hlim : ∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)),
      Tendsto (fun n => f n x) atTop (𝓝 (U.indicator (v : SpatialCoordinates d → ℝ) x)) := by
    filter_upwards [spatialMollifier_converges v] with x hx
    by_cases hxU : x ∈ U
    · rw [indicator_of_mem hxU]
      apply hx.congr'
      filter_upwards [eventually_mem_interiorRegion hU hxU hε] with n hn
      simp only [f,V,A,indicator_of_mem hn]
    · have hn (n : ℕ) : x ∉ A n := fun ha => hxU (interiorRegion_subset _ _ ha)
      simpa only [f,indicator_of_notMem (hn _),indicator_of_notMem hxU] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hfinal := (Lp.memLp v).indicator hU.measurableSet.nullMeasurableSet
  have he := Lp.eLpNorm_le_of_ae_tendsto hbound (fun n => (hm n).aestronglyMeasurable)
    hfinal.aestronglyMeasurable hlim
  have hh := (ENNReal.toReal_le_toReal hfinal.eLpNorm_lt_top.ne ENNReal.ofReal_ne_top).mpr he
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hU.measurableSet.nullMeasurableSet,
    ENNReal.toReal_ofReal hC] at hh
  exact hh
end Carleman
