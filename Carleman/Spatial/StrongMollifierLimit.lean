module

public import Carleman.Spatial.StrongL2Limit
public import Carleman.Spatial.FullSpaceInterpolation
public import Carleman.Continuous.NormDomination
public import Carleman.Continuous.BochnerNormAlgebra

/-! Strong L² convergence of the actual shrinking spatial mollifiers on
every full-space L² class. No continuity, compact support, or Sobolev
regularity of a representative is required. -/
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology Convolution
namespace Carleman
variable {d : ℕ}

theorem spatialMollifier_square_error_tendsto
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    Tendsto (fun n => ∫ x, ((u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (spatialMollifier d n).value) x-u x)^2) atTop (𝓝 0) := by
  have hm (n : ℕ) := (spatialMollifier d n).convolution_right_memLp_norm_le
    (spatialMollifier_nonneg n) (spatialMollifier_integral n) u
  apply l2_square_tendsto_zero_of_ae_of_energy_le (Lp.memLp u) (fun n => (hm n).1)
    (spatialMollifier_converges u)
  intro n
  rw [integral_sq_eq_bochnerL2Norm_sq (hm n).1,integral_sq_eq_bochnerL2Norm_sq (Lp.memLp u),
    bochnerL2Norm_coe]
  exact (sq_le_sq₀ (bochnerL2Norm_nonneg _) (norm_nonneg _)).mpr (hm n).2

theorem spatialMollifier_L2_error_tendsto
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    Tendsto (fun n => bochnerL2Norm volume (fun x =>
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (spatialMollifier d n).value) x-u x)) atTop (𝓝 0) := by
  have hm (n : ℕ) := ((spatialMollifier d n).convolution_right_memLp_norm_le
    (spatialMollifier_nonneg n) (spatialMollifier_integral n) u).1.sub (Lp.memLp u)
  have he (n : ℕ) : (∫ x, ((u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (spatialMollifier d n).value) x-u x)^2) =
      (bochnerL2Norm volume (fun x => (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (spatialMollifier d n).value) x-u x))^2 :=
    integral_sq_eq_bochnerL2Norm_sq (hm n)
  have ht := (spatialMollifier_square_error_tendsto u).sqrt
  simpa only [he,Real.sqrt_sq (bochnerL2Norm_nonneg _),Real.sqrt_zero] using ht

def spatialMollificationLp (n : ℕ) (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    Lp ℝ 2 (volume : Measure (SpatialCoordinates d)) :=
  ((spatialMollifier d n).convolution_right_memLp_norm_le
    (spatialMollifier_nonneg n) (spatialMollifier_integral n) u).1.toLp
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (spatialMollifier d n).value)

theorem spatialMollificationLp_ae (n : ℕ) (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    spatialMollificationLp n u =ᵐ[volume]
      u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (spatialMollifier d n).value := MemLp.coeFn_toLp _

theorem spatialMollificationLp_tendsto (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    Tendsto (fun n => spatialMollificationLp n u) atTop (𝓝 u) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he (n : ℕ) : ‖spatialMollificationLp n u-u‖ =
      bochnerL2Norm volume (fun x => (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (spatialMollifier d n).value) x-u x) := by
    rw [← bochnerL2Norm_coe]
    apply bochnerL2Norm_congr_ae
    filter_upwards [Lp.coeFn_sub (spatialMollificationLp n u) u,spatialMollificationLp_ae n u] with x hx hy
    rw [hx,Pi.sub_apply,hy]
  simpa only [he] using spatialMollifier_L2_error_tendsto u

end Carleman
