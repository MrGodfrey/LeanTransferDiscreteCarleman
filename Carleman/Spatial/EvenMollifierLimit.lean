module

public import Carleman.Spatial.EvenKernelConvolution

/-! Almost-everywhere and strong L² convergence of the actual fully even mollifiers. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Convolution Topology
namespace Carleman
variable {d : ℕ}

theorem SpatialTest.evenCoordinates_converges
    (κ : ℕ → SpatialTest (univ : Set (SpatialCoordinates d)))
    (hlim : ∀ u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d)),
      ∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)),
      Tendsto (fun n => ((κ n).value ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] u) x) atTop (𝓝 (u x)))
    (rs : List (Fin d)) :
    ∀ u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d)),
      ∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)),
      Tendsto (fun n => ((κ n |>.evenCoordinates rs).value ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] u) x)
        atTop (𝓝 (u x)) := by
  induction rs with
  | nil => exact hlim
  | cons r rs ih =>
    intro u
    let v := coordinateReflectionLp r 0 u
    have h1 := ih u
    have h2 := (coordinateReflection_measurePreserving r 0).quasiMeasurePreserving.ae (ih v)
    have h3 := (coordinateReflection_measurePreserving r 0).quasiMeasurePreserving.ae
      (coordinateReflectionLp_ae r 0 u)
    filter_upwards [h1,h2,h3] with x hx hx' hv
    simp only [coordinateReflection_zero] at hx'
    have he : v (coordinateSignFlip r x)=u x := by
      change coordinateReflectionLp r 0 u (coordinateReflection r 0 x)=
        u (coordinateReflection r 0 (coordinateReflection r 0 x)) at hv
      rw [coordinateReflection_involutive] at hv
      simpa only [coordinateReflection_zero] using hv
    have hh := (hx.add hx').div_const 2
    rw [he,show (u x+u x)/2=u x by ring] at hh
    convert! hh using 1
    funext n
    exact SpatialTest.evenCoordinate_convolution ((κ n).evenCoordinates rs) r u x

theorem evenSpatialMollifier_converges (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    ∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)),
      Tendsto (fun n => ((evenSpatialMollifier d n).value ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] u) x)
        atTop (𝓝 (u x)) := by
  apply SpatialTest.evenCoordinates_converges (fun n => spatialMollifier d n) _ _ u
  intro v
  simpa only [real_convolution_comm (v : SpatialCoordinates d → ℝ)] using spatialMollifier_converges v

theorem evenSpatialMollifier_square_error_tendsto
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    Tendsto (fun n => ∫ x, (((evenSpatialMollifier d n).value ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] u) x-u x)^2)
      atTop (𝓝 0) := by
  have hm (n : ℕ) := (evenSpatialMollifier d n).convolution_memLp_norm_le
    (evenSpatialMollifier_nonneg n) (evenSpatialMollifier_integral n) u
  apply l2_square_tendsto_zero_of_ae_of_energy_le (Lp.memLp u) (fun n => (hm n).1)
    (evenSpatialMollifier_converges u)
  intro n
  rw [integral_sq_eq_bochnerL2Norm_sq (hm n).1,integral_sq_eq_bochnerL2Norm_sq (Lp.memLp u),
    bochnerL2Norm_coe]
  exact (sq_le_sq₀ (bochnerL2Norm_nonneg _) (norm_nonneg _)).mpr (hm n).2

theorem evenSpatialMollifier_L2_error_tendsto
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    Tendsto (fun n => bochnerL2Norm volume (fun x =>
      ((evenSpatialMollifier d n).value ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] u) x-u x))
      atTop (𝓝 0) := by
  have hm (n : ℕ) := ((evenSpatialMollifier d n).convolution_memLp_norm_le
    (evenSpatialMollifier_nonneg n) (evenSpatialMollifier_integral n) u).1.sub (Lp.memLp u)
  have he (n : ℕ) : (∫ x, (((evenSpatialMollifier d n).value ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] u) x-u x)^2)=
      (bochnerL2Norm volume (fun x =>
        ((evenSpatialMollifier d n).value ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] u) x-u x))^2 :=
    integral_sq_eq_bochnerL2Norm_sq (hm n)
  have ht := (evenSpatialMollifier_square_error_tendsto u).sqrt
  simpa only [he,Real.sqrt_sq (bochnerL2Norm_nonneg _),Real.sqrt_zero] using ht

end Carleman
