module

public import Carleman.Spatial.SpacetimeHeatIdentity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Linearity of the actual classical derivatives used to identify smooth graph fields. -/
@[expose] public noncomputable section
open scoped ContDiff BigOperators
namespace Carleman
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

theorem directionalLap_add (e : ι → E) {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : E) :
    directionalLap e (fun y => f y+g y) x=directionalLap e f x+directionalLap e g x := by
  have he (i : ι) : smoothD (e i) (fun y => f y+g y)=
      (fun y => smoothD (e i) f y+smoothD (e i) g y) := funext (smoothD_add hf hg (e i))
  simp only [directionalLap,he,smoothD_add (smoothD_contDiff hf _) (smoothD_contDiff hg _),Finset.sum_add_distrib]

theorem directionalLap_const_mul (e : ι → E) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (c : ℝ) (x : E) :
    directionalLap e (fun y => c*f y) x=c*directionalLap e f x := by
  have he (i : ι) : smoothD (e i) (fun y => c*f y)=
      (fun y => c*smoothD (e i) f y) := funext (smoothD_const_mul hf c (e i))
  simp only [directionalLap,he,smoothD_const_mul (smoothD_contDiff hf _),Finset.mul_sum]

theorem directionalLap_zero (e : ι → E) (x : E) : directionalLap e (fun _ => 0) x=0 := by
  have he (i : ι) : smoothD (e i) (fun _ : E => 0)=(fun _ => 0) := by
    funext y
    simp [smoothD]
  simp only [directionalLap,he,Finset.sum_const_zero]

variable {d : ℕ}

theorem spatialLaplacian_add {f g : SpatialCoordinates d → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : SpatialCoordinates d) :
    spatialLaplacian (fun y => f y+g y) x=spatialLaplacian f x+spatialLaplacian g x :=
  directionalLap_add (EuclideanSpace.basisFun (Fin d) ℝ) hf hg x

theorem spatialLaplacian_const_mul {f : SpatialCoordinates d → ℝ}
    (hf : ContDiff ℝ ∞ f) (c : ℝ) (x : SpatialCoordinates d) :
    spatialLaplacian (fun y => c*f y) x=c*spatialLaplacian f x :=
  directionalLap_const_mul (EuclideanSpace.basisFun (Fin d) ℝ) hf c x

theorem smooth_harmonic_time_derivative (freq : ℝ) (φ ψ : SpatialCoordinates d → ℝ)
    (t : ℝ) (x : SpatialCoordinates d) :
    deriv (fun s => Real.cos (freq*s)*φ x+Real.sin (freq*s)*ψ x) t=
      (-freq*Real.sin (freq*t))*φ x+(freq*Real.cos (freq*t))*ψ x := by
  have hc := (((hasDerivAt_id t).const_mul freq).cos).mul_const (φ x)
  have hs := (((hasDerivAt_id t).const_mul freq).sin).mul_const (ψ x)
  simp only [id_eq,mul_one] at hc hs
  convert! (hc.fun_add hs).deriv using 1
  ring

theorem smooth_harmonic_spatial_laplacian (freq : ℝ) {φ ψ : SpatialCoordinates d → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ) (t : ℝ) (x : SpatialCoordinates d) :
    spatialLaplacian (fun y => Real.cos (freq*t)*φ y+Real.sin (freq*t)*ψ y) x=
      Real.cos (freq*t)*spatialLaplacian φ x+Real.sin (freq*t)*spatialLaplacian ψ x := by
  rw [spatialLaplacian_add (contDiff_const.mul hφ) (contDiff_const.mul hψ),
    spatialLaplacian_const_mul hφ,spatialLaplacian_const_mul hψ]

end Carleman
