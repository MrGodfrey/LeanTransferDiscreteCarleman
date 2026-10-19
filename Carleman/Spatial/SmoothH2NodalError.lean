module

public import Carleman.Spatial.SmoothAveragedTaylor
public import Carleman.Spatial.SimplexWithinInterpolation

/-! Nodal value error in dimensions at most three, controlled by the actual
L² Hessian rather than a pointwise Hessian supremum. The function is still
smooth here; passage to every weak H² state is a separate obligation. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

def averagedTaylorPolynomial (K : Set (SpatialCoordinates d)) (f : SpatialCoordinates d → ℝ) :
    SpatialCoordinates d →ᵃ[ℝ] ℝ :=
  affineJetPolynomial ((∫ y in K, f y-fderiv ℝ f y y)/volume.real K)
    ((volume.real K)⁻¹ • (∫ y in K, fderiv ℝ f y)) 0

theorem averagedTaylorPolynomial_apply
    {K : Set (SpatialCoordinates d)} (hK : IsCompact K)
    {f : SpatialCoordinates d → ℝ} (hf : ContDiff ℝ 1 f) (x : SpatialCoordinates d) :
    averagedTaylorPolynomial K f x = (∫ y in K, f y+fderiv ℝ f y (x-y))/volume.real K := by
  have hdf := hf.continuous_fderiv (by simp)
  have ha : Continuous (fun y => f y-fderiv ℝ f y y) := hf.continuous.sub (hdf.clm_apply continuous_id)
  have hb : Continuous (fun y => fderiv ℝ f y x) := hdf.clm_apply continuous_const
  rw [averagedTaylorPolynomial,affineJetPolynomial_apply,sub_zero]
  simp only [smul_apply,smul_eq_mul]
  rw [ContinuousLinearMap.integral_apply (hdf.continuousOn.integrableOn_compact hK)]
  have he (y : SpatialCoordinates d) : f y+fderiv ℝ f y (x-y) =
      (f y-fderiv ℝ f y y)+fderiv ℝ f y x := by rw [map_sub]; ring
  simp_rw [he]
  rw [integral_add (ha.continuousOn.integrableOn_compact hK) (hb.continuousOn.integrableOn_compact hK)]
  ring

theorem averagedTaylorPolynomial_error
    {K : Set (SpatialCoordinates d)} (hK : IsCompact K) (hc : Convex ℝ K)
    (hvol : 0 < volume.real K) (hd : d ≤ 3)
    {f : SpatialCoordinates d → ℝ} (hf : ContDiff ℝ 2 f)
    {D : ℝ} (hD : 0 ≤ D) (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {x : SpatialCoordinates d} (hx : x ∈ K) :
    |f x-averagedTaylorPolynomial K f x| ≤
      2*D^2*Real.sqrt (volume.real K*(∫ y in K, ‖iteratedFDeriv ℝ 2 f y‖^2))/volume.real K := by
  rw [averagedTaylorPolynomial_apply hK (hf.of_le (by norm_num))]
  have he : f x-(∫ y in K, f y+fderiv ℝ f y (x-y))/volume.real K =
      (volume.real K*f x-(∫ y in K, f y+fderiv ℝ f y (x-y)))/volume.real K := by
    field_simp
  rw [he,abs_div,abs_of_pos hvol]
  exact div_le_div_of_nonneg_right
    (convex_smooth_averaged_taylor_error hK hc hd hf hx hD (hdiam x hx)) hvol.le

theorem simplexNodal_smooth_h2_value_error
    (T : Affine.Simplex ℝ (SpatialCoordinates d) d) (hd : d ≤ 3)
    {f : SpatialCoordinates d → ℝ} (hf : ContDiff ℝ 2 f)
    {D : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ x ∈ simplicialCell T.points, ∀ y ∈ simplicialCell T.points, dist x y ≤ D)
    {x : SpatialCoordinates d} (hx : x ∈ simplicialCell T.points) :
    |f x-simplexNodalInterpolant T (fun i => f (T.points i)) x| ≤
      4*D^2*Real.sqrt (volume.real (simplicialCell T.points)*
        (∫ y in simplicialCell T.points, ‖iteratedFDeriv ℝ 2 f y‖^2))/volume.real (simplicialCell T.points) := by
  have hvol : 0 < volume.real (simplicialCell T.points) := ENNReal.toReal_pos
    (Measure.measure_pos_of_nonempty_interior volume
      (simplicialCell_interior_nonempty T)).ne' (simplicialCell_compact _).measure_ne_top
  have hb := simplexNodal_error_of_affine_approximation T f
    (averagedTaylorPolynomial (simplicialCell T.points) f)
    (fun y hy => averagedTaylorPolynomial_error (simplicialCell_compact T.points)
      (simplicialCell_convex T.points) hvol hd hf hD hdiam hy) hx
  exact hb.trans_eq (by ring)

theorem simplexNodal_smooth_h2_value_integral
    (T : Affine.Simplex ℝ (SpatialCoordinates d) d) (hd : d ≤ 3)
    {f : SpatialCoordinates d → ℝ} (hf : ContDiff ℝ 2 f)
    {D : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ x ∈ simplicialCell T.points, ∀ y ∈ simplicialCell T.points, dist x y ≤ D) :
    (∫ x in simplicialCell T.points, (f x-simplexNodalInterpolant T (fun i => f (T.points i)) x)^2) ≤
      16*D^4*(∫ y in simplicialCell T.points, ‖iteratedFDeriv ℝ 2 f y‖^2) := by
  let K := simplicialCell T.points
  let H := ∫ y in K, ‖iteratedFDeriv ℝ 2 f y‖^2
  let V := volume.real K
  let C := 4*D^2*Real.sqrt (V*H)/V
  have hV : 0 < V := ENNReal.toReal_pos
    (Measure.measure_pos_of_nonempty_interior volume
      (simplicialCell_interior_nonempty T)).ne' (simplicialCell_compact _).measure_ne_top
  have hH : 0 ≤ H := integral_nonneg fun y => sq_nonneg _
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have herr : Continuous (fun x => (f x-simplexNodalInterpolant T (fun i => f (T.points i)) x)^2) :=
    (hf.continuous.sub (simplexNodalInterpolant T _).continuous_of_finiteDimensional).pow 2
  calc
    _ ≤ ∫ _x in K, C^2 := by
      apply integral_mono_ae (herr.continuousOn.integrableOn_compact (simplicialCell_compact T.points))
        (integrableOn_const (simplicialCell_compact T.points).measure_ne_top)
      filter_upwards [ae_restrict_mem (simplicialCell_measurable T.points)] with x hx
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr
        (simplexNodal_smooth_h2_value_error T hd hf hD hdiam hx)
    _ = 16*D^4*H := by
      rw [integral_const,measureReal_restrict_apply_univ,smul_eq_mul]
      change V*C^2=16*D^4*H
      dsimp only [C]
      rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt (mul_nonneg hV.le hH)]
      field_simp
      ring

end Carleman
