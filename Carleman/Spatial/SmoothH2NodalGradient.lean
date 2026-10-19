module

public import Carleman.Spatial.SmoothH2NodalError
public import Carleman.Spatial.ConvexSmoothPoincare

/-! Actual gradient errors controlled by the L² Hessian. Together with the
value estimate this is the smooth local H² nodal estimate; weak-state closure
and the global conforming interpolation remain separate obligations. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem derivativeOneFiber_norm_sq (A : SpatialCoordinates d →L[ℝ] ℝ) :
    ‖derivativeOneFiber A‖^2 = ∑ i : Fin d, (A (EuclideanSpace.basisFun (Fin d) ℝ i))^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  exact (Equiv.sum_comp Sym.oneEquiv
    (fun α : Sym (Fin d) 1 => (derivativeOneFiber A α)^2)).symm

set_option maxHeartbeats 1200000 in
theorem smooth_directional_gradient_bound {f : SpatialCoordinates d → ℝ}
    (hf : ContDiff ℝ 2 f) (x e : SpatialCoordinates d) :
    ‖fderiv ℝ (fun y => fderiv ℝ f y e) x‖ ≤ ‖iteratedFDeriv ℝ 2 f x‖*‖e‖ := by
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  rw [fderiv_clm_apply (hdf.differentiable (by simp) x) (differentiableAt_const e),
    fderiv_const_apply,ContinuousLinearMap.comp_zero,zero_add]
  have hb := ((fderiv ℝ (fderiv ℝ f) x).flip).le_opNorm e
  rw [ContinuousLinearMap.opNorm_flip] at hb
  have hn : ‖fderiv ℝ (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
    rw [← norm_iteratedFDeriv_one (fderiv ℝ f),norm_iteratedFDeriv_fderiv]
  rw [hn] at hb
  exact hb

theorem averagedTaylorPolynomial_derivative
    (K : Set (SpatialCoordinates d)) (f : SpatialCoordinates d → ℝ) :
    affineScalarDerivative (averagedTaylorPolynomial K f) =
      (volume.real K)⁻¹ • (∫ y in K, fderiv ℝ f y) :=
  affineJetPolynomial_derivative _ _ 0

theorem averagedTaylorPolynomial_gradient_integral
    {K : Set (SpatialCoordinates d)} (hK : IsCompact K) (hc : Convex ℝ K)
    (hvol : 0 < volume.real K) {f : SpatialCoordinates d → ℝ} (hf : ContDiff ℝ 2 f)
    {D : ℝ} (hD : 0 ≤ D) (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) :
    (∫ x in K, ‖derivativeOneFiber (fderiv ℝ f x-
      affineScalarDerivative (averagedTaylorPolynomial K f))‖^2) ≤
      (d:ℝ)*((2:ℝ)^d/2)*D^2*(∫ y in K, ‖iteratedFDeriv ℝ 2 f y‖^2) := by
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hH : Continuous (fun y => ‖iteratedFDeriv ℝ 2 f y‖^2) :=
    (hf.continuous_iteratedFDeriv (by simp)).norm.pow 2
  let g := fun (i : Fin d) (x : SpatialCoordinates d) => fderiv ℝ f x (EuclideanSpace.basisFun (Fin d) ℝ i)
  have hg (i : Fin d) : ContDiff ℝ 1 (g i) := hdf.clm_apply contDiff_const
  have hid (x : SpatialCoordinates d) :
      ‖derivativeOneFiber (fderiv ℝ f x-affineScalarDerivative (averagedTaylorPolynomial K f))‖^2 =
      ∑ i : Fin d, (g i x-(∫ y in K, g i y)/volume.real K)^2 := by
    rw [derivativeOneFiber_norm_sq,averagedTaylorPolynomial_derivative]
    apply Finset.sum_congr rfl
    intro i _
    simp only [sub_apply,smul_apply,smul_eq_mul,
      ContinuousLinearMap.integral_apply (hdf.continuous.continuousOn.integrableOn_compact hK),g]
    congr 1
    ring
  simp_rw [hid]
  rw [integral_finsetSum (f := fun i x => (g i x-(∫ y in K, g i y)/volume.real K)^2) Finset.univ (fun i _ =>
    (((hg i).continuous.sub continuous_const).pow 2).continuousOn.integrableOn_compact hK)]
  calc
    _ ≤ ∑ _i : Fin d, ((2:ℝ)^d/2)*D^2*(∫ y in K, ‖iteratedFDeriv ℝ 2 f y‖^2) := by
      apply Finset.sum_le_sum
      intro i _
      apply (convex_smooth_mean_poincare hK hc hvol (hg i) hD hdiam).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply integral_mono_ae
      · exact (((hg i).continuous_fderiv (by simp)).norm.pow 2).continuousOn.integrableOn_compact hK
      · exact hH.continuousOn.integrableOn_compact hK
      · apply Filter.Eventually.of_forall
        intro x
        apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
        have hh := smooth_directional_gradient_bound hf x (EuclideanSpace.basisFun (Fin d) ℝ i)
        simpa only [(EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.norm_eq_one i,mul_one] using hh
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

set_option maxHeartbeats 1200000 in
theorem simplexNodal_smooth_h2_gradient_integral
    (T : Affine.Simplex ℝ (SpatialCoordinates d) d) (hd : d ≤ 3)
    {f : SpatialCoordinates d → ℝ} (hf : ContDiff ℝ 2 f)
    {a : SpatialCoordinates d} {r D κ : ℝ} (hr : 0 < r) (hD : 0 ≤ D)
    (hball : Metric.ball a r ⊆ simplicialCell T.points) (hshape : D ≤ κ*r)
    (hdiam : ∀ x ∈ simplicialCell T.points, ∀ y ∈ simplicialCell T.points, dist x y ≤ D) :
    (∫ x in simplicialCell T.points, ‖derivativeOneFiber (fderiv ℝ f x-
      affineScalarDerivative (simplexNodalInterpolant T (fun i => f (T.points i))))‖^2) ≤
      ((2:ℝ)^d*(d:ℝ)+128*κ^2*‖derivativeOneFiber (d := d)‖^2)*D^2*
        (∫ y in simplicialCell T.points, ‖iteratedFDeriv ℝ 2 f y‖^2) := by
  let K := simplicialCell T.points
  let p := averagedTaylorPolynomial K f
  let I := simplexNodalInterpolant T (fun i => f (T.points i))
  let V := volume.real K
  let H := ∫ y in K, ‖iteratedFDeriv ℝ 2 f y‖^2
  let F := ‖derivativeOneFiber (d := d)‖
  let R := 2*D^2*Real.sqrt (V*H)/V
  let B := F*(4*R/r)
  have hV : 0 < V := ENNReal.toReal_pos (Measure.measure_pos_of_nonempty_interior volume
    (simplicialCell_interior_nonempty T)).ne' (simplicialCell_compact _).measure_ne_top
  have hH : 0 ≤ H := integral_nonneg fun y => sq_nonneg _
  have hF : 0 ≤ F := norm_nonneg (derivativeOneFiber (d := d))
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hκ : 0 ≤ κ := by nlinarith only [hr,hD,hshape]
  have hp (y : SpatialCoordinates d) (hy : y ∈ K) : |f y-p y| ≤ R :=
    averagedTaylorPolynomial_error (simplicialCell_compact T.points)
      (simplicialCell_convex T.points) hV hd hf hD hdiam hy
  have hIp (y : SpatialCoordinates d) (hy : y ∈ Metric.ball a r) : |(I-p) y| ≤ R := by
    rw [← simplexNodalInterpolant_sub_affine]
    exact simplexNodalInterpolant_abs_le T _ R
      (fun i => hp _ (subset_convexHull ℝ _ (mem_range_self i))) (hball hy)
  have hlin : affineScalarDerivative (I-p)=affineScalarDerivative I-affineScalarDerivative p :=
    (affineScalar_hasFDerivAt (I-p) a).unique
      ((affineScalar_hasFDerivAt I a).sub (affineScalar_hasFDerivAt p a))
  have hI := affineScalarDerivative_inball_bound (I-p) hr hR hIp
  rw [hlin] at hI
  have hb : ‖derivativeOneFiber (affineScalarDerivative p-affineScalarDerivative I)‖ ≤ B := by
    calc
      _ = ‖derivativeOneFiber (affineScalarDerivative I-affineScalarDerivative p)‖ := by
        rw [map_sub,map_sub,norm_sub_rev]
      _ ≤ F*‖affineScalarDerivative I-affineScalarDerivative p‖ := derivativeOneFiber.le_opNorm _
      _ ≤ B := mul_le_mul_of_nonneg_left hI hF
  have hpoint (x : SpatialCoordinates d) :
      ‖derivativeOneFiber (fderiv ℝ f x-affineScalarDerivative I)‖^2 ≤
      2*‖derivativeOneFiber (fderiv ℝ f x-affineScalarDerivative p)‖^2+2*B^2 := by
    have he : fderiv ℝ f x-affineScalarDerivative I =
        (fderiv ℝ f x-affineScalarDerivative p)+(affineScalarDerivative p-affineScalarDerivative I) := by abel
    rw [he,map_add]
    have ht := (norm_add_le (derivativeOneFiber (fderiv ℝ f x-affineScalarDerivative p))
      (derivativeOneFiber (affineScalarDerivative p-affineScalarDerivative I))).trans
      (add_le_add le_rfl hb)
    have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) hB)).mpr ht
    nlinarith only [hs,sq_nonneg (‖derivativeOneFiber (fderiv ℝ f x-affineScalarDerivative p)‖-B)]
  have hdf := hf.continuous_fderiv (by norm_num)
  have hcont (A : SpatialCoordinates d →L[ℝ] ℝ) :
      Continuous (fun x => ‖derivativeOneFiber (fderiv ℝ f x-A)‖^2) :=
    (derivativeOneFiber.continuous.comp (hdf.sub continuous_const)).norm.pow 2
  have hint := integral_mono_ae (μ := volume.restrict K) ((hcont (affineScalarDerivative I)).continuousOn.integrableOn_compact
    (simplicialCell_compact T.points))
    ((((hcont (affineScalarDerivative p)).const_mul 2).add continuous_const).continuousOn.integrableOn_compact
      (simplicialCell_compact T.points)) (Filter.Eventually.of_forall hpoint)
  simp only [Pi.add_apply] at hint
  rw [integral_add (μ := volume.restrict K) (((hcont (affineScalarDerivative p)).const_mul 2).continuousOn.integrableOn_compact
    (simplicialCell_compact T.points)) (integrableOn_const (simplicialCell_compact T.points).measure_ne_top),
    integral_const_mul,integral_const,measureReal_restrict_apply_univ,smul_eq_mul] at hint
  have hpgrad := averagedTaylorPolynomial_gradient_integral (simplicialCell_compact T.points)
    (simplicialCell_convex T.points) hV hf hD hdiam
  have hratio : D^2/r^2 ≤ κ^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
    have ht := (sq_le_sq₀ hD (mul_nonneg hκ hr.le)).mpr hshape
    simpa only [mul_pow] using ht
  have hcancel : V*B^2=64*F^2*(D^2/r^2)*D^2*H := by
    dsimp only [B,R]
    simp only [mul_pow,div_pow,Real.sq_sqrt (mul_nonneg hV.le hH)]
    field_simp
    ring
  have hBsq : V*B^2 ≤ 64*F^2*κ^2*D^2*H := by
    rw [hcancel]
    nlinarith only [mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 64*F^2*D^2*H)]
  change (∫ x in K, ‖derivativeOneFiber (fderiv ℝ f x-affineScalarDerivative I)‖^2) ≤ _
  calc
    _ ≤ 2*((d:ℝ)*((2:ℝ)^d/2)*D^2*H)+2*(V*B^2) := by
      nlinarith only [hint,hpgrad]
    _ ≤ 2*((d:ℝ)*((2:ℝ)^d/2)*D^2*H)+2*(64*F^2*κ^2*D^2*H) := by linarith only [hBsq]
    _ = _ := by ring

end Carleman
