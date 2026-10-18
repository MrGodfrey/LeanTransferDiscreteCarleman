module

public import Carleman.Spatial.ConvexSegmentIntegral
public import Carleman.Spatial.SmoothSegmentSquare
public import Carleman.Spatial.MeanSquareDifference

/-! Mean Poincaré on a compact convex cell for genuine smooth functions,
with a dimension-only constant and the integral of the actual derivative. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {K : Set (SpatialCoordinates d)}

theorem convex_half_segment_integral_le (hK : IsCompact K) (hc : Convex ℝ K)
    {g : SpatialCoordinates d → ℝ} (hg : Continuous g) (hpos : ∀ z, 0 ≤ g z)
    {y : SpatialCoordinates d} (hy : y ∈ K) :
    (∫ x in K, ∫ s in Icc (0:ℝ) (1/2), g (x+s • (y-x))) ≤
      (2:ℝ)^d/2*(∫ x in K, g x) := by
  have hG : Continuous (fun p : SpatialCoordinates d × ℝ => g (p.1+p.2 • (y-p.1))) := by
    fun_prop
  have hi : Integrable (fun p : SpatialCoordinates d × ℝ => g (p.1+p.2 • (y-p.1)))
      ((volume.restrict K).prod (volume.restrict (Icc (0:ℝ) (1/2)))) := by
    rw [Measure.prod_restrict]
    exact hG.continuousOn.integrableOn_compact (hK.prod isCompact_Icc)
  rw [integral_integral_swap hi]
  have hb : ∀ᵐ s ∂volume.restrict (Icc (0:ℝ) (1/2)),
      (∫ x in K, g (x+s • (y-x))) ≤ (2:ℝ)^d*(∫ x in K, g x) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have he (x : SpatialCoordinates d) : x+s • (y-x)=(1-s) • x+(1-(1-s)) • y := by module
    simp_rw [he]
    exact integral_convex_segment_le hc (hg.continuousOn.integrableOn_compact hK)
      (Filter.Eventually.of_forall hpos) (by linarith [hs.2]) (by linarith [hs.1]) hy
  have he := integral_mono_ae hi.integral_prod_right (integrable_const _) hb
  simp only [integral_const,smul_eq_mul,measureReal_restrict_apply_univ,
    Real.volume_real_Icc_of_le (by norm_num : (0:ℝ) ≤ 1/2),sub_zero] at he
  exact he.trans_eq (by ring)

theorem convex_smooth_midpoint_error (hK : IsCompact K) (hc : Convex ℝ K)
    {f : SpatialCoordinates d → ℝ} (hf : ContDiff ℝ 1 f)
    {D : ℝ} (hD : 0 ≤ D) {y : SpatialCoordinates d} (hy : y ∈ K)
    (hdiam : ∀ x ∈ K, ‖y-x‖ ≤ D) :
    (∫ x in K, (f x-f (x+(1/2:ℝ) • (y-x)))^2) ≤
      (2:ℝ)^d/4*D^2*(∫ x in K, ‖fderiv ℝ f x‖^2) := by
  let g := fun x => ‖fderiv ℝ f x‖^2
  have hg : Continuous g := (hf.continuous_fderiv (by simp)).norm.pow 2
  have hgpos (x : SpatialCoordinates d) : 0 ≤ g x := sq_nonneg _
  have hG : Continuous (fun p : SpatialCoordinates d × ℝ => g (p.1+p.2 • (y-p.1))) := by
    fun_prop
  have havg : Continuous (fun x => ∫ s in Icc (0:ℝ) (1/2), g (x+s • (y-x))) :=
    continuous_parametric_integral_of_continuous hG isCompact_Icc
  have herr : Continuous (fun x => (f x-f (x+(1/2:ℝ) • (y-x)))^2) := by
    fun_prop
  have hb : ∀ᵐ x ∂volume.restrict K,
      (f x-f (x+(1/2:ℝ) • (y-x)))^2 ≤
        (1/2:ℝ)*D^2*(∫ s in Icc (0:ℝ) (1/2), g (x+s • (y-x))) := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    have he := smooth_segment_difference_sq hf x (y-x) (by norm_num : (0:ℝ) ≤ 1/2)
    rw [← integral_Icc_eq_integral_Ioc] at he
    have hd := (sq_le_sq₀ (norm_nonneg (y-x)) hD).mpr (hdiam x hx)
    have hp : 0 ≤ ∫ s in Icc (0:ℝ) (1/2), g (x+s • (y-x)) := integral_nonneg fun s => hgpos _
    calc
      _ = (f (x+(1/2:ℝ) • (y-x))-f x)^2 := by ring
      _ ≤ _ := he
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num)) hp
  have he := integral_mono_ae (herr.continuousOn.integrableOn_compact hK)
    ((havg.const_mul ((1/2:ℝ)*D^2)).continuousOn.integrableOn_compact hK) hb
  rw [integral_const_mul] at he
  have ha := convex_half_segment_integral_le hK hc hg hgpos hy
  calc
    _ ≤ _ := he
    _ ≤ ((1/2:ℝ)*D^2)*((2:ℝ)^d/2*(∫ x in K, g x)) :=
      mul_le_mul_of_nonneg_left ha (by positivity)
    _ = _ := by ring

theorem convex_smooth_pairwise_bound (hK : IsCompact K) (hc : Convex ℝ K)
    {f : SpatialCoordinates d → ℝ} (hf : ContDiff ℝ 1 f)
    {D : ℝ} (hD : 0 ≤ D) (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) :
    (∫ x in K, ∫ y in K, (f x-f y)^2) ≤
      (2:ℝ)^d*volume.real K*D^2*(∫ x in K, ‖fderiv ℝ f x‖^2) := by
  let : IsFiniteMeasure (volume.restrict K) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top⟩
  let μ := volume.restrict K
  let R := fun p : SpatialCoordinates d × SpatialCoordinates d =>
    (f p.1-f (p.1+(1/2:ℝ) • (p.2-p.1)))^2
  let B := (2:ℝ)^d/4*D^2*(∫ x in K, ‖fderiv ℝ f x‖^2)
  have hR : Continuous R := by dsimp only [R]; fun_prop
  have hiR : Integrable R (μ.prod μ) := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    exact hR.continuousOn.integrableOn_compact (hK.prod hK)
  have hb : (∫ p, R p ∂μ.prod μ) ≤ volume.real K*B := by
    rw [integral_prod_symm R hiR]
    have hh : ∀ᵐ y ∂μ, (∫ x, R (x,y) ∂μ) ≤ B := by
      filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
      exact convex_smooth_midpoint_error hK hc hf hD hy (fun x hx => by
        simpa only [dist_eq_norm] using hdiam y hy x hx)
    have he := integral_mono_ae hiR.integral_prod_right (integrable_const B) hh
    simpa only [integral_const,smul_eq_mul,μ,measureReal_restrict_apply_univ] using he
  have hiF : Integrable (fun p : SpatialCoordinates d × SpatialCoordinates d => (f p.1-f p.2)^2)
      (μ.prod μ) := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    apply ContinuousOn.integrableOn_compact (hK.prod hK)
    exact ((hf.continuous.comp continuous_fst).sub (hf.continuous.comp continuous_snd)).pow 2 |>.continuousOn
  have hpoint (p : SpatialCoordinates d × SpatialCoordinates d) :
      (f p.1-f p.2)^2 ≤ 2*R p+2*R p.swap := by
    have hm : p.2+(1/2:ℝ) • (p.1-p.2)=p.1+(1/2:ℝ) • (p.2-p.1) := by module
    dsimp only [R,Prod.swap] at *
    rw [hm]
    nlinarith only [sq_nonneg (f p.1+f p.2-2*f (p.1+(1/2:ℝ) • (p.2-p.1)))]
  have hiSum : Integrable (fun p => 2*R p+2*R p.swap) (μ.prod μ) :=
    (hiR.const_mul 2).add (hiR.swap.const_mul 2)
  have hiSwap : Integrable (fun p => 2*R p.swap) (μ.prod μ) := hiR.swap.const_mul 2
  have he := integral_mono_ae hiF hiSum (Filter.Eventually.of_forall hpoint)
  rw [integral_add (hiR.const_mul 2) hiSwap,integral_const_mul,
    integral_const_mul,integral_prod_swap] at he
  rw [← integral_prod _ hiF]
  change (∫ p, (f p.1-f p.2)^2 ∂μ.prod μ) ≤ _
  calc
    _ ≤ _ := he
    _ ≤ 4*(volume.real K*B) := by linarith [hb]
    _ = _ := by dsimp only [B]; ring

theorem convex_smooth_mean_poincare (hK : IsCompact K) (hc : Convex ℝ K)
    (hvol : 0 < volume.real K)
    {f : SpatialCoordinates d → ℝ} (hf : ContDiff ℝ 1 f)
    {D : ℝ} (hD : 0 ≤ D) (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) :
    (∫ x in K, (f x-(∫ y in K, f y)/volume.real K)^2) ≤
      (2:ℝ)^d/2*D^2*(∫ x in K, ‖fderiv ℝ f x‖^2) := by
  let : IsFiniteMeasure (volume.restrict K) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top⟩
  have hm : MemLp f 2 (volume.restrict K) := by
    apply (memLp_two_iff_integrable_sq hf.continuous.aestronglyMeasurable).mpr
    exact (hf.continuous.pow 2).continuousOn.integrableOn_compact hK
  have he := mean_square_pairwise_identity hm (by simpa using hvol)
  simp only [measureReal_restrict_apply_univ] at he
  apply (mul_le_mul_iff_right₀ (mul_pos (by norm_num : (0:ℝ) < 2) hvol)).mp
  rw [he]
  exact (convex_smooth_pairwise_bound hK hc hf hD hdiam).trans_eq (by ring)

end Carleman
