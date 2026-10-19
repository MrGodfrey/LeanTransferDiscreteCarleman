module

public import Carleman.Spatial.SmoothAveragedTaylor
public import Carleman.Continuous.BochnerNormAlgebra

/-! An actual point-evaluation estimate on a compact convex domain in
dimensions at most three, in the full L² value/gradient/Hessian norm. This
will control uniform limits of the genuine local smooth approximations. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {K : Set (SpatialCoordinates d)}

theorem continuous_memLp_compact {E : Type*} [NormedAddCommGroup E]
    (hK : IsCompact K) {F : SpatialCoordinates d → E} (hF : Continuous F) :
    MemLp F 2 (volume.restrict K) :=
  (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mpr
    ((hF.norm.pow 2).continuousOn.integrableOn_compact hK)

theorem compact_integral_norm_le_l2 {E : Type*} [NormedAddCommGroup E]
    (hK : IsCompact K) {F : SpatialCoordinates d → E} (hF : Continuous F) :
    (∫ y in K, ‖F y‖) ≤ Real.sqrt (volume.real K)*bochnerL2Norm (volume.restrict K) F := by
  let : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  have hm := continuous_memLp_compact hK hF
  have he := integral_mul_sq_le (memLp_const (1:ℝ)) hm.norm
  simp only [one_mul,one_pow,integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply_univ] at he
  rw [integral_sq_eq_bochnerL2Norm_sq hm.norm,bochnerL2Norm_norm _ hm] at he
  apply (sq_le_sq₀ (integral_nonneg fun y => norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (bochnerL2Norm_nonneg _))).mp
  simpa only [mul_pow,Real.sq_sqrt measureReal_nonneg] using he

theorem convex_smooth_h2_point_bound (hK : IsCompact K) (hc : Convex ℝ K)
    (hvol : 0 < volume.real K) (hd : d ≤ 3)
    {f : SpatialCoordinates d → ℝ} (hf : ContDiff ℝ 2 f)
    {D : ℝ} (hD : 0 ≤ D) (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {x : SpatialCoordinates d} (hx : x ∈ K) :
    |f x| ≤ (Real.sqrt (volume.real K)/volume.real K)*
      (bochnerL2Norm (volume.restrict K) f + D*bochnerL2Norm (volume.restrict K) (fderiv ℝ f) +
        2*D^2*bochnerL2Norm (volume.restrict K) (iteratedFDeriv ℝ 2 f)) := by
  let V := volume.real K
  let L₀ := bochnerL2Norm (volume.restrict K) f
  let L₁ := bochnerL2Norm (volume.restrict K) (fderiv ℝ f)
  let L₂ := bochnerL2Norm (volume.restrict K) (iteratedFDeriv ℝ 2 f)
  let g := fun y => f y+fderiv ℝ f y (x-y)
  have hdf := hf.continuous_fderiv (by norm_num)
  have hH := hf.continuous_iteratedFDeriv (m := 2) (by simp)
  have hg : Continuous g := hf.continuous.add (hdf.clm_apply (continuous_const.sub continuous_id))
  have hnorm (y : SpatialCoordinates d) (hy : y ∈ K) : |g y| ≤ ‖f y‖+D*‖fderiv ℝ f y‖ := by
    have hdxy : ‖x-y‖ ≤ D := by simpa only [dist_eq_norm] using hdiam x hx y hy
    calc
      _ ≤ ‖f y‖+‖fderiv ℝ f y (x-y)‖ := norm_add_le _ _
      _ ≤ ‖f y‖+D*‖fderiv ℝ f y‖ := add_le_add le_rfl
        (((fderiv ℝ f y).le_opNorm (x-y)).trans
          ((mul_le_mul_of_nonneg_left hdxy (norm_nonneg _)).trans_eq (mul_comm _ _)))
  have hmean : |∫ y in K, g y| ≤ Real.sqrt V*L₀+D*(Real.sqrt V*L₁) := by
    calc
      _ ≤ ∫ y in K, |g y| := abs_integral_le_integral_abs
      _ ≤ ∫ y in K, ‖f y‖+D*‖fderiv ℝ f y‖ := by
        apply integral_mono_ae (hg.abs.continuousOn.integrableOn_compact hK)
          ((hf.continuous.norm.add (hdf.norm.const_mul D)).continuousOn.integrableOn_compact hK)
        filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
        exact hnorm y hy
      _ = (∫ y in K, ‖f y‖)+D*(∫ y in K, ‖fderiv ℝ f y‖) := by
        rw [integral_add (hf.continuous.norm.continuousOn.integrableOn_compact hK)
          ((hdf.norm.const_mul D).continuousOn.integrableOn_compact hK),integral_const_mul]
      _ ≤ _ := add_le_add (compact_integral_norm_le_l2 hK hf.continuous)
        (mul_le_mul_of_nonneg_left (compact_integral_norm_le_l2 hK hdf) hD)
  have hroot : Real.sqrt (V*(∫ y in K, ‖iteratedFDeriv ℝ 2 f y‖^2)) = Real.sqrt V*L₂ := by
    rw [integral_sq_eq_bochnerL2Norm_sq (continuous_memLp_compact hK hH).norm,
      bochnerL2Norm_norm _ (continuous_memLp_compact hK hH),Real.sqrt_mul hvol.le,
      Real.sqrt_sq (bochnerL2Norm_nonneg _)]
  have ht := convex_smooth_averaged_taylor_error hK hc hd hf hx hD (hdiam x hx)
  change |V*f x-∫ y in K, g y| ≤ 2*D^2*Real.sqrt (V*(∫ y in K, ‖iteratedFDeriv ℝ 2 f y‖^2)) at ht
  rw [hroot] at ht
  have htri : V*|f x| ≤ |V*f x-∫ y in K, g y|+|∫ y in K, g y| := by
    calc
      _ = |V*f x| := by rw [abs_mul,abs_of_pos (show 0 < V from hvol)]
      _ = |(V*f x-∫ y in K, g y)+(∫ y in K, g y)| := by congr 1; ring
      _ ≤ _ := by simpa only [Real.norm_eq_abs] using
        norm_add_le (V*f x-∫ y in K, g y) (∫ y in K, g y)
  have hbound : V*|f x| ≤ Real.sqrt V*(L₀+D*L₁+2*D^2*L₂) := by nlinarith only [htri,ht,hmean]
  have hfinal : |f x| ≤ Real.sqrt V*(L₀+D*L₁+2*D^2*L₂)/V :=
    (le_div_iff₀ hvol).mpr (by nlinarith only [hbound])
  exact hfinal.trans_eq (by ring)

end Carleman
