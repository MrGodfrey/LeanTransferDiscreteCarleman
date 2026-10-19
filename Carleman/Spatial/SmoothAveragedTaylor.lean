module

public import Carleman.Spatial.ConvexSegmentIntegral
public import Carleman.Spatial.RealL2Integral
public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Actual second-order Taylor remainders and the exact Jacobian bound on
contracting segments. These estimates prepare the full H² nodal interpolation
argument; no weak Sobolev class is evaluated at a point in this module. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem smooth_first_taylor_integral {f : SpatialCoordinates d → ℝ}
    (hf : ContDiff ℝ 2 f) (x y : SpatialCoordinates d) :
    f x-f y-fderiv ℝ f y (x-y) =
      ∫ t in (0:ℝ)..1, (1-t)*iteratedFDeriv ℝ 2 f (y+t • (x-y)) (fun _ => x-y) := by
  have he := map_add_eq_sum_add_integral_iteratedFDeriv (n := 1) (x := y) (y := x-y)
    (fun t _ => hf.contDiffAt)
  simp only [Nat.reduceAdd,Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
    Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,inv_one,
    iteratedFDeriv_zero_apply,iteratedFDeriv_one_apply,pow_one,smul_eq_mul,
    add_sub_cancel] at he
  linarith only [he]

theorem integral_convex_segment_jacobian_le
    {K : Set (SpatialCoordinates d)} (hc : Convex ℝ K)
    {f : SpatialCoordinates d → ℝ} (hf : IntegrableOn f K)
    (hpos : 0 ≤ᵐ[volume.restrict K] f)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {x : SpatialCoordinates d} (hx : x ∈ K) :
    (∫ y in K, f (r • y+(1-r) • x)) ≤ (r^d)⁻¹*(∫ y in K, f y) := by
  rw [integral_comp_scalar_affine K f hr]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (pow_nonneg hr.le _))
  apply setIntegral_mono_set hf hpos
  apply Filter.Eventually.of_forall
  rintro _ ⟨y,hy,rfl⟩
  exact hc hy hx hr.le (sub_nonneg.mpr hr1) (by ring)

theorem convex_segment_norm_integral_sq
    {K : Set (SpatialCoordinates d)} (hK : IsCompact K) (hc : Convex ℝ K)
    {E : Type*} [NormedAddCommGroup E]
    {F : SpatialCoordinates d → E} (hF : Continuous F)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {x : SpatialCoordinates d} (hx : x ∈ K) :
    (∫ y in K, ‖F (r • y+(1-r) • x)‖)^2 ≤
      volume.real K*(r^d)⁻¹*(∫ y in K, ‖F y‖^2) := by
  let : IsFiniteMeasure (volume.restrict K) :=
    ⟨by simpa using hK.measure_lt_top⟩
  have hG : Continuous (fun y => ‖F (r • y+(1-r) • x)‖) := by fun_prop
  have hm : MemLp (fun y => ‖F (r • y+(1-r) • x)‖) 2 (volume.restrict K) := by
    apply (memLp_two_iff_integrable_sq hG.aestronglyMeasurable).mpr
    exact (hG.pow 2).continuousOn.integrableOn_compact hK
  have he := integral_mul_sq_le (memLp_const (1:ℝ)) hm
  simp only [one_mul,one_pow,integral_const,smul_eq_mul,mul_one,
    measureReal_restrict_apply_univ] at he
  have hj := integral_convex_segment_jacobian_le hc
    ((hF.norm.pow 2).continuousOn.integrableOn_compact hK)
    (Filter.Eventually.of_forall (fun y => sq_nonneg ‖F y‖)) hr hr1 hx
  simp only [Pi.pow_apply] at hj
  exact he.trans ((mul_le_mul_of_nonneg_left hj (measureReal_nonneg)).trans_eq (by ring))

theorem convex_segment_lowdim_kernel_bound
    {K : Set (SpatialCoordinates d)} (hK : IsCompact K) (hc : Convex ℝ K)
    (hd : d ≤ 3) {E : Type*} [NormedAddCommGroup E]
    {F : SpatialCoordinates d → E} (hF : Continuous F)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {x : SpatialCoordinates d} (hx : x ∈ K) :
    r*(∫ y in K, ‖F (r • y+(1-r) • x)‖) ≤
      Real.sqrt (volume.real K*(∫ y in K, ‖F y‖^2))/Real.sqrt r := by
  let I := ∫ y in K, ‖F (r • y+(1-r) • x)‖
  let A := volume.real K*(∫ y in K, ‖F y‖^2)
  have hA : 0 ≤ A := mul_nonneg measureReal_nonneg (integral_nonneg fun y => sq_nonneg _)
  have hI : 0 ≤ I := integral_nonneg fun y => norm_nonneg _
  have hb := convex_segment_norm_integral_sq hK hc hF hr hr1 hx
  have hb' : I^2 ≤ A/(r^d) := hb.trans_eq (by dsimp only [A]; ring)
  have hp : r^3 ≤ r^d := pow_le_pow_of_le_one hr.le hr1 hd
  have hs : (r*I*Real.sqrt r)^2 ≤ A := by
    have ht := (le_div_iff₀ (pow_pos hr d)).mp hb'
    have hh := mul_le_mul_of_nonneg_left hp (sq_nonneg I)
    rw [mul_pow,mul_pow,Real.sq_sqrt hr.le]
    nlinarith only [ht,hh]
  apply (le_div_iff₀ (Real.sqrt_pos.2 hr)).mpr
  apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rwa [Real.sq_sqrt hA]

theorem integrableOn_unit_inv_sqrt :
    IntegrableOn (fun r : ℝ => (Real.sqrt r)⁻¹) (Ioc 0 1) := by
  have he : (fun r : ℝ => (Real.sqrt r)⁻¹) =ᵐ[volume.restrict (Ioc (0:ℝ) 1)]
      (fun r => r^(-(1/(2:ℝ)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [Real.rpow_neg hr.1.le,Real.sqrt_eq_rpow]
  exact ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
    (by norm_num : (-1:ℝ) < -(1/(2:ℝ)))).1).congr he.symm

theorem integral_unit_inv_sqrt :
    (∫ r in Ioc (0:ℝ) 1, (Real.sqrt r)⁻¹) = 2 := by
  have he : (∫ r in Ioc (0:ℝ) 1, (Real.sqrt r)⁻¹) =
      ∫ r in (0:ℝ)..1, r^(-(1/(2:ℝ))) := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [Real.rpow_neg hr.1.le,Real.sqrt_eq_rpow]
  rw [he,integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(1/(2:ℝ))))]
  norm_num

theorem convex_segment_lowdim_integral_bound
    {K : Set (SpatialCoordinates d)} (hK : IsCompact K) (hc : Convex ℝ K)
    (hd : d ≤ 3) {E : Type*} [NormedAddCommGroup E]
    {F : SpatialCoordinates d → E} (hF : Continuous F)
    {x : SpatialCoordinates d} (hx : x ∈ K) :
    (∫ r in Ioc (0:ℝ) 1, r*(∫ y in K, ‖F (r • y+(1-r) • x)‖)) ≤
      2*Real.sqrt (volume.real K*(∫ y in K, ‖F y‖^2)) := by
  let A := Real.sqrt (volume.real K*(∫ y in K, ‖F y‖^2))
  have hG : Continuous (fun p : ℝ × SpatialCoordinates d =>
      ‖F (p.1 • p.2+(1-p.1) • x)‖) := by fun_prop
  have hI : Continuous (fun r : ℝ => ∫ y in K, ‖F (r • y+(1-r) • x)‖) :=
    continuous_parametric_integral_of_continuous hG hK
  have hi : IntegrableOn (fun r => r*(∫ y in K, ‖F (r • y+(1-r) • x)‖)) (Ioc (0:ℝ) 1) :=
    ((continuous_id.mul hI).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have he := integral_mono_ae hi (integrableOn_unit_inv_sqrt.const_mul A) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    simpa only [div_eq_mul_inv] using convex_segment_lowdim_kernel_bound hK hc hd hF hr.1 hr.2 hx)
  rw [integral_const_mul,integral_unit_inv_sqrt] at he
  exact he.trans_eq (by ring)

theorem smooth_first_taylor_contracted {f : SpatialCoordinates d → ℝ}
    (hf : ContDiff ℝ 2 f) (x y : SpatialCoordinates d) :
    f x-f y-fderiv ℝ f y (x-y) =
      ∫ r in Icc (0:ℝ) 1, r*iteratedFDeriv ℝ 2 f (r • y+(1-r) • x) (fun _ => x-y) := by
  rw [smooth_first_taylor_integral hf x y,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one]
  calc
    _ = ∫ t in (0:ℝ)..1, (1-t)*
        iteratedFDeriv ℝ 2 f ((1-t) • y+(1-(1-t)) • x) (fun _ => x-y) := by
      apply intervalIntegral.integral_congr
      intro t _
      have he : y+t • (x-y)=(1-t) • y+(1-(1-t)) • x := by module
      dsimp only
      rw [he]
    _ = _ := by
      simpa only [sub_self,sub_zero] using
        intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := 1)
          (fun r => r*iteratedFDeriv ℝ 2 f (r • y+(1-r) • x) (fun _ => x-y)) 1

theorem smooth_taylor_remainder_norm_bound {f : SpatialCoordinates d → ℝ}
    (hf : ContDiff ℝ 2 f) (x y : SpatialCoordinates d)
    {D : ℝ} (hD : 0 ≤ D) (hxy : ‖x-y‖ ≤ D) :
    |f x-f y-fderiv ℝ f y (x-y)| ≤
      D^2*(∫ r in Icc (0:ℝ) 1, r*‖iteratedFDeriv ℝ 2 f (r • y+(1-r) • x)‖) := by
  have hF : Continuous (iteratedFDeriv ℝ 2 f) := hf.continuous_iteratedFDeriv (by simp)
  have hi : Continuous (fun r : ℝ => r*‖iteratedFDeriv ℝ 2 f (r • y+(1-r) • x)‖) := by fun_prop
  rw [smooth_first_taylor_contracted hf x y,← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_const_mul]
  apply integral_mono_ae
  · apply ContinuousOn.integrableOn_compact isCompact_Icc
    fun_prop
  · exact (hi.const_mul (D^2)).continuousOn.integrableOn_compact isCompact_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hr.1]
    have hb := (iteratedFDeriv ℝ 2 f (r • y+(1-r) • x)).le_opNorm (fun _ => x-y)
    simp only [Finset.prod_const,Real.norm_eq_abs] at hb
    have hd := (sq_le_sq₀ (norm_nonneg (x-y)) hD).mpr hxy
    calc
      _ ≤ r*(‖iteratedFDeriv ℝ 2 f (r • y+(1-r) • x)‖*‖x-y‖^2) :=
        mul_le_mul_of_nonneg_left hb hr.1
      _ ≤ r*(‖iteratedFDeriv ℝ 2 f (r • y+(1-r) • x)‖*D^2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd (norm_nonneg _)) hr.1
      _ = _ := by ring

theorem convex_smooth_averaged_taylor_error
    {K : Set (SpatialCoordinates d)} (hK : IsCompact K) (hc : Convex ℝ K)
    (hd : d ≤ 3) {f : SpatialCoordinates d → ℝ} (hf : ContDiff ℝ 2 f)
    {x : SpatialCoordinates d} (hx : x ∈ K)
    {D : ℝ} (hD : 0 ≤ D) (hdiam : ∀ y ∈ K, dist x y ≤ D) :
    |volume.real K*f x-(∫ y in K, f y+fderiv ℝ f y (x-y))| ≤
      2*D^2*Real.sqrt (volume.real K*(∫ y in K, ‖iteratedFDeriv ℝ 2 f y‖^2)) := by
  let F := iteratedFDeriv ℝ 2 f
  have hF : Continuous F := hf.continuous_iteratedFDeriv (by simp)
  let G := fun p : SpatialCoordinates d × ℝ => p.2*‖F (p.2 • p.1+(1-p.2) • x)‖
  have hG : Continuous G := by dsimp only [G]; fun_prop
  have hi : Integrable G ((volume.restrict K).prod (volume.restrict (Icc (0:ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact hG.continuousOn.integrableOn_compact (hK.prod isCompact_Icc)
  have hJ : Continuous (fun y => ∫ r in Icc (0:ℝ) 1, G (y,r)) :=
    continuous_parametric_integral_of_continuous hG isCompact_Icc
  have hTaylor : Continuous (fun y => f y+fderiv ℝ f y (x-y)) := by
    have hdf := hf.continuous_fderiv (by norm_num)
    fun_prop
  have heq : volume.real K*f x-(∫ y in K, f y+fderiv ℝ f y (x-y)) =
      ∫ y in K, f x-f y-fderiv ℝ f y (x-y) := by
    have he (y : SpatialCoordinates d) : f x-f y-fderiv ℝ f y (x-y)=
        f x-(f y+fderiv ℝ f y (x-y)) := by ring
    simp_rw [he]
    rw [integral_sub (integrableOn_const hK.measure_ne_top)
      (hTaylor.continuousOn.integrableOn_compact hK)]
    simp only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul]
  rw [heq,← Real.norm_eq_abs]
  calc
    _ ≤ ∫ y in K, ‖f x-f y-fderiv ℝ f y (x-y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y in K, D^2*(∫ r in Icc (0:ℝ) 1, G (y,r)) := by
      apply integral_mono_ae
      · apply ContinuousOn.integrableOn_compact hK
        have hdf := hf.continuous_fderiv (by norm_num)
        have hfc := hf.continuous
        fun_prop
      · exact (hJ.const_mul (D^2)).continuousOn.integrableOn_compact hK
      · filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
        exact smooth_taylor_remainder_norm_bound hf x y hD (by simpa only [dist_eq_norm] using hdiam y hy)
    _ = D^2*(∫ r in Ioc (0:ℝ) 1, r*(∫ y in K, ‖F (r • y+(1-r) • x)‖)) := by
      rw [integral_const_mul,integral_integral_swap hi,integral_Icc_eq_integral_Ioc]
      congr 1
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro r
      exact integral_const_mul r _
    _ ≤ D^2*(2*Real.sqrt (volume.real K*(∫ y in K, ‖F y‖^2))) :=
      mul_le_mul_of_nonneg_left (convex_segment_lowdim_integral_bound hK hc hd hF hx) (sq_nonneg D)
    _ = _ := by ring

end Carleman
