module

public import Carleman.Spatial.RealL2Integral
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The segment fundamental theorem and its genuine L² derivative bound.
These smooth statements will be applied to actual local mollifications. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem smooth_segment_ftc {f : SpatialCoordinates d → ℝ} (hf : ContDiff ℝ 1 f)
    (x z : SpatialCoordinates d) (t : ℝ) :
    f (x+t • z)-f x = ∫ s in (0:ℝ)..t, fderiv ℝ f (x+s • z) z := by
  have hd (s : ℝ) : HasDerivAt (fun r : ℝ => f (x+r • z))
      (fderiv ℝ f (x+s • z) z) s := by
    simpa only [zero_add,one_smul,Function.comp_def,Pi.add_apply,id_eq] using
      (hf.differentiable (by simp) (x+s • z)).hasFDerivAt.comp_hasDerivAt s
        ((hasDerivAt_const s x).add ((hasDerivAt_id s).smul_const z))
  have hc : Continuous (fun s : ℝ => fderiv ℝ f (x+s • z) z) :=
    ((hf.continuous_fderiv (by simp)).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  simpa only [zero_smul,add_zero] using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) (hc.intervalIntegrable 0 t)).symm

theorem smooth_segment_difference_sq {f : SpatialCoordinates d → ℝ} (hf : ContDiff ℝ 1 f)
    (x z : SpatialCoordinates d) {t : ℝ} (ht : 0 ≤ t) :
    (f (x+t • z)-f x)^2 ≤
      t*‖z‖^2*(∫ s in Ioc 0 t, ‖fderiv ℝ f (x+s • z)‖^2) := by
  let D := fun s : ℝ => fderiv ℝ f (x+s • z)
  have hD : Continuous D := (hf.continuous_fderiv (by simp)).comp
    (continuous_const.add (continuous_id.smul continuous_const))
  have hg : Continuous (fun s => D s z) := hD.clm_apply continuous_const
  have hm : MemLp (fun s => D s z) 2 (volume.restrict (Ioc 0 t)) := by
    apply (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr
    exact ((hg.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have he := integral_mul_sq_le (memLp_const (1:ℝ)) hm
  simp only [one_mul,one_pow,integral_const,smul_eq_mul,mul_one,
    measureReal_restrict_apply_univ,Real.volume_real_Ioc_of_le ht,sub_zero] at he
  have hb : (∫ s in Ioc 0 t, (D s z)^2) ≤
      ‖z‖^2*(∫ s in Ioc 0 t, ‖D s‖^2) := by
    rw [← integral_const_mul]
    apply integral_mono_ae hm.integrable_sq
      ((((hD.norm.pow 2).const_mul _).integrableOn_Icc).mono_set Ioc_subset_Icc_self)
    apply Filter.Eventually.of_forall
    intro s
    have hh := (sq_le_sq₀ (norm_nonneg (D s z)) (mul_nonneg (norm_nonneg (D s))
      (norm_nonneg z))).mpr ((D s).le_opNorm z)
    simpa only [Real.norm_eq_abs,sq_abs,mul_pow,mul_comm,Pi.pow_apply] using hh
  rw [smooth_segment_ftc hf x z t,intervalIntegral.integral_of_le ht]
  exact he.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb ht)

end Carleman
