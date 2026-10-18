module

public import Carleman.Spatial.MollifiedConeTranslation
public import Carleman.Continuous.BochnerNormAlgebra

/-! A local interpolation estimate for an actual second weak directional
chain. Only inward segments are used, with no boundary trace assumption. -/
@[expose] public noncomputable section
open MeasureTheory Set Metric
open scoped Convolution ContDiff
namespace Carleman
variable {d : ℕ} {S A : Set (SpatialCoordinates d)}

theorem mollified_cone_interpolation (p : InwardConePatch S) (hA : MeasurableSet A)
    {z : SpatialCoordinates d} {ε t : ℝ}
    (hmargin : ∀ x ∈ A, closedBall x ε ⊆ p.region ∩ S)
    (hz : ‖z-p.direction‖ ≤ 1) (ht : 0 < t) (hheight : t ≤ p.height)
    {u v w : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))}
    (huv : IsWeakSpatialDerivative volume S z u v)
    (hvw : IsWeakSpatialDerivative volume S z v w)
    (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hκ : tsupport κ.value ⊆ closedBall 0 ε)
    (hκpos : ∀ y, 0 ≤ κ.value y) (hunit : ∫ y, κ.value y = 1) :
    bochnerL2Norm (volume.restrict A)
      (v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) ≤ 2/t*‖u‖+t*‖w‖ := by
  let U := u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value
  let V := v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value
  let c := fun s : ℝ => max 0 (min s t)
  let νt : Measure ℝ := volume.restrict (Ioc 0 t)
  let f := fun q : SpatialCoordinates d × ℝ => V (q.1+c q.2 • z)-V q.1
  have hc0 (s : ℝ) : 0 ≤ c s := le_max_left _ _
  have hct (s : ℝ) : c s ≤ t := max_le ht.le (min_le_right _ _)
  have hf : AEStronglyMeasurable f ((volume.restrict A).prod νt) := by
    apply Continuous.aestronglyMeasurable
    exact (((κ.smooth_convolution v).continuous.comp (continuous_fst.add
      ((continuous_const.max (continuous_snd.min continuous_const)).smul continuous_const))).sub
      ((κ.smooth_convolution v).continuous.comp continuous_fst))
  have hs (s : ℝ) := mollified_cone_translation_l2 p hA hmargin hz (hc0 s)
    ((hct s).trans hheight) hvw κ hκ hκpos hunit
  have hb (s : ℝ) : bochnerL2Norm (volume.restrict A) (fun x => f (x,s)) ≤ t*‖w‖ :=
    (hs s).2.trans (mul_le_mul_of_nonneg_right (hct s) (norm_nonneg _))
  have havg := l2_average_le_of_slice_bound hf (fun s => (hs s).1) (mul_nonneg ht.le (norm_nonneg w)) hb
  have hνt : νt.real univ = t := by
    simp only [νt,measureReal_restrict_apply_univ,Real.volume_real_Ioc_of_le ht.le,sub_zero]
  have heq : (fun x => ∫ s, f (x,s) ∂νt) =ᵐ[volume.restrict A]
      (fun x => U (x+t • z)-U x-t*V x) := by
    filter_upwards [ae_restrict_mem hA] with x hx
    have hftc := mollified_cone_ftc p (hmargin x hx) hz ht.le hheight huv κ hκ
    rw [intervalIntegral.integral_of_le ht.le] at hftc
    calc
      _ = ∫ s, (V (x+s • z)-V x) ∂νt := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        have hc' : c s = s := by simp only [c,min_eq_left hs.2,max_eq_right hs.1.le]
        simp only [f,hc']
      _ = U (x+t • z)-U x-t*V x := by
        rw [integral_sub]
        · rw [← hftc,integral_const]
          simp only [smul_eq_mul,hνt]
          rfl
        · exact ((κ.smooth_convolution v).continuous.comp
            (continuous_const.add (continuous_id.smul continuous_const))).integrableOn_Icc.mono_set Ioc_subset_Icc_self
        · exact integrable_const _
  have hu : MemLp U 2 volume ∧ bochnerL2Norm volume U ≤ ‖u‖ :=
    κ.convolution_right_memLp_norm_le hκpos hunit u
  have huShift : MemLp (fun x => U (x+t • z)) 2 volume :=
    hu.1.comp_measurePreserving (measurePreserving_add_right volume (t • z))
  have hshift : bochnerL2Norm volume (fun x => U (x+t • z)) = bochnerL2Norm volume U := by
    exact congrArg ENNReal.toReal (eLpNorm_comp_measurePreserving hu.1.aestronglyMeasurable
      (measurePreserving_add_right volume _))
  have hdu := bochnerL2Norm_sub (huShift.restrict A) (hu.1.restrict A)
  have hdub : bochnerL2Norm (volume.restrict A) (fun x => U (x+t • z)-U x) ≤ 2*‖u‖ := by
    have ha := (bochnerL2Norm_restrict_le huShift A).trans_eq hshift
    have hb' := bochnerL2Norm_restrict_le hu.1 A
    linarith [hu.2]
  have hrest := havg.2
  rw [hνt,bochnerL2Norm_congr_ae heq] at hrest
  have hmrest := (memLp_congr_ae heq).mp havg.1
  have he := bochnerL2Norm_sub ((huShift.restrict A).sub (hu.1.restrict A)) hmrest
  change bochnerL2Norm (volume.restrict A)
    (fun x => (U (x+t • z)-U x)-(U (x+t • z)-U x-t*V x)) ≤
    bochnerL2Norm (volume.restrict A) (fun x => U (x+t • z)-U x)+
      bochnerL2Norm (volume.restrict A) (fun x => U (x+t • z)-U x-t*V x) at he
  have halg : (fun x => (U (x+t • z)-U x)-(U (x+t • z)-U x-t*V x)) = t • V := by
    funext x
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  rw [halg,bochnerL2Norm_const_smul,abs_of_pos ht] at he
  change bochnerL2Norm (volume.restrict A) V ≤ _
  have htotal : t*bochnerL2Norm (volume.restrict A) V ≤ (2/t*‖u‖+t*‖w‖)*t := by
    calc
      _ ≤ 2*‖u‖+t*(t*‖w‖) := he.trans (add_le_add hdub hrest)
      _ = (2/t*‖u‖+t*‖w‖)*t := by field_simp
  nlinarith
end Carleman
