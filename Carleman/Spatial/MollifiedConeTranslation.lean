module

public import Carleman.Spatial.MollifiedConeFTC
public import Carleman.Spatial.MollifiedInterpolation
public import Carleman.Spatial.L2Averaging

/-! An actual L² translation estimate for the smooth local convolutions.
Its constant is the original weak directional derivative norm, independent
of the mollifier radius, the interior subset, and the time grid. -/
@[expose] public noncomputable section
open MeasureTheory Set Metric
open scoped Convolution ContDiff
namespace Carleman
variable {d : ℕ} {S A : Set (SpatialCoordinates d)}

theorem mollified_cone_translation_l2 (p : InwardConePatch S) (hA : MeasurableSet A)
    {z : SpatialCoordinates d} {ε t : ℝ}
    (hmargin : ∀ x ∈ A, closedBall x ε ⊆ p.region ∩ S)
    (hz : ‖z-p.direction‖ ≤ 1) (ht : 0 ≤ t) (hheight : t ≤ p.height)
    {u v : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))}
    (hweak : IsWeakSpatialDerivative volume S z u v)
    (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hκ : tsupport κ.value ⊆ closedBall 0 ε)
    (hκpos : ∀ y, 0 ≤ κ.value y) (hunit : ∫ y, κ.value y = 1) :
    let U := u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value
    MemLp (fun x => U (x+t • z)-U x) 2 (volume.restrict A) ∧
      bochnerL2Norm (volume.restrict A) (fun x => U (x+t • z)-U x) ≤ t*‖v‖ := by
  intro U
  let V := v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value
  let f := fun q : SpatialCoordinates d × ℝ => V (q.1+q.2 • z)
  let νt : Measure ℝ := volume.restrict (Ioc 0 t)
  have hv := κ.convolution_right_memLp_norm_le hκpos hunit v
  have hs (s : ℝ) : MemLp (fun x => V (x+s • z)) 2 volume :=
    hv.1.comp_measurePreserving (measurePreserving_add_right volume _)
  have hnorm (s : ℝ) : bochnerL2Norm volume (fun x => V (x+s • z)) = bochnerL2Norm volume V := by
    unfold bochnerL2Norm
    exact congrArg ENNReal.toReal (eLpNorm_comp_measurePreserving hv.1.aestronglyMeasurable
      (measurePreserving_add_right volume _))
  have hf : AEStronglyMeasurable f ((volume.restrict A).prod νt) :=
    ((κ.smooth_convolution v).continuous.comp
      (continuous_fst.add (continuous_snd.smul continuous_const))).aestronglyMeasurable
  have hb (s : ℝ) : bochnerL2Norm (volume.restrict A) (fun x => f (x,s)) ≤ ‖v‖ := by
    exact ((bochnerL2Norm_restrict_le (hs s) A).trans_eq (hnorm s)).trans hv.2
  have havg := l2_average_le_of_slice_bound hf (fun s => (hs s).restrict A) (norm_nonneg v) hb
  have hm : MemLp (fun x => ∫ s, f (x,s) ∂νt) 2 (volume.restrict A) := havg.1
  have he := havg.2
  have heq : (fun x => U (x+t • z)-U x) =ᵐ[volume.restrict A] (fun x => ∫ s, f (x,s) ∂νt) := by
    filter_upwards [ae_restrict_mem hA] with x hx
    have he := mollified_cone_ftc p (hmargin x hx) hz ht hheight hweak κ hκ
    rw [intervalIntegral.integral_of_le ht] at he
    exact he
  refine ⟨(memLp_congr_ae heq).mpr hm,?_⟩
  have hνt : νt.real univ = t := by
    simp only [νt,measureReal_restrict_apply_univ,Real.volume_real_Ioc_of_le ht,sub_zero]
  rw [hνt] at he
  change (eLpNorm _ 2 _).toReal ≤ _
  rw [eLpNorm_congr_ae heq]
  exact he
end Carleman
