module

public import Carleman.Geometry.InwardConeTube
public import Carleman.Spatial.DomainConvolution
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Fundamental theorem of calculus along genuine inward-cone segments for
the mollifications of a domain weak derivative pair. The domain margin is
proved geometrically and supplies every admissible reflected kernel test. -/
@[expose] public noncomputable section
open MeasureTheory Set Metric
open scoped Convolution ContDiff
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem mollified_cone_ftc (p : InwardConePatch S) {x z : SpatialCoordinates d} {ε t : ℝ}
    (hx : closedBall x ε ⊆ p.region ∩ S) (hz : ‖z-p.direction‖ ≤ 1)
    (ht : 0 ≤ t) (hheight : t ≤ p.height)
    {u v : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))}
    (hweak : IsWeakSpatialDerivative volume S z u v)
    (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hκ : tsupport κ.value ⊆ closedBall 0 ε) :
    (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) (x+t • z) -
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) x =
      ∫ s in (0 : ℝ)..t, (v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) (x+s • z) := by
  let U := u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value
  let V := v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value
  have hlocal (s : ℝ) (hs : s ∈ Icc 0 t) : fderiv ℝ U (x+s • z) z = V (x+s • z) := by
    apply hweak.fderiv_convolution_local κ
    intro y hy
    apply p.tube_subset hx hz hs.1 (hs.2.trans hheight)
    rw [mem_closedBall,dist_eq_norm]
    rw [show x+s • z-y-(x+s • z) = -y by abel,norm_neg]
    simpa only [mem_closedBall,dist_zero_right] using hκ hy
  have hd : ∀ s ∈ uIcc (0 : ℝ) t, HasDerivAt (fun r : ℝ => U (x+r • z))
      (V (x+s • z)) s := by
    intro s hs
    rw [uIcc_of_le ht] at hs
    rw [← hlocal s hs]
    simpa only [zero_add,one_smul,Function.comp_def,Pi.add_apply,id_eq,U] using
      ((κ.smooth_convolution u).differentiable (by simp) (x+s • z)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_const s x).add ((hasDerivAt_id s).smul_const z))
  have hcont : Continuous (fun s : ℝ => V (x+s • z)) :=
    (κ.smooth_convolution v).continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable 0 t)
  simpa only [zero_smul,add_zero] using he.symm
end Carleman
