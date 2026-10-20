module

public import Carleman.Control.CartesianWeakLimitTests
public import Carleman.Continuous.L2Pairing
public import Carleman.Continuous.ClassicalWeakTime

/-! Actual Bochner tensor pairings, adjoints and transport of weak derivatives. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology BigOperators NNReal ContDiff
namespace Carleman

theorem timeTensor_eq_scalarTensor {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : ℝ) (v : H) (f : Lp ℝ 2 (volume.restrict (Ioc 0 T))) :
    timeTensor T v f=scalarTensor (volume.restrict (Ioc 0 T)) f v := by
  apply Lp.ext
  exact (timeTensor_ae T v f).trans (scalarTensor_ae _ f v).symm

theorem inner_timeTensor_integral {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (T : ℝ) (u : Lp H 2 (volume.restrict (Ioc 0 T)))
    (v : H) (f : Lp ℝ 2 (volume.restrict (Ioc 0 T))) :
    inner ℝ u (timeTensor T v f)=inner ℝ (∫ t, f t • u t ∂(volume.restrict (Ioc 0 T))) v := by
  rw [timeTensor_eq_scalarTensor,inner_scalarTensor_integral]

theorem compLpL_adjoint {α H G : Type*} [MeasurableSpace α] (μ : Measure α)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (L : H →L[ℝ] G) :
    (L.compLpL 2 μ).adjoint=L.adjoint.compLpL 2 μ := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_left,L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [L.coeFn_compLpL z,L.adjoint.coeFn_compLpL f] with t ht hf
  rw [ht,hf,ContinuousLinearMap.adjoint_inner_left]

theorem HasWeakTimeDerivative.map_integral
    {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {g : TimeGrid} {u du : ℝ → H} (hw : HasWeakTimeDerivative g u du)
    (hu : MemLp u 2 g.timeMeasure) (hdu : MemLp du 2 g.timeMeasure)
    (L : H →L[ℝ] F) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo 0 g.period) :
    (∫ t, deriv φ t • L (u t) ∂g.timeMeasure)=-(∫ t, φ t • L (du t) ∂g.timeMeasure) := by
  have hiu : Integrable (fun t => deriv φ t • u t) g.timeMeasure :=
    memLp_one_iff_integrable.mp ((g.memLp_of_continuousOn (hφ.continuous_deriv (by simp)).continuousOn).smul hu)
  have hid : Integrable (fun t => φ t • du t) g.timeMeasure :=
    memLp_one_iff_integrable.mp ((g.memLp_of_continuousOn hφ.continuous.continuousOn).smul hdu)
  simp_rw [← map_smul]
  rw [L.integral_comp_comm hiu,L.integral_comp_comm hid,hw φ hφ hc hs,map_neg]

end Carleman
