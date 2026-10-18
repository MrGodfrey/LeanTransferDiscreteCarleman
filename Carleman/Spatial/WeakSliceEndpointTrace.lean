module

public import Carleman.Spatial.FiberEndpointIntegral

/-! The product endpoint integrals are actual endpoint values of continuous
representatives for almost every genuine weak H¹ slice. Passing from the
full spatial weak-test relation to these slice identities remains explicit. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

omit [MeasurableSpace X] [SFinite μ] in
theorem fiberEndpointIntegral_eq_weak_trace (g : TimeGrid) (f v : X × ℝ → ℝ) (x : X)
    (z : weakTimeSubmodule (H := ℝ) g)
    (hf : z.val.1 =ᵐ[g.timeMeasure] (fun t => f (x,t)))
    (hv : z.val.2 =ᵐ[g.timeMeasure] (fun t => v (x,t))) :
    fiberEndpointIntegral g g.period f v x=g.weakIntervalTrace ⟨0,le_rfl,g.period_pos.le⟩ z ∧
      fiberEndpointIntegral g 0 f v x=g.weakIntervalTrace ⟨g.period,g.period_pos.le,le_rfl⟩ z := by
  have he (c : ℝ) : (∫ t, (z.val.1 t+(t-c)*z.val.2 t) ∂g.timeMeasure)=
      ∫ t, (f (x,t)+(t-c)*v (x,t)) ∂g.timeMeasure := by
    apply integral_congr_ae
    filter_upwards [hf,hv] with t ht hdt
    rw [ht,hdt]
  constructor
  · rw [g.weakIntervalTrace_zero_formula,he]
    exact mul_comm _ _
  · rw [g.weakIntervalTrace_end_formula]
    have hz := he 0
    simp only [sub_zero] at hz
    rw [hz]
    simp only [fiberEndpointIntegral,sub_zero,div_eq_mul_inv,mul_comm]

theorem weak_slices_actual_endpoint_traces (g : TimeGrid) {f v : X × ℝ → ℝ}
    (hf : MemLp f 2 (μ.prod g.timeMeasure)) (hv : MemLp v 2 (μ.prod g.timeMeasure))
    (hw : ∀ᵐ x ∂μ, HasWeakTimeDerivative g (fun t => f (x,t)) (fun t => v (x,t))) :
    ∀ᵐ x ∂μ, ∃ U : ℝ → ℝ, ContinuousOn U (Icc 0 g.period) ∧
      ((fun t => f (x,t)) =ᵐ[g.timeMeasure] U) ∧
      HasWeakTimeDerivative g U (fun t => v (x,t)) ∧
      fiberEndpointIntegral g g.period f v x=U 0 ∧ fiberEndpointIntegral g 0 f v x=U g.period := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_left,hv.aestronglyMeasurable.prodMk_left,
    hf.integrable_sq.prod_right_ae,hv.integrable_sq.prod_right_ae,hw] with x hfm hvm hf2 hv2 hwx
  have hfx : MemLp (fun t => f (x,t)) 2 g.timeMeasure :=
    (memLp_two_iff_integrable_sq hfm).mpr hf2
  have hvx : MemLp (fun t => v (x,t)) 2 g.timeMeasure :=
    (memLp_two_iff_integrable_sq hvm).mpr hv2
  let z : weakTimeSubmodule (H := ℝ) g :=
    ⟨(hfx.toLp (fun t => f (x,t)),hvx.toLp (fun t => v (x,t))),
      IsWeakTimeClass.iff_weakDerivative.mpr
        ((hwx.congr_value hfx.coeFn_toLp.symm).congr_derivative hvx.coeFn_toLp.symm)⟩
  have hzf : z.val.1 =ᵐ[g.timeMeasure] (fun t => f (x,t)) := hfx.coeFn_toLp
  have hzv : z.val.2 =ᵐ[g.timeMeasure] (fun t => v (x,t)) := hvx.coeFn_toLp
  have he := fiberEndpointIntegral_eq_weak_trace g f v x z hzf hzv
  refine ⟨g.clampPath (g.weakTracePath z),(g.clampPath (g.weakTracePath z)).continuous.continuousOn,
    hzf.symm.trans (g.weakTracePath_ae z),(g.weakTracePath_weak z).congr_derivative hzv,?_,?_⟩
  · rw [g.clampPath_on _ 0 ⟨le_rfl,g.period_pos.le⟩]
    exact he.1
  · rw [g.clampPath_on _ g.period ⟨g.period_pos.le,le_rfl⟩]
    exact he.2

end Carleman
