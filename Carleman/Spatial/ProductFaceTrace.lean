module

public import Carleman.Spatial.ProductWeakSlices

/-! Face traces as genuine L² classes, with actual endpoint values of the
weak slice representatives and the sharp scaling powers in the interval length. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

def fiberEndpointLp (g : TimeGrid) (c : Icc (0 : ℝ) g.period)
    (f v : Lp ℝ 2 (μ.prod g.timeMeasure)) : Lp ℝ 2 μ :=
  (fiberEndpointIntegral_memLp_bound g c.property (Lp.memLp f) (Lp.memLp v)).1.toLp
    (fiberEndpointIntegral g c f v)

theorem fiberEndpointLp_ae (g : TimeGrid) (c : Icc (0 : ℝ) g.period)
    (f v : Lp ℝ 2 (μ.prod g.timeMeasure)) :
    fiberEndpointLp g c f v =ᵐ[μ] fiberEndpointIntegral g c f v := MemLp.coeFn_toLp _

theorem fiberEndpointLp_norm_sq (g : TimeGrid) (c : Icc (0 : ℝ) g.period)
    (f v : Lp ℝ 2 (μ.prod g.timeMeasure)) :
    ‖fiberEndpointLp g c f v‖^2 ≤ 2/g.period*‖f‖^2+2*g.period*‖v‖^2 := by
  have he := (fiberEndpointIntegral_memLp_bound g c.property (Lp.memLp f) (Lp.memLp v)).2
  have hf : bochnerL2Norm (μ.prod g.timeMeasure) (f : X × ℝ → ℝ)=‖f‖ := by
    rw [bochnerL2Norm_eq _ (Lp.memLp f),Lp.toLp_coeFn]
  have hv : bochnerL2Norm (μ.prod g.timeMeasure) (v : X × ℝ → ℝ)=‖v‖ := by
    rw [bochnerL2Norm_eq _ (Lp.memLp v),Lp.toLp_coeFn]
  rw [hf,hv,bochnerL2Norm_eq _
    (fiberEndpointIntegral_memLp_bound g c.property (Lp.memLp f) (Lp.memLp v)).1] at he
  exact he

variable {d : ℕ} {S : Set (SpatialCoordinates d)}

omit [MeasurableSpace X] [SFinite μ] in
theorem product_weak_face_trace_representatives [IsFiniteMeasure (volume.restrict S)]
    (hS : IsOpen S) (g : TimeGrid)
    (f v : Lp ℝ 2 ((volume.restrict S).prod g.timeMeasure))
    (hw : IsWeakSpatialDerivative ((volume.restrict S).prod g.timeMeasure)
      (S ×ˢ Ioo 0 g.period) (0,1) f v) :
    ∀ᵐ x ∂volume.restrict S, ∃ U : ℝ → ℝ, ContinuousOn U (Icc 0 g.period) ∧
      ((fun t => f (x,t)) =ᵐ[g.timeMeasure] U) ∧
      HasWeakTimeDerivative g U (fun t => v (x,t)) ∧
      fiberEndpointLp g ⟨g.period,g.period_pos.le,le_rfl⟩ f v x=U 0 ∧
        fiberEndpointLp g ⟨0,le_rfl,g.period_pos.le⟩ f v x=U g.period := by
  filter_upwards [product_weak_endpoint_representatives hS g f v hw,
    fiberEndpointLp_ae g ⟨g.period,g.period_pos.le,le_rfl⟩ f v,
    fiberEndpointLp_ae g ⟨0,le_rfl,g.period_pos.le⟩ f v] with x hx hzero hend
  obtain ⟨U,hc,ha,hwU,h0,hT⟩ := hx
  exact ⟨U,hc,ha,hwU,hzero.trans h0,hend.trans hT⟩

end Carleman
