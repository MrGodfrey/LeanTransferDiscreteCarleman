module

public import Carleman.Spatial.ProductWeakMarginal
public import Carleman.Spatial.WeakSliceEndpointTrace

/-! The full product-domain spatial weak identity implies genuine weak
interval identities for almost every slice, simultaneously for every test.
Consequently the endpoint integrals are actual L² face traces. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman

def intervalSliceLp {X : Type*} (g : TimeGrid) (f : X × ℝ → ℝ) (x : X) : Lp ℝ 2 g.timeMeasure := by
  classical
  exact if h : MemLp (fun t => f (x,t)) 2 g.timeMeasure then h.toLp (fun t => f (x,t)) else 0

theorem intervalSliceLp_ae {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    (g : TimeGrid) {f : X × ℝ → ℝ} (hf : MemLp f 2 (μ.prod g.timeMeasure)) :
    ∀ᵐ x ∂μ, intervalSliceLp g f x =ᵐ[g.timeMeasure] (fun t => f (x,t)) := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_left,hf.integrable_sq.prod_right_ae] with x hx hi
  have hm := (memLp_two_iff_integrable_sq hx).mpr hi
  rw [intervalSliceLp,dite_eq_left hm]
  exact hm.coeFn_toLp

theorem scalar_interval_test_pairing (g : TimeGrid) (u : Lp ℝ 2 g.timeMeasure)
    (ψ : SpatialTest (Ioo 0 g.period)) :
    inner ℝ u (ψ.derivativeLp g.timeMeasure 1)=(∫ t, deriv ψ.value t*u t ∂g.timeMeasure) ∧
      inner ℝ u (ψ.toLp g.timeMeasure)=(∫ t, ψ.value t*u t ∂g.timeMeasure) := by
  constructor
  · rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ψ.derivativeLp_ae g.timeMeasure 1] with t ht
    simp only [ht,RCLike.inner_apply,conj_trivial]
    rfl
  · rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ψ.toLp_ae g.timeMeasure] with t ht
    simp only [ht,RCLike.inner_apply,conj_trivial]

variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem product_weak_slices [IsFiniteMeasure (volume.restrict S)]
    (hS : IsOpen S) (g : TimeGrid)
    (f v : Lp ℝ 2 ((volume.restrict S).prod g.timeMeasure))
    (hw : IsWeakSpatialDerivative ((volume.restrict S).prod g.timeMeasure)
      (S ×ˢ Ioo 0 g.period) (0,1) f v) :
    ∀ᵐ x ∂volume.restrict S,
      HasWeakTimeDerivative g (fun t => f (x,t)) (fun t => v (x,t)) := by
  have hf := intervalSliceLp_ae g (Lp.memLp f)
  have hv := intervalSliceLp_ae g (Lp.memLp v)
  have he := ae_weak_interval_of_ae_tests g (intervalSliceLp g f) (intervalSliceLp g v) (by
    intro ψ
    filter_upwards [hf,hv,product_weak_marginal hS g f v hw ψ] with x hx hy hm
    rw [(scalar_interval_test_pairing g (intervalSliceLp g f x) ψ).1,
      (scalar_interval_test_pairing g (intervalSliceLp g v x) ψ).2]
    have hA : (∫ t, deriv ψ.value t*intervalSliceLp g f x t ∂g.timeMeasure)=
        ∫ t, deriv ψ.value t*f (x,t) ∂g.timeMeasure := by
      apply integral_congr_ae
      filter_upwards [hx] with t ht
      rw [ht]
    have hB : (∫ t, ψ.value t*intervalSliceLp g v x t ∂g.timeMeasure)=
        ∫ t, ψ.value t*v (x,t) ∂g.timeMeasure := by
      apply integral_congr_ae
      filter_upwards [hy] with t ht
      rw [ht]
    rw [hA,hB]
    exact hm)
  filter_upwards [hf,hv,he] with x hx hy hwx
  exact (hwx.congr_value hx).congr_derivative hy

theorem product_weak_endpoint_representatives [IsFiniteMeasure (volume.restrict S)]
    (hS : IsOpen S) (g : TimeGrid)
    (f v : Lp ℝ 2 ((volume.restrict S).prod g.timeMeasure))
    (hw : IsWeakSpatialDerivative ((volume.restrict S).prod g.timeMeasure)
      (S ×ˢ Ioo 0 g.period) (0,1) f v) :
    ∀ᵐ x ∂volume.restrict S, ∃ U : ℝ → ℝ, ContinuousOn U (Icc 0 g.period) ∧
      ((fun t => f (x,t)) =ᵐ[g.timeMeasure] U) ∧
      HasWeakTimeDerivative g U (fun t => v (x,t)) ∧
      fiberEndpointIntegral g g.period f v x=U 0 ∧ fiberEndpointIntegral g 0 f v x=U g.period :=
  weak_slices_actual_endpoint_traces g (Lp.memLp f) (Lp.memLp v) (product_weak_slices hS g f v hw)

end Carleman
