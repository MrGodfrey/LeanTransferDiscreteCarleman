module

public import Carleman.Control.BochnerProductL2
public import Carleman.Control.TimeCutoffPairing

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology
namespace Carleman
variable {α β V H : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {μ : Measure α} {ν : Measure β}

theorem bochnerL2ProductIsometry_cutoff [IsFiniteMeasure μ] [SFinite ν]
    (s : Set α) (hs : MeasurableSet s) (u : Lp (Lp ℝ 2 ν) 2 μ) :
    bochnerL2ProductIsometry ((BoundedMultiplier.cutoff s hs).map u)=
      (BoundedMultiplier.cutoff (Prod.fst ⁻¹' s) (hs.preimage measurable_fst)).map
        (bochnerL2ProductIsometry u) := by
  classical
  let W := BoundedMultiplier.cutoff (ν := μ) s hs
  let Q := BoundedMultiplier.cutoff (ν := μ.prod ν) (Prod.fst ⁻¹' s) (hs.preimage measurable_fst)
  let J := bochnerL2ProductIsometry (μ := μ) (ν := ν)
  change J (W.map u)=Q.map (J u)
  refine (simpleL2_bochnerLinear_dense (μ := μ) (ν := ν)).induction_on
    (p := fun v => J (W.map v)=Q.map (J v)) u
    (isClosed_eq (J.continuous.comp W.continuousLinearMap.continuous)
      (Q.continuousLinearMap.continuous.comp J.continuous)) ?_
  intro f
  let z := simpleL2_bochnerLinear (μ := μ) f
  let f' := SimpleFunc.piecewise s hs f (SimpleFunc.const α 0)
  have hz : W.map z=simpleL2_bochnerLinear (μ := μ) f' := by
    apply Lp.ext
    filter_upwards [W.map_ae z,(f.memLp_of_isFiniteMeasure 2 μ).coeFn_toLp,
      (f'.memLp_of_isFiniteMeasure 2 μ).coeFn_toLp] with t hw hf hf'
    change z t=f t at hf
    change simpleL2_bochnerLinear f' t=f' t at hf'
    rw [hw,hf,hf']
    by_cases ht : t∈s <;> simp [W,f',BoundedMultiplier.cutoff,SimpleFunc.piecewise_apply,ht]
  change J (W.map z)=Q.map (J z)
  rw [hz]
  apply Lp.ext
  filter_upwards [bochnerL2ProductIsometry_simple_ae (μ := μ) f',
    bochnerL2ProductIsometry_simple_ae (μ := μ) f,Q.map_ae (J z),
    quasiMeasurePreserving_snd.ae (Lp.coeFn_zero ℝ 2 ν)] with x h1 h2 h3 hzero
  change J (simpleL2_bochnerLinear f') x=_ at h1
  change J z x=_ at h2
  rw [h1,h3,h2]
  by_cases hx : x.1∈s
  · simp [Q,f',BoundedMultiplier.cutoff,SimpleFunc.piecewise_apply,hx]
  · simpa [Q,f',BoundedMultiplier.cutoff,SimpleFunc.piecewise_apply,hx] using hzero


end Carleman
