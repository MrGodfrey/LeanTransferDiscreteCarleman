module

public import Carleman.Continuous.RegularTimeCore
public import Mathlib.Analysis.Normed.Operator.Banach

/-! Harmonic trajectories depend continuously on both coefficients in the actual operator graph. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman.CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V) (g : TimeGrid) (n : ℤ)

def harmonicGraph (x y : b.operatorGraph) : b.PeriodicGraph g :=
  (b.harmonicTrajectory g n (b.graphDomain x) (b.graphDomain y)).toPeriodicGraph

theorem harmonicGraph_trace (x y : b.operatorGraph) (t : Icc 0 g.period) :
    (b.harmonicGraph g n x y).val.1 t=
      harmonicValue (g.angularFrequency n) (b.graphH x) (b.graphH y) t := rfl

def harmonicGraphLinear : (b.operatorGraph × b.operatorGraph) →ₗ[ℝ] b.PeriodicGraph g where
  toFun z := b.harmonicGraph g n z.1 z.2
  map_add' x y := by
    apply PeriodicGraph.trace_injective
    apply ContinuousMap.ext
    intro t
    change (b.harmonicGraph g n (x.1+y.1) (x.2+y.2)).val.1 t=
      (b.harmonicGraph g n x.1 x.2).val.1 t+(b.harmonicGraph g n y.1 y.2).val.1 t
    simp only [b.harmonicGraph_trace,map_add,harmonicValue,smul_add]
    module
  map_smul' c x := by
    apply PeriodicGraph.trace_injective
    apply ContinuousMap.ext
    intro t
    change (b.harmonicGraph g n (c • x.1) (c • x.2)).val.1 t=
      c • (b.harmonicGraph g n x.1 x.2).val.1 t
    simp only [b.harmonicGraph_trace,map_smul,harmonicValue,smul_add,smul_smul]
    module

theorem harmonicGraph_continuous : Continuous (b.harmonicGraphLinear g n) := by
  convert! LinearMap.continuous_of_seq_closed_graph (𝕜 := ℝ) (E := b.operatorGraph × b.operatorGraph)
    (F := b.PeriodicGraph g) (b.harmonicGraphLinear g n) ?_ using 1
  intro U x p hU hp
  apply PeriodicGraph.trace_injective
  apply ContinuousMap.ext
  intro t
  have heval : Continuous (fun q : b.PeriodicGraph g => q.val.1 t) := by fun_prop
  have hleft := (heval.tendsto p).comp hp
  have hparam : Continuous (fun z : b.operatorGraph × b.operatorGraph =>
      harmonicValue (g.angularFrequency n) (b.graphH z.1) (b.graphH z.2) t) := by
    unfold harmonicValue
    fun_prop
  have hright := (hparam.tendsto x).comp hU
  change Tendsto (fun k => (b.harmonicGraph g n (U k).1 (U k).2).val.1 t) atTop (𝓝 (p.val.1 t)) at hleft
  simp only [b.harmonicGraph_trace] at hleft
  exact tendsto_nhds_unique hleft hright

def harmonicGraphCLM : (b.operatorGraph × b.operatorGraph) →L[ℝ] b.PeriodicGraph g where
  toLinearMap := b.harmonicGraphLinear g n
  cont := b.harmonicGraph_continuous g n

end Carleman.CoerciveForm
