module

public import Carleman.Continuous.PeriodicGraphSpace

/-! Every original B1 weak trajectory belongs to the complete periodic graph
space. The conversion preserves the entire closed-period trace and the actual
weak derivative and operator in L²; it adds no timewise D(A) hypothesis. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {g : TimeGrid} {b : CoerciveForm H V}

namespace PeriodicWeakTrajectory
variable (u : PeriodicWeakTrajectory g b.domain b.operator)

def tracePath : g.TracePath (H := H) :=
  ⟨(Icc 0 g.period).domRestrict u.value, continuousOn_iff_continuous_domRestrict.mp u.continuous⟩

theorem tracePath_on (t : ℝ) (ht : t ∈ Icc 0 g.period) :
    g.clampPath u.tracePath t = u.value t := g.clampPath_on u.tracePath t ht

theorem tracePath_ae : (g.clampPath u.tracePath : ℝ → H) =ᵐ[g.timeMeasure] u.value := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact u.tracePath_on t ⟨ht.1.le, ht.2.le⟩

theorem tracePathL2_ae : g.pathL2 u.tracePath =ᵐ[g.timeMeasure] u.value :=
  (g.pathL2_ae u.tracePath).trans u.tracePath_ae

variable [CompleteSpace V]

def toPeriodicGraph : b.PeriodicGraph g :=
  ⟨(u.tracePath, u.derivative_L2.toLp u.derivative,
      u.operator_L2.toLp (fun t => b.operator (u.domainValue t))), by
    apply (b.periodicGraph_mem g _).mpr
    refine ⟨?_, ?_, u.periodic_trace⟩
    · apply IsWeakTimeClass.iff_weakDerivative.mpr
      exact (u.weak_derivative.congr u.tracePathL2_ae.symm).congr_derivative
        u.derivative_L2.coeFn_toLp.symm
    · apply (b.timeOperatorGraph_ae g.timeMeasure _ _).mpr
      filter_upwards [u.domainValue_ae, u.tracePathL2_ae, u.operator_L2.coeFn_toLp]
        with t ht hv ha
      apply (b.operatorGraph_mem _ _).mpr
      exact ⟨u.domainValue t, ht.trans hv.symm, ha.symm⟩⟩

theorem toPeriodicGraph_value_on (t : ℝ) (ht : t ∈ Icc 0 g.period) :
    u.toPeriodicGraph.toTrajectory.value t = u.value t := u.tracePath_on t ht

theorem toPeriodicGraph_derivative_ae :
    u.toPeriodicGraph.toTrajectory.derivative =ᵐ[g.timeMeasure] u.derivative :=
  u.derivative_L2.coeFn_toLp

theorem toPeriodicGraph_operator_ae :
    (fun t => b.operator (u.toPeriodicGraph.toTrajectory.domainValue t)) =ᵐ[g.timeMeasure]
      (fun t => b.operator (u.domainValue t)) :=
  u.toPeriodicGraph.toTrajectory_operator_ae.trans u.operator_L2.coeFn_toLp
end PeriodicWeakTrajectory

namespace CoerciveForm.PeriodicGraph
variable [CompleteSpace V]

theorem trace_injective : Function.Injective
    (fun p : b.PeriodicGraph g => p.val.1) := by
  intro p q he
  change p.val.1 = q.val.1 at he
  have hp := (b.periodicGraph_mem g p.val).mp p.property
  have hq := (b.periodicGraph_mem g q.val).mp q.property
  have hd : p.val.2.1 = q.val.2.1 := by
    rw [← he] at hq
    exact hp.1.unique hq.1
  have ha : p.val.2.2 = q.val.2.2 := by
    apply Lp.ext
    have hpA := b.timeOperatorGraph_representative g.timeMeasure hp.2.1 _ (g.pathL2_ae p.val.1)
    have hqA := b.timeOperatorGraph_representative g.timeMeasure hq.2.1 _ (g.pathL2_ae q.val.1)
    rw [← he] at hqA
    exact hpA.2.symm.trans hqA.2
  apply Subtype.ext
  exact Prod.ext he (Prod.ext hd ha)

theorem toTrajectory_toPeriodicGraph (p : b.PeriodicGraph g) :
    p.toTrajectory.toPeriodicGraph = p := by
  apply trace_injective
  apply ContinuousMap.ext
  intro t
  exact g.clampPath_on p.val.1 t t.property
end CoerciveForm.PeriodicGraph
end Carleman
