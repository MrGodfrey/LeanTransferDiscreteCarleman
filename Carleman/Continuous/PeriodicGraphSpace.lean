module

public import Carleman.Continuous.FormTimeGraph
public import Carleman.Continuous.WeakTimeSpace

/-! A complete space of genuine periodic H¹ trajectories with Au in L².
Only the H representative has continuous traces; D(A) membership is a.e. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

namespace TimeGrid
variable (g : TimeGrid)
abbrev PeriodicFields := g.TracePath (H := H) × (Lp H 2 g.timeMeasure × Lp H 2 g.timeMeasure)

def fieldsValue : g.PeriodicFields (H := H) →L[ℝ] Lp H 2 g.timeMeasure :=
  g.pathL2.comp (ContinuousLinearMap.fst ℝ _ _)

def fieldsDerivative : g.PeriodicFields (H := H) →L[ℝ] Lp H 2 g.timeMeasure :=
  (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)

def fieldsOperator : g.PeriodicFields (H := H) →L[ℝ] Lp H 2 g.timeMeasure :=
  (ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)

def fieldsTraceDefect : g.PeriodicFields (H := H) →L[ℝ] H :=
  ((ContinuousMap.evalCLM ℝ (M := H) (⟨0, by simp [g.period_pos.le]⟩ : Icc 0 g.period)) -
    ContinuousMap.evalCLM ℝ (M := H)
      (⟨g.period, by simp [g.period_pos.le]⟩ : Icc 0 g.period)).comp
      (ContinuousLinearMap.fst ℝ _ _)
end TimeGrid

namespace CoerciveForm
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V) (g : TimeGrid)

def periodicGraphSubmodule : Submodule ℝ (g.PeriodicFields (H := H)) :=
  (weakTimeSubmodule g).comap (g.fieldsValue.prod g.fieldsDerivative).toLinearMap ⊓
    ((b.timeOperatorGraph g.timeMeasure).comap
      (g.fieldsValue.prod g.fieldsOperator).toLinearMap ⊓ g.fieldsTraceDefect.ker)

abbrev PeriodicGraph : Type _ := b.periodicGraphSubmodule g

theorem periodicGraph_mem (p : g.PeriodicFields (H := H)) :
    p ∈ b.periodicGraphSubmodule g ↔
      IsWeakTimeClass g (g.pathL2 p.1) p.2.1 ∧
      (g.pathL2 p.1,p.2.2) ∈ b.timeOperatorGraph g.timeMeasure ∧
      p.1 ⟨0, by simp [g.period_pos.le]⟩ = p.1 ⟨g.period, by simp [g.period_pos.le]⟩ := by
  simp only [periodicGraphSubmodule, Submodule.mem_inf, Submodule.mem_comap,
    LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  change (IsWeakTimeClass g (g.pathL2 p.1) p.2.1 ∧
    (g.pathL2 p.1,p.2.2) ∈ b.timeOperatorGraph g.timeMeasure ∧
    p.1 ⟨0, by simp [g.period_pos.le]⟩ - p.1 ⟨g.period, by simp [g.period_pos.le]⟩ = 0) ↔ _
  rw [sub_eq_zero]

theorem periodicGraph_isClosed :
    IsClosed (b.periodicGraphSubmodule g : Set (g.PeriodicFields (H := H))) :=
  ((weakTimeSubmodule_isClosed g).preimage (g.fieldsValue.prod g.fieldsDerivative).continuous).inter
    (((b.timeOperatorGraph_isClosed g.timeMeasure).preimage
      (g.fieldsValue.prod g.fieldsOperator).continuous).inter g.fieldsTraceDefect.isClosed_ker)

instance periodicGraph_completeSpace [CompleteSpace H] : CompleteSpace (b.PeriodicGraph g) := by
  let : IsClosed (b.periodicGraphSubmodule g : Set (g.PeriodicFields (H := H))) :=
    b.periodicGraph_isClosed g
  exact IsClosed.completeSpace_coe

namespace PeriodicGraph
variable [CompleteSpace H] {b : CoerciveForm H V} {g : TimeGrid}

def toTrajectory (p : b.PeriodicGraph g) : PeriodicWeakTrajectory g b.domain b.operator where
  value := g.clampPath p.val.1
  derivative := p.val.2.1
  continuous := (g.clampPath p.val.1).continuous.continuousOn
  periodic_trace := by
    rw [g.clampPath_on _ 0 (by simp [g.period_pos.le]),
      g.clampPath_on _ g.period (by simp [g.period_pos.le])]
    exact ((b.periodicGraph_mem g p.val).mp p.property).2.2
  value_L2 := g.pathL2_memLp p.val.1
  derivative_L2 := Lp.memLp p.val.2.1
  domain_ae := (b.timeOperatorGraph_representative g.timeMeasure
    ((b.periodicGraph_mem g p.val).mp p.property).2.1 _ (g.pathL2_ae p.val.1)).1
  operator_L2 := (Lp.memLp p.val.2.2).ae_eq
    (b.timeOperatorGraph_representative g.timeMeasure
      ((b.periodicGraph_mem g p.val).mp p.property).2.1 _ (g.pathL2_ae p.val.1)).2.symm
  weak_derivative :=
    (IsWeakTimeClass.iff_weakDerivative.mp
      ((b.periodicGraph_mem g p.val).mp p.property).1).congr (g.pathL2_ae p.val.1)

theorem toTrajectory_operator_ae (p : b.PeriodicGraph g) :
    (fun t => b.operator (p.toTrajectory.domainValue t)) =ᵐ[g.timeMeasure] p.val.2.2 :=
  (b.timeOperatorGraph_representative g.timeMeasure
    ((b.periodicGraph_mem g p.val).mp p.property).2.1 _ (g.pathL2_ae p.val.1)).2
end PeriodicGraph
end CoerciveForm
end Carleman
