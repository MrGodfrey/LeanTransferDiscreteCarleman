module

public import Carleman.Section3.Statements

/-! Original a.e.-domain weak solutions and the complete graph equations.
Representatives outside [0,T] are immaterial; no all-time D(A) premise is used. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.PeriodicWeakTrajectory
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {g : TimeGrid} {b : CoerciveForm H V}

/-- Exactly the original a.e. equation, for any weak representative. -/
theorem graph_equation_iff (u : PeriodicWeakTrajectory g b.domain b.operator)
    (s : Orientation) (μ : BoundedMultiplier g.timeMeasure) (f : Lp H 2 g.timeMeasure) :
    b.evolution g s μ u.toPeriodicGraph = f ↔
      ∀ᵐ t ∂g.timeMeasure, s.sign • u.derivative t + b.operator (u.domainValue t) +
        μ.value t • u.value t = f t := by
  rw [b.evolution_eq_iff]
  have he : ∀ᵐ t ∂g.timeMeasure,
      s.sign • u.toPeriodicGraph.toTrajectory.derivative t +
        b.operator (u.toPeriodicGraph.toTrajectory.domainValue t) +
        μ.value t • u.toPeriodicGraph.toTrajectory.value t =
      s.sign • u.derivative t + b.operator (u.domainValue t) + μ.value t • u.value t := by
    filter_upwards [u.toPeriodicGraph_derivative_ae,u.toPeriodicGraph_operator_ae,g.ae_mem_period] with t hd ha ht
    rw [hd,ha,u.toPeriodicGraph_value_on t (Ioo_subset_Icc_self ht)]
  constructor <;> intro h
  · filter_upwards [he,h] with t he ht
    rwa [← he]
  · filter_upwards [he,h] with t he ht
    rwa [he]
end Carleman.PeriodicWeakTrajectory
