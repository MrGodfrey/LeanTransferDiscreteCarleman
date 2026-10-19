module

public import Carleman.Continuous.HarmonicGraphContinuity

/-! The actual Bochner fields of each harmonic graph trajectory. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V) (g : TimeGrid) (n : ℤ)

theorem harmonicGraph_derivative_ae (x y : b.operatorGraph) :
    (b.harmonicGraph g n x y).val.2.1 =ᵐ[g.timeMeasure]
      harmonicDerivative (g.angularFrequency n) (b.graphH x) (b.graphH y) :=
  (b.harmonicTrajectory g n (b.graphDomain x) (b.graphDomain y)).derivative_L2.coeFn_toLp

theorem harmonicGraph_operator_ae (x y : b.operatorGraph) :
    (b.harmonicGraph g n x y).val.2.2 =ᵐ[g.timeMeasure]
      harmonicValue (g.angularFrequency n) (b.graphA x) (b.graphA y) := by
  have hh := (b.harmonicTrajectory g n (b.graphDomain x) (b.graphDomain y)).operator_L2.coeFn_toLp
  filter_upwards [hh] with t ht
  change (b.harmonicGraph g n x y).val.2.2 t = _ at ht ⊢
  rw [ht]
  change b.operator (domainRepresentative b.domain
    (harmonicValue (g.angularFrequency n) (b.graphDomain x : H) (b.graphDomain y : H)) t)=_
  rw [b.harmonicDomain_representative (g.angularFrequency n) (b.graphDomain x) (b.graphDomain y) t,
    b.harmonicDomain_operator,b.graphDomain_operator,b.graphDomain_operator]

end Carleman.CoerciveForm
