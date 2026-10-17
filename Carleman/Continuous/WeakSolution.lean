module

public import Carleman.Periodic.Orientation
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# A periodic H¹ trajectory with almost-everywhere operator-domain values

The H-valued representative is continuous on [0,T], with matching endpoint
traces, and its derivative is defined by the distributional integration-by-parts
identity against every compactly supported smooth scalar test function in (0,T).
Both functions belong to L². Domain membership is required only a.e. The
auxiliary domain-valued representative is set to zero at exceptional times;
this changes neither weak derivatives nor traces of the original H trajectory.
Existence and graph estimates are deliberately not claimed here (bridge B1).
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace Carleman
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A choice-free modification on the null set where domain membership fails. -/
def domainRepresentative (D : Submodule ℝ H) (u : ℝ → H) (t : ℝ) : D :=
  by
    classical
    exact if h : u t ∈ D then ⟨u t, h⟩ else 0

theorem domainRepresentative_ae (D : Submodule ℝ H) (u : ℝ → H)
    (μ : Measure ℝ) (h : ∀ᵐ t ∂μ, u t ∈ D) :
    (fun t => (domainRepresentative D u t : H)) =ᵐ[μ] u := by
  filter_upwards [h] with t ht
  simp [domainRepresentative, ht]

/-- Lebesgue time measure on the open period; endpoints are handled as traces. -/
def TimeGrid.timeMeasure (g : TimeGrid) : Measure ℝ := volume.restrict (Ioo 0 g.period)

/-- The H-valued distributional derivative, with explicit local test support. -/
def HasWeakTimeDerivative (g : TimeGrid) (u du : ℝ → H) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo 0 g.period →
    (∫ t, deriv φ t • u t ∂g.timeMeasure) = -(∫ t, φ t • du t ∂g.timeMeasure)

theorem HasWeakTimeDerivative.congr {g : TimeGrid} {u v du : ℝ → H}
    (hu : HasWeakTimeDerivative g u du) (huv : u =ᵐ[g.timeMeasure] v) :
    HasWeakTimeDerivative g v du := by
  intro φ hφ hc hs
  have heq : (fun t => deriv φ t • u t) =ᵐ[g.timeMeasure] (fun t => deriv φ t • v t) := by
    filter_upwards [huv] with t ht
    rw [ht]
  rw [← integral_congr_ae heq]
  exact hu φ hφ hc hs

/-- B1 regularity; the operator is never applied to a value outside its domain. -/
structure PeriodicWeakTrajectory (g : TimeGrid) (D : Submodule ℝ H) (A : D →ₗ[ℝ] H)
    [CompleteSpace H] where
  value : ℝ → H
  derivative : ℝ → H
  continuous : ContinuousOn value (Icc 0 g.period)
  periodic_trace : value 0 = value g.period
  value_L2 : MemLp value 2 g.timeMeasure
  derivative_L2 : MemLp derivative 2 g.timeMeasure
  domain_ae : ∀ᵐ t ∂g.timeMeasure, value t ∈ D
  operator_L2 : MemLp (fun t => A (domainRepresentative D value t)) 2 g.timeMeasure
  weak_derivative : HasWeakTimeDerivative g value derivative

namespace PeriodicWeakTrajectory
variable [CompleteSpace H]
variable {g : TimeGrid} {D : Submodule ℝ H} {A : D →ₗ[ℝ] H}
  (u : PeriodicWeakTrajectory g D A)

def domainValue : ℝ → D := domainRepresentative D u.value

theorem domainValue_ae : (fun t => (u.domainValue t : H)) =ᵐ[g.timeMeasure] u.value :=
  domainRepresentative_ae D u.value g.timeMeasure u.domain_ae

theorem domainValue_L2 : MemLp (fun t => (u.domainValue t : H)) 2 g.timeMeasure :=
  u.value_L2.ae_eq u.domainValue_ae.symm

theorem domainValue_weakDerivative :
    HasWeakTimeDerivative g (fun t => (u.domainValue t : H)) u.derivative :=
  u.weak_derivative.congr u.domainValue_ae.symm

variable {X F : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  {V : Submodule ℝ H} {r : Reconstruction V X}

/-- Section 5 cancellation for the actual weak derivative and original H trajectory. -/
theorem residual_ae (l : LoadInterface r F) (s : Orientation)
    (μ : g.Sequence ℝ) (f : g.Sequence F) (z : g.Sequence X)
    (hFrozen : ∀ᵐ t ∂g.timeMeasure,
      s.sign • u.derivative t + A (u.domainValue t) + s.extension g μ t • u.value t =
        s.extension g (l.transferLoad g μ f z) t) :
    ∀ᵐ t ∂g.timeMeasure,
      s.sign • u.derivative t + A (u.domainValue t) =
        s.extension g (fun i => l.lift (f i)) t -
          s.extension g μ t • (u.value t - r.RH (s.extension g z t)) := by
  filter_upwards [hFrozen, u.domainValue_ae] with t ht heq
  rw [← heq] at ht ⊢
  cases s
  · exact l.residualPlus_eq g A 1 u.domainValue u.derivative μ f z t ht
  · exact l.residualMinus_eq g A (-1) u.domainValue u.derivative μ f z t ht

end PeriodicWeakTrajectory
end Carleman
