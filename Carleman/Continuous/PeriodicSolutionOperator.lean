module

public import Carleman.Continuous.ConstantPeriodicExistence

/-! The constructed constant-coefficient solution operator and its
T-uniform L² state estimate. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman.CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V) (g : TimeGrid) (s : Orientation) (r : ℝ) (hr : 0 ≤ r)

def constantEvolutionEquiv : b.PeriodicGraph g ≃L[ℝ] Lp H 2 g.timeMeasure :=
  ContinuousLinearEquiv.ofBijective (σ := RingHom.id ℝ) (σ' := RingHom.id ℝ) (E := b.PeriodicGraph g) (F := Lp H 2 g.timeMeasure) (b.evolution g s (g.constantMultiplier r))
    (LinearMap.ker_eq_bot.mpr (b.evolution_injective g s (g.constantMultiplier r)
      (Filter.Eventually.of_forall fun _ => hr)))
    (LinearMap.range_eq_top.mpr (b.evolution_constant_surjective g s r hr))

def constantSolve : Lp H 2 g.timeMeasure →L[ℝ] b.PeriodicGraph g :=
  (b.constantEvolutionEquiv g s r hr).symm.toContinuousLinearMap

theorem constantSolve_equation (f : Lp H 2 g.timeMeasure) :
    b.evolution g s (g.constantMultiplier r) (b.constantSolve g s r hr f) = f :=
  (b.constantEvolutionEquiv g s r hr).apply_symm_apply f

def constantStateSolve : Lp H 2 g.timeMeasure →L[ℝ] Lp H 2 g.timeMeasure :=
  g.fieldsValue.comp ((b.periodicGraphSubmodule g).subtypeL.comp (b.constantSolve g s r hr))

theorem constantStateSolve_eq (f : Lp H 2 g.timeMeasure) :
    b.constantStateSolve g s r hr f = g.pathL2 (b.constantSolve g s r hr f).val.1 := rfl

theorem constantStateSolve_bound (α : ℝ)
    (hα : ∀ x : b.domain, α * ‖(x : H)‖^2 ≤ inner ℝ (x : H) (b.operator x))
    (f : Lp H 2 g.timeMeasure) :
    (α+r) * ‖b.constantStateSolve g s r hr f‖ ≤ ‖f‖ := by
  have he := b.time_state_bound s r α hα (b.constantSolve g s r hr f)
  rw [b.constantSolve_equation] at he
  exact he

end Carleman.CoerciveForm
