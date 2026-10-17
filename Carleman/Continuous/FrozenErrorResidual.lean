module

public import Carleman.Continuous.SobolevError
public import Carleman.Continuous.VariablePeriodicExistence

/-! The actual continuous-minus-Euler error for the same frozen problem.
The continuous state retains only a.e. domain membership, its H-valued weak
derivative, and its periodic H traces. No time derivative of the step function
or of the frozen multiplier is asserted. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {g : TimeGrid} {D : Submodule ℝ H} {A : D →ₗ[ℝ] H}

namespace PeriodicWeakTrajectory
variable (U : PeriodicWeakTrajectory g D A) (s : Orientation) (u : g.Sequence D)

def domainError (t : ℝ) : D := U.domainValue t - s.extension g u t

theorem domainError_value_ae :
    (fun t => (U.domainError s u t : H)) =ᵐ[g.timeMeasure]
      (fun t => U.value t - s.extension g (fun i => (u i : H)) t) := by
  filter_upwards [U.domainValue_ae] with t ht
  simp only [domainError, Submodule.coe_sub, ht]
  cases s <;> rfl

theorem domainError_L2 : MemLp (fun t => (U.domainError s u t : H)) 2 g.timeMeasure :=
  (U.value_L2.sub (s.memLp_extension g (fun i => (u i : H)))).ae_eq
    (U.domainError_value_ae s u).symm

theorem domainError_operator_L2 :
    MemLp (fun t => A (U.domainError s u t)) 2 g.timeMeasure := by
  have he : (fun t => A (U.domainError s u t)) =
      (fun t => A (U.domainValue t) - s.extension g (fun i => A (u i)) t) := by
    funext t
    simp only [domainError, map_sub]
    cases s <;> rfl
  rw [he]
  exact U.operator_L2.sub (s.memLp_extension g _)

/-- Subtract the actual two equations with the identical frozen coefficient.
There is no smooth-minus-frozen coefficient perturbation. -/
theorem domainError_residual_ae (μ : g.Sequence ℝ) (f : g.Sequence H)
    (hU : ∀ᵐ t ∂g.timeMeasure, s.sign • U.derivative t + A (U.domainValue t) +
      s.extension g μ t • U.value t = s.extension g f t)
    (hu : ∀ i, s.difference g (fun k => (u k : H)) i + A (u i) +
      μ i • (u i : H) = f i) :
    ∀ᵐ t ∂g.timeMeasure,
      A (U.domainError s u t) + s.extension g μ t • (U.domainError s u t : H) =
        s.extension g (s.difference g (fun i => (u i : H))) t - s.sign • U.derivative t := by
  filter_upwards [hU, U.domainValue_ae] with t hU ht
  have hd : s.extension g (s.difference g (fun i => (u i : H))) t +
      A (s.extension g u t) + s.extension g μ t • ((s.extension g u t : D) : H) =
      s.extension g f t := by
    cases s <;> exact hu _
  simp only [domainError, map_sub, Submodule.coe_sub, smul_sub, ht]
  calc
    _ = (s.sign • U.derivative t + A (U.domainValue t) + s.extension g μ t • U.value t) -
        (s.extension g (s.difference g (fun i => (u i : H))) t + A (s.extension g u t) +
          s.extension g μ t • ((s.extension g u t : D) : H)) +
        s.extension g (s.difference g (fun i => (u i : H))) t - s.sign • U.derivative t := by abel
    _ = _ := by rw [hU, hd]; abel

end PeriodicWeakTrajectory

/-- Both solutions of one actual frozen load; existence is proved below from A1. -/
structure FrozenEulerPair (g : TimeGrid) (s : Orientation) (μ : g.Sequence ℝ)
    {D : Submodule ℝ H} (A : D →ₗ[ℝ] H) (f : g.Sequence H) where
  nodes : g.Sequence D
  trajectory : PeriodicWeakTrajectory g D A
  discrete_equation : ∀ i, s.difference g (fun k => (nodes k : H)) i + A (nodes i) +
    μ i • (nodes i : H) = f i
  continuous_equation : ∀ᵐ t ∂g.timeMeasure,
    s.sign • trajectory.derivative t + A (trajectory.domainValue t) +
      s.extension g μ t • trajectory.value t = s.extension g f t

namespace CoerciveForm
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (b : CoerciveForm H E)

theorem IsAssociated.nonempty_frozenEulerPair (hA : b.IsAssociated A)
    (g : TimeGrid) (s : Orientation) (μ : g.Sequence ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (f : g.Sequence H) : Nonempty (FrozenEulerPair g s μ A f) := by
  obtain ⟨u, hu, _⟩ := hA.existsUnique_periodicEuler b g s μ hμ f
  let hf := s.memLp_extension g f
  have hnon : ∀ᵐ t ∂g.timeMeasure, 0 ≤ (s.frozenMultiplier g μ).value t :=
    Filter.Eventually.of_forall fun t => by
      change 0 ≤ s.extension g μ t
      cases s <;> exact hμ _
  obtain ⟨U, hU⟩ := hA.exists_variable_weak_periodic b g s (s.frozenMultiplier g μ)
    hnon (hf.toLp (s.extension g f))
  refine ⟨⟨u, U, hu, ?_⟩⟩
  filter_upwards [hU, hf.coeFn_toLp] with t ht hf
  exact ht.trans hf

end CoerciveForm
end Carleman
