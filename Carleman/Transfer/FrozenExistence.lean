module

public import Carleman.Continuous.VariablePeriodicExistence
public import Carleman.Transfer.SobolevBridges

/-! Discharge the frozen auxiliary-solution existence quantifier for the
actual Section 5 load, every discrete state, and both orientations. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman.LoadInterface
variable {H E X F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  {V D : Submodule ℝ H} {r : Reconstruction V X} (l : LoadInterface r F)
  (b : CoerciveForm H E) {A : D →ₗ[ℝ] H} (hA : b.IsAssociated A)
  (g : TimeGrid) (s : Orientation) (μ : g.Sequence ℝ) (hμ : ∀ i, 0 ≤ μ i)
  (f : g.Sequence F) (z : g.Sequence X)
include hA hμ

/-- No linearity of Γ or of the lift, and no restriction on the discrete state, is required. -/
theorem exists_frozen_transfer_trajectory :
    ∃ u : PeriodicWeakTrajectory g D A, ∀ᵐ t ∂g.timeMeasure,
      s.sign • u.derivative t + A (u.domainValue t) + s.extension g μ t • u.value t =
        s.extension g (l.transferLoad g μ f z) t := by
  let load : Lp H 2 g.timeMeasure :=
    (s.memLp_extension g (l.transferLoad g μ f z)).toLp (s.extension g (l.transferLoad g μ f z))
  have hnon : ∀ᵐ t ∂g.timeMeasure, 0 ≤ (s.frozenMultiplier g μ).value t :=
    Filter.Eventually.of_forall fun t => by
      change 0 ≤ s.extension g μ t
      cases s <;> exact hμ _
  obtain ⟨u, hu⟩ := hA.exists_variable_weak_periodic b g s (s.frozenMultiplier g μ) hnon load
  refine ⟨u, ?_⟩
  filter_upwards [hu, (s.memLp_extension g (l.transferLoad g μ f z)).coeFn_toLp] with t ht hf
  exact ht.trans hf

end Carleman.LoadInterface
