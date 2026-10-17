module

public import Carleman.Weights.SobolevGraphRegularity
public import Carleman.Weights.ClosureConforming
public import Carleman.Spatial.SobolevTimeGraph

/-! Two-sided conjugation for the manuscript's actual Bochner space-time R.
The same constant works before T, q, tau, sign, and the trajectory are chosen. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Carleman
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hbounded : Bornology.IsBounded S)
  (hνS : ∀ᵐ x ∂ν, x ∈ S)
  {D : Submodule ℝ (Lp ℝ 2 ν)} (hD : D ≤ sobolevSubspace d n ν S)

include hbounded
/-- Actual A2 domain multiplication has Bochner Sobolev regularity and both
R comparisons. Intrinsic closure smoothness suffices, with no exterior extension. -/
theorem closure_spacetime_conjugation_uniform
    (ρ : SpatialProfile ν) (hρ : SmoothOnClosure ρ.value S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : TimeGrid) (w : TimeWeight) (τ : ℝ) (negative : Bool),
      let σ := (if negative then ρ.neg else ρ).multiplier w τ
      ∀ _hq : AEStronglyMeasurable w.q g.timeMeasure,
      ∀ hw : ∀ t (u : D), (σ t).map (u : Lp ℝ 2 ν) ∈ D,
      ∀ u : ℝ → D,
      MemLp (fun t => domainSobolevJet hS hνS hD (u t)) 2 g.timeMeasure →
      let J := fun t => domainSobolevJet hS hνS hD (u t)
      let W := fun t => domainSobolevJet hS hνS hD (conformingWeight (σ t) (hw t) (u t))
      MemLp W 2 g.timeMeasure ∧
      WeakSobolevJet.spacetimeParameterNorm g w.q (fun _ => BoundedMultiplier.one) W ≤
        C*WeakSobolevJet.spacetimeParameterNorm g w.q σ J ∧
      WeakSobolevJet.spacetimeParameterNorm g w.q σ J ≤
        C*WeakSobolevJet.spacetimeParameterNorm g w.q (fun _ => BoundedMultiplier.one) W := by
  obtain ⟨C, hC, hb⟩ := closure_conforming_conjugation_uniform hS hbounded hνS hD ρ hρ
  refine ⟨(n+1:ℝ)*C, by positivity, ?_⟩
  intro g w τ negative σ hq hw u hu J W
  have h1 (t : ℝ) : WeakSobolevJet.parameterNorm (w.q t) BoundedMultiplier.one (W t) ≤
      C*WeakSobolevJet.parameterNorm (w.q t) (σ t) (J t) := (hb w τ t negative (hw t) (u t)).1
  have h2 (t : ℝ) : WeakSobolevJet.parameterNorm (w.q t) (σ t) (J t) ≤
      C*WeakSobolevJet.parameterNorm (w.q t) BoundedMultiplier.one (W t) :=
    (hb w τ t negative (hw t) (u t)).2.1
  have hW : MemLp W 2 g.timeMeasure := by
    apply WeakSobolevJet.memLp_of_weighted_value hS hνS g w
      (if negative then ρ.neg else ρ) τ hq hu _ hC.le h1
    intro t
    simp only [W, domainSobolevJet_value]
    rfl
  have hJfields (k : Fin (n+1)) : MemLp (WeakSobolevJet.parameterTimeField w.q σ J k)
      2 g.timeMeasure := by
    simpa only [one_mul] using WeakSobolevJet.memLp_parameterTimeField g w
      (if negative then ρ.neg else ρ) τ 1 hq hu k
  have hWfields (k : Fin (n+1)) :
      MemLp (WeakSobolevJet.parameterTimeField w.q (fun _ => BoundedMultiplier.one) W k)
        2 g.timeMeasure := by
    simpa only [one_mul] using WeakSobolevJet.memLp_unweightedParameterTimeField g w 1 hq hW k
  have hq0 : ∀ᵐ t ∂g.timeMeasure, 0 ≤ w.q t := Filter.Eventually.of_forall w.nonneg
  exact ⟨hW, WeakSobolevJet.spacetimeParameterNorm_le g _ _ _ _ _ _ hWfields hJfields hq0 hq0
    hC.le (Filter.Eventually.of_forall h1),
    WeakSobolevJet.spacetimeParameterNorm_le g _ _ _ _ _ _ hJfields hWfields hq0 hq0
      hC.le (Filter.Eventually.of_forall h2)⟩
end Carleman
