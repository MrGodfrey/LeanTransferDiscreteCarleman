module

public import Carleman.Weights.ClosureSpacetime
public import Carleman.Spatial.SpacetimeWeightedNorm

/-! Uniform two-sided conjugation of the actual space-time N norm, using
intrinsic smoothness up to the boundary and the original A2 domain action. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hbounded : Bornology.IsBounded S)
  (hνS : ∀ᵐ x ∂ν, x ∈ S)
  {D : Submodule ℝ (Lp ℝ 2 ν)} (hD : D ≤ sobolevSubspace d n ν S)

include hbounded
theorem closure_spacetime_energy_conjugation_uniform
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
      WeakSobolevJet.spacetimeWeightedNorm g w.q (fun _ => BoundedMultiplier.one) W ≤
        C*WeakSobolevJet.spacetimeWeightedNorm g w.q σ J ∧
      WeakSobolevJet.spacetimeWeightedNorm g w.q σ J ≤
        C*WeakSobolevJet.spacetimeWeightedNorm g w.q (fun _ => BoundedMultiplier.one) W := by
  obtain ⟨C, hC, hb⟩ := closure_conforming_conjugation_uniform hS hbounded hνS hD ρ hρ
  obtain ⟨_, _, hregularity⟩ := closure_spacetime_conjugation_uniform hS hbounded hνS hD ρ hρ
  refine ⟨C, hC, ?_⟩
  intro g w τ negative σ hq hw u hu J W
  have hW : MemLp W 2 g.timeMeasure := (hregularity g w τ negative hq hw u hu).1
  have hJfields (k : Fin (n+1)) : MemLp (WeakSobolevJet.parameterTimeField w.q σ J k)
      2 g.timeMeasure := by
    simpa only [one_mul] using WeakSobolevJet.memLp_parameterTimeField g w
      (if negative then ρ.neg else ρ) τ 1 hq hu k
  have hWfields (k : Fin (n+1)) :
      MemLp (WeakSobolevJet.parameterTimeField w.q (fun _ => BoundedMultiplier.one) W k)
        2 g.timeMeasure := by
    simpa only [one_mul] using WeakSobolevJet.memLp_unweightedParameterTimeField g w 1 hq hW k
  have hq0 : ∀ᵐ t ∂g.timeMeasure, 0 ≤ w.q t := Filter.Eventually.of_forall w.nonneg
  exact ⟨hW, WeakSobolevJet.spacetimeWeightedNorm_le g _ _ _ _ _ _ hWfields hJfields hq0 hq0
    hC.le (Filter.Eventually.of_forall fun t => (hb w τ t negative (hw t) (u t)).2.2.1),
    WeakSobolevJet.spacetimeWeightedNorm_le g _ _ _ _ _ _ hJfields hWfields hq0 hq0
      hC.le (Filter.Eventually.of_forall fun t => (hb w τ t negative (hw t) (u t)).2.2.2)⟩
end Carleman
