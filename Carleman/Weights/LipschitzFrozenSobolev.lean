module

public import Carleman.Weights.InterpolatedFrozenSobolev
public import Carleman.Spatial.InterpolatedParameterGraph
public import Carleman.Spatial.LipschitzDomainParameterInterpolation

/-! The full continuous frozen R_{2m} graph on the original bounded
Lipschitz domain. This uses actual Bochner derivative-field norms and a.e.
operator-domain representatives; no weighted graph estimate is assumed. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.CoerciveForm
variable {d m : ℕ} {S : Set (SpatialCoordinates d)}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (hΩ : IsBoundedLipschitzDomain S F)
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  (b : CoerciveForm (Lp ℝ 2 (volume.restrict S)) W)
  (hD : b.domain ≤ sobolevSubspace d (2*m) (volume.restrict S) S)
  (ρ : SpatialProfile (volume.restrict S)) (hρ : SmoothOnClosure ρ.value S)

include hρ
set_option maxHeartbeats 1200000 in
theorem lipschitz_weighted_frozen_sobolev_uniform (hm : 0 < m)
    (Creg Ccomm β τStar : ℝ) (hCcomm : 0 ≤ Ccomm) (hβ : 0 < β) (hτStar : 0 ≤ τStar)
    (hell : ∀ v : b.domain, ‖domainSobolevJet hΩ.isOpen
      (ae_restrict_mem hΩ.isOpen.measurableSet) hD v‖ ≤ Creg*‖b.operator v‖) :
    ∃ L₀ δ K : ℝ, 1 ≤ L₀ ∧ 0 < δ ∧ 0 < K ∧
      ∀ (g : TimeGrid) (s extension : Orientation) (w : TimeWeight) (h : TimeWeightRegularity w g β)
        (L τ : ℝ), L₀ ≤ L → g.dt*w.max^2 ≤ δ → |τ| ≤ τStar →
        ∀ (hw : ∀ t, ∀ u : b.domain, (ρ.multiplier w τ t).map (u : Lp ℝ 2 (volume.restrict S)) ∈ b.domain)
          (hξ : ∀ t, ∀ u : b.domain, (ρ.neg.multiplier w (-τ) t).map (u : Lp ℝ 2 (volume.restrict S)) ∈ b.domain),
        (∀ t (v : b.domain), ‖allowedCommutatorPath b.operator ρ w τ hw hξ (fun _ => v) t‖ ≤
          Ccomm*∑ k : Fin (2*m), w.q t^(2*m-k.val)*
            ‖WeakSobolevJet.field k.castSucc (domainSobolevJet hΩ.isOpen
              (ae_restrict_mem hΩ.isOpen.measurableSet) hD v)‖) →
        ∀ p : b.PeriodicGraph g,
        let M := ρ.timeMap g w τ h.aestronglyMeasurable
        let μ := extension.frozenMultiplier g (fun i => (L*w.nodes g i)^(2*m))
        let J := fun t => domainSobolevJet hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hD
          (p.toTrajectory.domainValue t)
        MemLp J 2 g.timeMeasure ∧
          ‖M p.val.2.1‖+WeakSobolevJet.spacetimeParameterNorm g w.q (ρ.multiplier w τ) J ≤
            K*‖M (b.evolution g s μ p)‖ := by
  obtain ⟨Ci,hCi,hI⟩ := boundedLipschitz_domain_parameter_interpolation hΩ hD
  exact b.interpolated_weighted_frozen_sobolev_uniform hΩ.isOpen hΩ.isBounded
    (ae_restrict_mem hΩ.isOpen.measurableSet) hD ρ hρ hm
    Ci Creg Ccomm β τStar hCi hCcomm hβ hτStar hI hell
end Carleman.CoerciveForm
