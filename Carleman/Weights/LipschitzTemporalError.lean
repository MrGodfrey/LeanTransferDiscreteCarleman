module

public import Carleman.Weights.InterpolatedTemporalError
public import Carleman.Spatial.LipschitzDomainParameterInterpolation

/-! Original bounded Lipschitz domain: the parameter interpolation premise
is proved from geometry. The remaining form, elliptic, and allowed-weight
hypotheses stay explicit; all states, both orientations and uniform grid
quantifiers are preserved. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.CoerciveForm
variable {d m : ℕ}
  {S : Set (SpatialCoordinates d)}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (hΩ : IsBoundedLipschitzDomain S F)
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  (b : CoerciveForm (Lp ℝ 2 (volume.restrict S)) W)
  {V : Submodule ℝ (Lp ℝ 2 (volume.restrict S))} (hV : V ≤ sobolevSubspace d m (volume.restrict S) S) (hDV : b.domain ≤ V)
  (hD : b.domain ≤ sobolevSubspace d (2*m) (volume.restrict S) S)
  (a : V → V → ℝ)
  (htest : ∀ u : b.domain, ∀ v : V,
    a (b.domain.inclusion hDV u) v = inner ℝ (b.operator u) (v : Lp ℝ 2 (volume.restrict S)))
  (ρ : SpatialProfile (volume.restrict S)) (hρ : SmoothOnClosure ρ.value S)

include hρ htest
set_option maxHeartbeats 1200000 in
theorem lipschitz_weighted_temporal_error_uniform (hm : 0 < m)
    (Creg c C Ccomm β τStar : ℝ) (hc : 0 < c) (hCcomm : 0 ≤ Ccomm) (hβ : 0 < β) (hτStar : 0 ≤ τStar)
    (hell : ∀ v : b.domain, ‖domainSobolevJet hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hD v‖ ≤ Creg*‖b.operator v‖) :
    ∃ L₀ δ : ℝ, 1 ≤ L₀ ∧ 0 < δ ∧
      ∀ (g : TimeGrid) (s : Orientation) (w : TimeWeight) (_h : TimeWeightRegularity w g β)
        (L τ : ℝ), L₀ ≤ L → g.dt*w.max^2 ≤ δ → |τ| ≤ τStar →
        AllowedWeightData hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hV hD a b.operator ρ w τ c C Ccomm →
        AllowedWeightData hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hV hD a b.operator ρ.neg w (-τ) c C Ccomm →
        ∀ f : g.Sequence (Lp ℝ 2 (volume.restrict S)),
        let μ := fun i => (L*w.nodes g i)^(2*m)
        let hμ : ∀ i, 0 ≤ μ i := fun _i => (even_two_mul m).pow_nonneg _
        let u := b.eulerSolution g s μ hμ f
        let F := g.l2Norm (ρ.nodeMap g w τ f)
        ∃ p : b.PeriodicGraph g,
          b.evolution g s (s.frozenMultiplier g μ) p = s.extensionLp g f ∧
          bochnerL2Norm g.timeMeasure (fun t => (ρ.multiplier w τ t).map
            (p.toTrajectory.value t-s.extension g (fun i => (u i : Lp ℝ 2 (volume.restrict S))) t)) ≤ 2160*g.dt*F ∧
          MemLp (fun t => domainSobolevJet hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hV
            (b.domain.inclusion hDV (p.toTrajectory.domainError s u t))) 2 g.timeMeasure ∧
          WeakSobolevJet.spacetimeWeightedNorm g w.q (ρ.multiplier w τ)
            (fun t => domainSobolevJet hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hV
              (b.domain.inclusion hDV (p.toTrajectory.domainError s u t))) ≤
            Real.sqrt (466560/c)*Real.sqrt g.dt*F := by
  obtain ⟨Cinterp,hCi,hI⟩ := boundedLipschitz_domain_parameter_interpolation hΩ hD
  exact b.interpolated_weighted_temporal_error_uniform hΩ.isOpen hΩ.isBounded
    (ae_restrict_mem hΩ.isOpen.measurableSet) hV hDV hD a htest ρ hρ hm
    Cinterp Creg c C Ccomm β τStar hCi hc hCcomm hβ hτStar hI hell
end Carleman.CoerciveForm
