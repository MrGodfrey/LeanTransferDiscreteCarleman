module

public import Carleman.Weights.InterpolatedEulerSobolev
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
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  (b : CoerciveForm (Lp ℝ 2 (volume.restrict S)) W)
  {V : Submodule ℝ (Lp ℝ 2 (volume.restrict S))} (hV : V ≤ sobolevSubspace d m (volume.restrict S) S)
  (hD : b.domain ≤ sobolevSubspace d (2*m) (volume.restrict S) S) (a : V → V → ℝ)
  (ρ : SpatialProfile (volume.restrict S)) (hρ : SmoothOnClosure ρ.value S)

include hρ
theorem lipschitz_weighted_euler_sobolev_uniform (hm : 0 < m)
    (Creg c C Ccomm β τStar : ℝ) (hCcomm : 0 ≤ Ccomm) (hβ : 0 < β) (hτStar : 0 ≤ τStar)
    (hell : ∀ v : b.domain, ‖domainSobolevJet hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hD v‖ ≤ Creg*‖b.operator v‖) :
    ∃ L₀ δ K : ℝ, 1 ≤ L₀ ∧ 0 < δ ∧ 0 < K ∧
      ∀ (g : TimeGrid) (s : Orientation) (w : TimeWeight) (_h : TimeWeightRegularity w g β)
        (L τ : ℝ), L₀ ≤ L → g.dt*w.max^2 ≤ δ → |τ| ≤ τStar →
        AllowedWeightData hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hV hD a b.operator ρ w τ c C Ccomm →
        ∀ u : g.Sequence b.domain,
        g.l2Norm (ρ.nodeMap g w τ (s.difference g (fun i => (u i : Lp ℝ 2 (volume.restrict S))))) +
          WeakSobolevJet.nodeParameterNorm g (w.nodes g)
            (fun i => ρ.multiplier w τ (g.nodeTime i)) (fun i => domainSobolevJet hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hD (u i)) ≤
          K*g.l2Norm (ρ.nodeMap g w τ (b.eulerResidual g s (fun i => (L*w.nodes g i)^(2*m)) u)) := by
  obtain ⟨Cinterp,hCi,hI⟩ := boundedLipschitz_domain_parameter_interpolation hΩ hD
  exact b.interpolated_weighted_euler_sobolev_uniform hΩ.isOpen hΩ.isBounded
    (ae_restrict_mem hΩ.isOpen.measurableSet) hV hD a ρ hρ hm
    Cinterp Creg c C Ccomm β τStar hCi hCcomm hβ hτStar hI hell
end Carleman.CoerciveForm
