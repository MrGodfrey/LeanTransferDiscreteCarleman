module

public import Carleman.Spatial.FullSpaceJetInterpolation
public import Carleman.Weights.ConformingConjugation

/-! The precise remaining geometric input, restricted to actual D(A) states.
This predicate is not an axiom and is not asserted for arbitrary domains.
All uses keep it explicit until a domain interpolation construction discharges it. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {D : Submodule ℝ (Lp ℝ 2 ν)} (hD : D ≤ sobolevSubspace d n ν S)

/-- Same constant for every parameter and every original operator-domain state.
The derivatives are the unique actual weak jet, and its complete graph norm. -/
def DomainParameterInterpolation (C : ℝ) : Prop :=
  ∀ r : ℝ, 1 ≤ r → ∀ u : D,
    conformingParameterNorm hS hν hD r BoundedMultiplier.one u ≤
      C*(‖domainSobolevJet hS hν hD u‖ + r^n*‖(u : Lp ℝ 2 ν)‖)

/-- Existing full-space weak interpolation supplies the interface on full space;
this does not assert any domain extension theorem. -/
theorem fullSpace_domain_parameter_interpolation
    {D : Submodule ℝ (Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))}
    (hD : D ≤ sobolevSubspace d n volume univ) :
    ∃ C : ℝ, 1 ≤ C ∧ DomainParameterInterpolation isOpen_univ
      (Filter.Eventually.of_forall fun _ => mem_univ _) hD C := by
  obtain ⟨C,hC,hI⟩ := WeakSobolevJet.fullSpace_parameter_interpolation_uniform d n
  refine ⟨C,hC,?_⟩
  intro r hr u
  have he := hI r (zero_le_one.trans hr)
    (domainSobolevJet isOpen_univ (Filter.Eventually.of_forall fun _ => mem_univ _) hD u)
  simpa only [conformingParameterNorm,WeakSobolevJet.parameterNorm,
    BoundedMultiplier.one_seminorm,domainSobolevJet_value] using he
end Carleman
