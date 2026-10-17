module

public import Carleman.Continuous.GraphMeasurability
public import Carleman.Continuous.SobolevGraph

/-! Genuine graph measurability of the full weak Sobolev jet, inferred from
its scalar L² value. This does not assume a bounded inverse in the L² norm. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
instance spatialLp_secondCountable {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [TopologicalSpace.SeparableSpace E] (ν : Measure (SpatialCoordinates d))
    [IsFiniteMeasureOnCompacts ν] : SecondCountableTopology (Lp E 2 ν) := by
  have : SigmaFinite ν := SigmaFinite.of_isFiniteMeasureOnCompacts ν
  have : IsSeparable ν := inferInstance
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  exact Lp.SecondCountableTopology

namespace WeakSobolevJet
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
  [IsLocallyFiniteMeasure ν] {S : Set (SpatialCoordinates d)}

/-- The actual scalar H representative determines a measurable jet. -/
theorem aestronglyMeasurable_of_value (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {u : X → WeakSobolevJet d n ν S}
    (hu : AEStronglyMeasurable (fun t => value (u t)) μ) :
    AEStronglyMeasurable u μ := by
  have : SecondCountableTopology (JetFields d n ν) := inferInstance
  exact aestronglyMeasurable_of_injective_clm valueCLM (value_injective hS hν) hu
end WeakSobolevJet
end Carleman
