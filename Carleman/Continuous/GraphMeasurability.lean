module

public import Carleman.Continuous.RegularTimeCore
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! Measurability of the actual closed operator graph. A domain-valued path
need only be strongly measurable as an H-valued path. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman

/-- A continuous injective map from a complete separable space reflects
strong measurability, by the Borel inverse theorem. -/
theorem aestronglyMeasurable_of_injective_clm
    {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace X] {μ : Measure X} (L : E →L[ℝ] F) (hL : Function.Injective L)
    {u : X → E} (hu : AEStronglyMeasurable (fun t => L (u t)) μ) :
    AEStronglyMeasurable u μ := by
  let : MeasurableSpace E := borel E
  let : MeasurableSpace F := borel F
  have : BorelSpace E := ⟨rfl⟩
  have : BorelSpace F := ⟨rfl⟩
  exact ((L.continuous.measurableEmbedding hL).aemeasurable_comp_iff.mp
    hu.aemeasurable).aestronglyMeasurable

namespace CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V)

theorem operator_aestronglyMeasurable {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {u : X → b.domain} (hu : AEStronglyMeasurable (fun t => (u t : H)) μ) :
    AEStronglyMeasurable (fun t => b.operator (u t)) μ := by
  have hg : AEStronglyMeasurable (fun t => b.graphOfDomain (u t)) μ :=
    aestronglyMeasurable_of_injective_clm b.graphH b.graphH_injective hu
  exact b.graphA.continuous.comp_aestronglyMeasurable hg

/-- This transports to the original A:D(A)→H using its full A1 definition. -/
theorem IsAssociated.operator_aestronglyMeasurable
    {D : Submodule ℝ H} {A : D →ₗ[ℝ] H} (hA : b.IsAssociated A)
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {u : X → D} (hu : AEStronglyMeasurable (fun t => (u t : H)) μ) :
    AEStronglyMeasurable (fun t => A (u t)) μ := by
  have hd := hA.domain_eq b
  subst D
  have ha := hA.operator_eq b
  subst A
  exact b.operator_aestronglyMeasurable hu
end CoerciveForm
end Carleman
