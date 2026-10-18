module

public import Carleman.Spatial.DomainJetInterpolation
public import Carleman.Spatial.DomainParameterInterpolation

/-! Discharge of the original-domain hI premise from bounded Lipschitz
geometry, with no new regularity restriction on any operator-domain state. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d n : ℕ} {S : Set (SpatialCoordinates d)}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem boundedLipschitz_domain_parameter_interpolation
    (hS : IsBoundedLipschitzDomain S F)
    {D : Submodule ℝ (Lp ℝ 2 ((volume : Measure (SpatialCoordinates d)).restrict S))}
    (hD : D ≤ sobolevSubspace d n (volume.restrict S) S) :
    ∃ C : ℝ, 1 ≤ C ∧ DomainParameterInterpolation hS.isOpen
      (ae_restrict_mem hS.isOpen.measurableSet) hD C := by
  obtain ⟨C,hC,hI⟩ := WeakSobolevJet.boundedLipschitz_parameter_interpolation hS n
  refine ⟨C,hC,?_⟩
  intro r hr u
  have he := hI r hr (domainSobolevJet hS.isOpen (ae_restrict_mem hS.isOpen.measurableSet) hD u)
  simpa only [conformingParameterNorm,WeakSobolevJet.parameterNorm,
    BoundedMultiplier.one_seminorm,domainSobolevJet_value] using he
/-- The manuscript's unweighted parameter graph estimate, using only the
forward elliptic bound from A1 after the proved original-domain interpolation. -/
theorem boundedLipschitz_operator_parameter_graph
    (hS : IsBoundedLipschitzDomain S F)
    {D : Submodule ℝ (Lp ℝ 2 ((volume : Measure (SpatialCoordinates d)).restrict S))}
    (hD : D ≤ sobolevSubspace d n (volume.restrict S) S)
    (A : D →ₗ[ℝ] Lp ℝ 2 (volume.restrict S)) (Creg : ℝ)
    (hell : ∀ u : D, ‖domainSobolevJet hS.isOpen (ae_restrict_mem hS.isOpen.measurableSet) hD u‖ ≤ Creg*‖A u‖) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ u : D,
      conformingParameterNorm hS.isOpen (ae_restrict_mem hS.isOpen.measurableSet) hD r BoundedMultiplier.one u ≤
        C*(‖A u‖+r^n*‖(u : Lp ℝ 2 (volume.restrict S))‖) := by
  obtain ⟨Ci,hCi,hI⟩ := boundedLipschitz_domain_parameter_interpolation hS hD
  let B := max 1 Creg
  have hB : 1 ≤ B := le_max_left _ _
  have hreg : Creg ≤ B := le_max_right _ _
  refine ⟨Ci*B,by nlinarith,?_⟩
  intro r hr u
  have hlow := mul_nonneg (pow_nonneg (zero_le_one.trans hr) n) (norm_nonneg (u : Lp ℝ 2 (volume.restrict S)))
  have hell' := (hell u).trans (mul_le_mul_of_nonneg_right hreg (norm_nonneg (A u)))
  have he := hI r hr u
  have hh : ‖domainSobolevJet hS.isOpen (ae_restrict_mem hS.isOpen.measurableSet) hD u‖+
      r^n*‖(u : Lp ℝ 2 (volume.restrict S))‖ ≤ B*(‖A u‖+r^n*‖(u : Lp ℝ 2 (volume.restrict S))‖) := by
    nlinarith
  exact he.trans ((mul_le_mul_of_nonneg_left hh (zero_le_one.trans hCi)).trans_eq (by ring))
end Carleman
