module

public import Carleman.Section3.Complete

/-! Full original variational operator input, with explicit domain and action
identification. Equalities transport all states and hypotheses into the proven
Section 3 theorem; there is no restriction to a core or a kernel. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.OriginalForm
variable {d m : ℕ} {S : Set (SpatialCoordinates d)}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (hΩ : IsBoundedLipschitzDomain S F)
  (a : OriginalForm (m := m) (ν := volume.restrict S) hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet))
  {D : Submodule ℝ (Lp ℝ 2 (volume.restrict S))} (A : D →ₗ[ℝ] Lp ℝ 2 (volume.restrict S))
  (hA : ∀ x f : Lp ℝ 2 (volume.restrict S),
    (∃ v : D, (v : Lp ℝ 2 (volume.restrict S)) = x ∧ A v = f) ↔
      ∃ v : a.V, (v : Lp ℝ 2 (volume.restrict S)) = x ∧ ∀ z : a.V,
        a.scalarForm v z = inner ℝ f (z : Lp ℝ 2 (volume.restrict S)))

include hA in
set_option maxHeartbeats 1600000 in
theorem identify_operator : ∃ hd : D = a.model.domain, ∀ v : D,
    a.model.operator ⟨v.val, hd ▸ v.property⟩ = A v := by
  have ha := (a.associated_iff A).mpr hA
  have hd := ha.domain_eq a.model
  subst D
  have he := ha.operator_eq a.model
  subst A
  exact ⟨rfl,fun _ => rfl⟩

include hA in
set_option maxHeartbeats 2000000 in
/-- Original A1 on D and A, followed by the complete original conclusions.
The returned domain equality and action equality identify the entire original
operator and make the transport in every norm and equation explicit. -/
theorem section3_original_operator
    (hD : D ≤ sobolevSubspace d (2*m) (volume.restrict S) S)
    (ρ : SpatialProfile (volume.restrict S)) (hρ : SmoothOnClosure ρ.value S)
    (hm : 0 < m) (Creg c C Ccomm β τStar : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hCcomm : 0 ≤ Ccomm) (hβ : 0 < β) (hτStar : 0 ≤ τStar)
    (hell : ∀ v : D, ‖domainSobolevJet hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hD v‖ ≤ Creg*‖A v‖) :
    ∃ hd : D = a.model.domain,
      (∀ v : D, a.model.operator ⟨v.val, hd ▸ v.property⟩ = A v) ∧
      ∃ K : ℝ, 0 < K ∧ ∃ (L₀ : ℝ → ℝ) (δ : ℝ), 0 < δ ∧ δ ≤ 1 ∧
        Section3.Conclusions hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) a.model
          a.sobolev a.domain_le (hd ▸ hD) a.scalarForm ρ c C Ccomm β τStar K L₀ δ := by
  have ha := (a.associated_iff A).mpr hA
  have hd := ha.domain_eq a.model
  subst D
  have he := ha.operator_eq a.model
  subst A
  exact ⟨rfl,fun _ => rfl,a.section3 hΩ hD ρ hρ hm Creg c C Ccomm β τStar hc hC hCcomm hβ hτStar hell⟩
end Carleman.OriginalForm
