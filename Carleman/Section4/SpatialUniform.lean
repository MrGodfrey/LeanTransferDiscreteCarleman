module

public import Carleman.Section4.EnergyUniform
public import Carleman.Section4.L2Estimate

/-! Full Lemma 4.1: energy and L² rates with one uniform choice of
constants, on every original conforming reconstruction and actual state. -/
@[expose] public noncomputable section
open MeasureTheory Set
universe u
namespace Carleman.Section4
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} {hS : IsOpen S} {hν : ∀ᵐ x ∂ν, x ∈ S}
  (a : OriginalForm (m := m) hS hν)
  (hD : a.model.domain ≤ sobolevSubspace d (2*m) ν S)
  (ρ : SpatialProfile ν) (c C Ccomm β τStar Ctime Csuper δnum : ℝ)

/-- Original Lemma 4.1. Both signs and orientations and the full discrete
space occur after the constants. N3 is supplied at σ and σ⁻¹, as in the
original allowed family, and all spatial bounds are conclusions. -/
def SpatialUniform : Prop :=
  ∃ Lmin δt : ℝ, 1 ≤ Lmin ∧ 0 < δt ∧ ∀ L : ℝ, Lmin ≤ L →
    ∃ δx ηstar K : ℝ, 0 < δx ∧ δx ≤ δnum ∧ 0 < ηstar ∧ 0 < K ∧
      ∀ (X : Type u) [NormedAddCommGroup X] [InnerProductSpace ℝ X]
      (r : Reconstruction a.V X) (A : X →ₗ[ℝ] X) (b : X →ₗ[ℝ] X →ₗ[ℝ] ℝ),
      (∀ z v, inner ℝ (A z) v = a.scalarForm (r.R z) (r.R v)+b z v) →
      ∀ (g : TimeGrid) (s : Orientation) (w : TimeWeight), TimeWeightRegularity w g β →
      g.dt*w.max^2 ≤ δt → ∀ (τ : ℝ) (e : Bool), |τ| ≤ τStar →
      Section3.AllowedFamily hS hν a.sobolev hD a.scalarForm a.model.operator ρ w c C Ccomm τStar →
      ∀ (mesh aE a0 ηA : ℝ), 0 ≤ mesh → mesh*w.max ≤ δx →
      0 ≤ aE → aE ≤ 1 → 0 ≤ a0 → 0 ≤ ηA → ηA ≤ ηstar →
      WeightedApproximation hS hν a.sobolev hD a.domain_le r g (ρ.signed e) w τ aE a0 →
      WeightedApproximation hS hν a.sobolev hD a.domain_le r g (ρ.signed e).neg w (-τ) aE a0 →
      WeightedTest hS hν a.sobolev r g (ρ.signed e) w τ Ctime Csuper mesh →
      (∀ i z v, |b z v| ≤
        ηA*conformingWeightedNorm hS hν a.sobolev (w.q (g.nodeTime i))
          ((ρ.signed e).multiplier w τ (g.nodeTime i)) (r.R z)*
        conformingWeightedNorm hS hν a.sobolev (w.q (g.nodeTime i))
          ((ρ.signed e).neg.multiplier w (-τ) (g.nodeTime i)) (r.R v)) →
      EnergyEstimate a r A g s (ρ.signed e) w L τ aE ηA K ∧
      L2Estimate a r A g s (ρ.signed e) w L τ aE a0 ηA K

/-- Assemble Cea and actual opposite-Euler duality with the Section 3
dependency. The original-form wrapper discharges that dependency. -/
theorem spatial_uniform_of_section3 (hbounded : Bornology.IsBounded S)
    (hρ : SmoothOnClosure ρ.value S) (hc : 0 < c) (hβ : 0 < β) (hτ : 0 ≤ τStar)
    (hCt : 0 ≤ Ctime) (hCs : 0 ≤ Csuper) (hδnum : 0 < δnum)
    {Kg δ : ℝ} {L₀ : ℝ → ℝ} (hKg : 0 < Kg) (hδ : 0 < δ)
    (H : Section3.Conclusions hS hν a.model a.sobolev a.domain_le hD a.scalarForm
      ρ c C Ccomm β τStar Kg L₀ δ) :
    SpatialUniform a hD ρ c C Ccomm β τStar Ctime Csuper δnum := by
  obtain ⟨Le,δe,hLe,hδe,he⟩ := energy_uniform_of_section3 a hD ρ c C Ccomm β τStar Ctime Csuper δnum
    hbounded hρ hc hβ hτ hCt hCs hδnum hKg hδ H
  refine ⟨max Le (L₀ 1),min δe δ,hLe.trans (le_max_left _ _),lt_min hδe hδ,?_⟩
  intro L hL
  have hLeL : Le ≤ L := (le_max_left _ _).trans hL
  have hL₀L : L₀ 1 ≤ L := (le_max_right _ _).trans hL
  obtain ⟨δx,ηstar,Ke,hδx,hδxnum,hηstar,hKe,henergy⟩ := he L hLeL
  obtain ⟨Cf,hCf,hform⟩ := H.form_bound L (hLe.trans hLeL)
  let K₂ := (Kg+Cf*Ke+Ke*(m+2))*Kg
  refine ⟨δx,ηstar,max Ke K₂,hδx,hδxnum,hηstar,hKe.trans_le (le_max_left _ _),?_⟩
  intro X _ _ r A b hA g s w hw htime τ e hτw ha mesh aE a0 ηA hmesh hx haE haE1 ha0 hη hηs happ happi T hdef
  have hg : Section3.EulerEstimate hS hν a.model hD g s w (ρ.signed e) L τ Kg :=
    H.euler g s w hw L τ e hL₀L (htime.trans (min_le_right _ _)) hτw ha
  have hd : Section3.EulerEstimate hS hν a.model hD g s.opposite w (ρ.signed e).neg L (-τ) Kg := by
    rw [ρ.signed_neg]
    exact H.euler g s.opposite w hw L (-τ) (!e) hL₀L (htime.trans (min_le_right _ _))
      (by simpa only [abs_neg] using hτw) ha
  have hE := henergy X r A b hA g s w hw (htime.trans (min_le_left _ _)) τ e hτw ha
    mesh aE a0 ηA hmesh hx haE haE1 hη hηs happ T hdef
  have h₂ := l2_estimate_of_energy a hD r A g s (ρ.signed e) w L τ
    haE haE1 ha0 hη hCf.le hKe.le hKg.le b hA happi
    (fun i v z => hform w τ e hτw ha (g.nodeTime i) v z) hdef hE hg hd
  constructor
  · intro f u z hu hz
    obtain ⟨herr,hstate⟩ := hE f u z hu hz
    constructor
    · exact herr.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg haE hη)) (g.l2Norm_nonneg _))
    · exact hstate.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (g.l2Norm_nonneg _))
  · intro f u z hu hz
    exact (h₂ f u z hu hz).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) (g.l2Norm_nonneg _))

end Carleman.Section4

namespace Carleman.OriginalForm
variable {d m : ℕ} {S : Set (SpatialCoordinates d)}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (hΩ : IsBoundedLipschitzDomain S F)
  (a : OriginalForm (m := m) (ν := volume.restrict S) hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet))
  (hD : a.model.domain ≤ sobolevSubspace d (2*m) (volume.restrict S) S)
  (ρ : SpatialProfile (volume.restrict S)) (hρ : SmoothOnClosure ρ.value S)

include hρ in
/-- Full original Lemma 4.1 from A1–A3 and N1/N3/N4, including the original
energy and a₀+a_E²+η_A L² rates. All Section 3 estimates and absorption
conditions are proved dependencies, not additional premises. -/
theorem spatial_uniform (hm : 0 < m) (Creg c C Ccomm β τStar Ctime Csuper δnum : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hCcomm : 0 ≤ Ccomm) (hβ : 0 < β) (hτStar : 0 ≤ τStar)
    (hCt : 0 ≤ Ctime) (hCs : 0 ≤ Csuper) (hδnum : 0 < δnum)
    (hell : ∀ v : a.model.domain, ‖domainSobolevJet hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hD v‖ ≤ Creg*‖a.model.operator v‖) :
    Section4.SpatialUniform a hD ρ c C Ccomm β τStar Ctime Csuper δnum := by
  obtain ⟨Kg,hKg,L₀,δ,hδ,_,H⟩ := a.section3 hΩ hD ρ hρ
    hm Creg c C Ccomm β τStar hc hC hCcomm hβ hτStar hell
  exact Section4.spatial_uniform_of_section3 a hD ρ c C Ccomm β τStar Ctime Csuper δnum
    hΩ.isBounded hρ hc hβ hτStar hCt hCs hδnum hKg hδ H

end Carleman.OriginalForm
