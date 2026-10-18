module

public import Carleman.Section4.CombinedEstimate

/-! Full uniform space-time error from original analytic/numerical data. -/
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

/-- Original Theorem 4.2, with the same original numerical hypotheses and
all constants preceding the period, grid, allowed weight and full state. -/
def CombinedUniform : Prop :=
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
      CombinedEstimate a r g s A (ρ.signed e) w L τ aE a0 ηA K

/-- One fixed threshold also covers the analytic comparison of all spatial
derivative weights. No numerical hypothesis is required outside |τ|≤τStar. -/
theorem combined_uniform_of_section3 (hbounded : Bornology.IsBounded S)
    (hρ : SmoothOnClosure ρ.value S) (hc : 0 < c) (hβ : 0 < β) (hτ : 0 ≤ τStar)
    (hCt : 0 ≤ Ctime) (hCs : 0 ≤ Csuper) (hδnum : 0 < δnum)
    {Kg δ : ℝ} {L₀ : ℝ → ℝ} (hKg : 0 < Kg) (hδ : 0 < δ)
    (H : Section3.Conclusions hS hν a.model a.sobolev a.domain_le hD a.scalarForm
      ρ c C Ccomm β τStar Kg L₀ δ) :
    CombinedUniform a hD ρ c C Ccomm β τStar Ctime Csuper δnum := by
  obtain ⟨Ls,δs,hLs,hδs,hs⟩ := spatial_uniform_of_section3 a hD ρ c C Ccomm β τStar Ctime Csuper δnum
    hbounded hρ hc hβ hτ hCt hCs hδnum hKg hδ H
  let δc := cellThreshold β (τStar+m) ρ.bound
  have hδc : 0 < δc := cellThreshold_pos hβ (by positivity) ρ.bound_nonneg
  refine ⟨max Ls (L₀ 1),min δs (min δ δc),hLs.trans (le_max_left _ _),
    lt_min hδs (lt_min hδ hδc),?_⟩
  intro L hL
  have hLsL : Ls ≤ L := (le_max_left _ _).trans hL
  have hL₀L : L₀ 1 ≤ L := (le_max_right _ _).trans hL
  obtain ⟨δx,ηstar,Ks,hδx,hδxnum,hηstar,hKs,hspatial⟩ := hs L hLsL
  refine ⟨δx,ηstar,Kg+3*Ks,hδx,hδxnum,hηstar,by positivity,?_⟩
  intro X _ _ r A b hA g s w hw htime τ e hτw ha mesh aE a0 ηA hmesh hx haE haE1 ha0 hη hηs happ happi T hdef
  have hmS : g.dt*w.max^2 ≤ δs := htime.trans (min_le_left _ _)
  have hmT : g.dt*w.max^2 ≤ δ := htime.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hmC : g.dt*w.max^2 ≤ cellThreshold β (τStar+m) (ρ.signed e).bound := by
    have hh := htime.trans ((min_le_right _ _).trans (min_le_right _ _))
    cases e <;> exact hh
  obtain ⟨he,h0⟩ := hspatial X r A b hA g s w hw hmS τ e hτw ha
    mesh aE a0 ηA hmesh hx haE haE1 ha0 hη hηs happ happi T hdef
  exact combined_estimate_of_spatial_temporal a r g s A (ρ.signed e) w L τ hD
    hw hτ hτw hmC hKg.le hKs.le haE ha0 hη
    (H.euler g s w hw L τ e hL₀L hmT hτw ha)
    (H.temporal g s w hw L τ e hL₀L hmT hτw ha) he h0

end Carleman.Section4

namespace Carleman.OriginalForm
variable {d m : ℕ} {S : Set (SpatialCoordinates d)}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (hΩ : IsBoundedLipschitzDomain S F)
  (a : OriginalForm (m := m) (ν := volume.restrict S) hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet))
  (hD : a.model.domain ≤ sobolevSubspace d (2*m) (volume.restrict S) S)
  (ρ : SpatialProfile (volume.restrict S)) (hρ : SmoothOnClosure ρ.value S)

include hρ in
/-- Original Theorem 4.2: actual frozen continuous and fully discrete
solutions have the original two space-time rates. All earlier estimates,
intermediary solutions, finite norms and uniform thresholds are internal. -/
theorem combined_uniform (hm : 0 < m) (Creg c C Ccomm β τStar Ctime Csuper δnum : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hCcomm : 0 ≤ Ccomm) (hβ : 0 < β) (hτStar : 0 ≤ τStar)
    (hCt : 0 ≤ Ctime) (hCs : 0 ≤ Csuper) (hδnum : 0 < δnum)
    (hell : ∀ v : a.model.domain, ‖domainSobolevJet hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hD v‖ ≤ Creg*‖a.model.operator v‖) :
    Section4.CombinedUniform a hD ρ c C Ccomm β τStar Ctime Csuper δnum := by
  obtain ⟨Kg,hKg,L₀,δ,hδ,_,H⟩ := a.section3 hΩ hD ρ hρ
    hm Creg c C Ccomm β τStar hc hC hCcomm hβ hτStar hell
  exact Section4.combined_uniform_of_section3 a hD ρ c C Ccomm β τStar Ctime Csuper δnum
    hΩ.isBounded hρ hc hβ hτStar hCt hCs hδnum hKg hδ H

end Carleman.OriginalForm

