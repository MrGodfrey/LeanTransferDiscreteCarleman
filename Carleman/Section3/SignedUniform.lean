module

public import Carleman.Section3.ProfileUniform

/-! Both signs of rho and all exponents share thresholds selected before the
period, grid, weight, load and state. Inversion changes both profile and exponent. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SpatialProfile
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
def signed (ρ : SpatialProfile ν) (e : Bool) : SpatialProfile ν := if e then ρ.neg else ρ

theorem signed_neg (ρ : SpatialProfile ν) (e : Bool) : (ρ.signed e).neg = ρ.signed (!e) := by
  cases e <;> simp [signed,neg_neg_profile]
end Carleman.SpatialProfile
namespace Carleman.Section3
variable {d m : ℕ} {S : Set (SpatialCoordinates d)}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (hΩ : IsBoundedLipschitzDomain S F)
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  (b : CoerciveForm (Lp ℝ 2 (volume.restrict S)) W)
  {V : Submodule ℝ (Lp ℝ 2 (volume.restrict S))}
  (hV : V ≤ sobolevSubspace d m (volume.restrict S) S)
  (hDV : b.domain ≤ V) (hD : b.domain ≤ sobolevSubspace d (2*m) (volume.restrict S) S)
  (a : V → V → ℝ)
  (htest : ∀ u : b.domain, ∀ v : V, a (b.domain.inclusion hDV u) v = inner ℝ (b.operator u) (v : Lp ℝ 2 (volume.restrict S)))
  (ρ : SpatialProfile (volume.restrict S)) (hρ : SmoothOnClosure ρ.value S)

include hρ htest in
set_option maxHeartbeats 2000000 in
theorem signed_uniform (hm : 0 < m) (Creg c C Ccomm β τStar : ℝ)
    (hc : 0 < c) (hCcomm : 0 ≤ Ccomm) (hβ : 0 < β) (hτStar : 0 ≤ τStar)
    (hell : ∀ v : b.domain, ‖domainSobolevJet hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hD v‖ ≤ Creg*‖b.operator v‖) :
    ∃ L₀ δ K : ℝ, 1 ≤ L₀ ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < K ∧ ∀ e : Bool,
      ProfileEstimates hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) b hV hDV hD a (ρ.signed e) c C Ccomm β τStar L₀ δ K := by
  obtain ⟨L₁,δ₁,K₁,hL₁,hδ₁,hd₁,hK₁,hp₁⟩ := profile_uniform hΩ b hV hDV hD a htest ρ hρ hm Creg c C Ccomm β τStar hc hCcomm hβ hτStar hell
  obtain ⟨L₂,δ₂,K₂,hL₂,hδ₂,hd₂,hK₂,hp₂⟩ := profile_uniform hΩ b hV hDV hD a htest ρ.neg hρ.neg hm Creg c C Ccomm β τStar hc hCcomm hβ hτStar hell
  refine ⟨max L₁ L₂,min δ₁ δ₂,max K₁ K₂,hL₁.trans (le_max_left _ _),lt_min hδ₁ hδ₂,
    (min_le_left _ _).trans hd₁,hK₁.trans_le (le_max_left _ _),?_⟩
  intro e
  cases e
  · exact hp₁.mono _ _ _ _ _ _ _ _ _ _ _ _ _ (le_max_left _ _) (min_le_left _ _) (le_max_left _ _)
  · exact hp₂.mono _ _ _ _ _ _ _ _ _ _ _ _ _ (le_max_right _ _) (min_le_right _ _) (le_max_right _ _)
end Carleman.Section3
