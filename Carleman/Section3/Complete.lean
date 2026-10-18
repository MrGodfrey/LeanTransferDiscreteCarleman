module

public import Carleman.Section3.AllowedFamily
public import Carleman.Section3.OriginalForm

/-! One common threshold for the four genuine estimates. These are conclusions,
not hypotheses replacing the original analytic assumptions. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Section3
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  (b : CoerciveForm (Lp ℝ 2 ν) W)
  {V : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d m ν S)
  (hDV : b.domain ≤ V) (hD : b.domain ≤ sobolevSubspace d (2*m) ν S)
  (a : V → V → ℝ) (ρ : SpatialProfile ν) (c C Ccomm β τStar : ℝ)

/-- Full Lemmas 3.1, 3.3, 3.4 and Theorem 3.5 with one common choice of thresholds. -/
structure Conclusions (K : ℝ) (L₀ : ℝ → ℝ) (δ : ℝ) : Prop where
  threshold : ∀ B : ℝ, 0 < B → 1 ≤ L₀ B
  primitive : ∀ (B : ℝ), 0 < B → ∀ (g : TimeGrid) (s : Orientation)
    (w : TimeWeight) (h : TimeWeightRegularity w g β) (L τ : ℝ) (e : Bool),
    L₀ B ≤ L → |τ| ≤ τStar →
    AllowedFamily hS hν hV hD a b.operator ρ w c C Ccomm τStar → ∀ hLpos : 0 < L,
    ContinuousEstimate hS hν b hD g s w (ρ.signed e) τ K h.aestronglyMeasurable (h.shiftMultiplier m L hLpos)
  form_bound : ∀ (L : ℝ), 1 ≤ L → ∃ Cform : ℝ, 0 < Cform ∧
    ∀ (w : TimeWeight) (τ : ℝ) (e : Bool), |τ| ≤ τStar →
    AllowedFamily hS hν hV hD a b.operator ρ w c C Ccomm τStar → ∀ (t : ℝ) (v z : V),
    |shiftedForm a ((L*w.q t)^(2*m)) v z| ≤
      Cform*conformingWeightedNorm hS hν hV (w.q t) ((ρ.signed e).multiplier w τ t) v *
        conformingWeightedNorm hS hν hV (w.q t) ((ρ.signed e).neg.multiplier w (-τ) t) z
  form_coercive : ∀ (B : ℝ), 0 < B → ∀ (L : ℝ), L₀ B ≤ L →
    ∀ (w : TimeWeight) (τ : ℝ) (e : Bool) (hτ : |τ| ≤ τStar)
      (hd : AllowedFamily hS hν hV hD a b.operator ρ w c C Ccomm τStar) (t : ℝ) (v : V),
    c*(conformingWeightedNorm hS hν hV (w.q t) ((ρ.signed e).multiplier w τ t) v)^2 +
      B*(w.q t*((ρ.signed e).multiplier w τ t).seminorm (v : Lp ℝ 2 ν))^2 ≤
      shiftedForm a ((L*w.q t)^(2*m)) v
        (conformingWeight ((ρ.signed e).multiplier w τ t) ((hd.data e τ hτ).form_preserving t)
          (conformingWeight ((ρ.signed e).multiplier w τ t) ((hd.data e τ hτ).form_preserving t) v))
  euler : ∀ (g : TimeGrid) (s : Orientation) (w : TimeWeight) (_h : TimeWeightRegularity w g β)
    (L τ : ℝ) (e : Bool), L₀ 1 ≤ L → g.dt*w.max^2 ≤ δ → |τ| ≤ τStar →
    AllowedFamily hS hν hV hD a b.operator ρ w c C Ccomm τStar →
    EulerEstimate hS hν b hD g s w (ρ.signed e) L τ K
  frozen : ∀ (g : TimeGrid) (s extension : Orientation) (w : TimeWeight) (h : TimeWeightRegularity w g β)
    (L τ : ℝ) (e : Bool), L₀ 1 ≤ L → g.dt*w.max^2 ≤ δ → |τ| ≤ τStar →
    AllowedFamily hS hν hV hD a b.operator ρ w c C Ccomm τStar →
    ContinuousEstimate hS hν b hD g s w (ρ.signed e) τ K h.aestronglyMeasurable
      (extension.frozenMultiplier g (fun i => (L*w.nodes g i)^(2*m)))
  temporal : ∀ (g : TimeGrid) (s : Orientation) (w : TimeWeight) (_h : TimeWeightRegularity w g β)
    (L τ : ℝ) (e : Bool), L₀ 1 ≤ L → g.dt*w.max^2 ≤ δ → |τ| ≤ τStar →
    AllowedFamily hS hν hV hD a b.operator ρ w c C Ccomm τStar →
    TemporalEstimate hS hν b hV hDV g s w (ρ.signed e) L τ K

end Carleman.Section3
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
theorem complete_uniform (hm : 0 < m) (Creg c C Ccomm β τStar : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hCcomm : 0 ≤ Ccomm) (hβ : 0 < β) (hτStar : 0 ≤ τStar)
    (hell : ∀ v : b.domain, ‖domainSobolevJet hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hD v‖ ≤ Creg*‖b.operator v‖) :
    ∃ K : ℝ, 0 < K ∧ ∃ (L₀ : ℝ → ℝ) (δ : ℝ), 0 < δ ∧ δ ≤ 1 ∧
      Conclusions hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) b hV hDV hD a ρ c C Ccomm β τStar K L₀ δ := by
  obtain ⟨Lc,δ,K,hLc,hδ,hd,hK,hp⟩ := signed_uniform hΩ b hV hDV hD a htest ρ hρ
    hm Creg c C Ccomm β τStar hc hCcomm hβ hτStar hell
  let L₀ : ℝ → ℝ := fun B => max Lc (max 1 (C+B))
  have hbase (B : ℝ) : Lc ≤ L₀ B := le_max_left _ _
  have hone (B : ℝ) : 1 ≤ L₀ B := hLc.trans (hbase B)
  refine ⟨K,hK,L₀,δ,hδ,hd,?_⟩
  constructor
  · exact fun B _ => hone B
  · intro B _ g s w h L τ e hL hτ ha hLpos
    exact (hp e).shift g s w h L τ hLpos ((hbase B).trans hL) hτ (ha.data e τ hτ)
  · intro L hL
    refine ⟨C+L^(2*m),by positivity,?_⟩
    intro w τ e hτ ha t v z
    exact allowed_shiftedForm_bound _ _ hV a (ρ.signed e) w τ t (zero_le_one.trans hL)
      (ha.upper e τ hτ t) v z
  · intro B hB L hL w τ e hτ ha t v
    have hpow : C+B ≤ L^(2*m) := by
      apply ((le_max_right (1:ℝ) (C+B)).trans ((le_max_right _ _).trans hL)).trans
      simpa only [pow_one] using pow_le_pow_right₀ ((hone B).trans hL) (show 1 ≤ 2*m by omega)
    exact shiftedForm_coercive _ _ hV a hm (w.lower t) hB.le hpow _
      ((ha.data e τ hτ).form_preserving t) ((ha.data e τ hτ).coercive t) v
  · intro g s w h L τ e hL hmsh hτ ha
    exact (hp e).euler g s w h L τ ((hbase 1).trans hL) hmsh hτ (ha.data e τ hτ)
  · intro g s ex w h L τ e hL hmsh hτ ha
    exact (hp e).frozen g s ex w h L τ ((hbase 1).trans hL) hmsh hτ (ha.data e τ hτ)
  · intro g s w h L τ e hL hmsh hτ ha
    exact (hp e).temporal g s w h L τ ((hbase 1).trans hL) hmsh hτ (ha.data e τ hτ)
      (ha.inverse _ _ _ _ _ _ _ _ _ _ _ _ e τ hτ)
end Carleman.Section3

namespace Carleman.OriginalForm
variable {d m : ℕ} {S : Set (SpatialCoordinates d)}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (hΩ : IsBoundedLipschitzDomain S F)
  (a : OriginalForm (m := m) (ν := volume.restrict S) hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet))
  (hD : a.model.domain ≤ sobolevSubspace d (2*m) (volume.restrict S) S)
  (ρ : SpatialProfile (volume.restrict S)) (hρ : SmoothOnClosure ρ.value S)

include hρ in
set_option maxHeartbeats 2000000 in
/-- Original V and A1 instantiate every Section 3 conclusion; hI and the
form/operator testing identity are supplied internally by proved bridges. -/
theorem section3 (hm : 0 < m) (Creg c C Ccomm β τStar : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hCcomm : 0 ≤ Ccomm) (hβ : 0 < β) (hτStar : 0 ≤ τStar)
    (hell : ∀ v : a.model.domain, ‖domainSobolevJet hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hD v‖ ≤ Creg*‖a.model.operator v‖) :
    ∃ K : ℝ, 0 < K ∧ ∃ (L₀ : ℝ → ℝ) (δ : ℝ), 0 < δ ∧ δ ≤ 1 ∧
      Section3.Conclusions hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) a.model
        a.sobolev a.domain_le hD a.scalarForm ρ c C Ccomm β τStar K L₀ δ :=
  Section3.complete_uniform hΩ a.model a.sobolev a.domain_le hD a.scalarForm a.operator_test ρ hρ
    hm Creg c C Ccomm β τStar hc hC hCcomm hβ hτStar hell
end Carleman.OriginalForm
