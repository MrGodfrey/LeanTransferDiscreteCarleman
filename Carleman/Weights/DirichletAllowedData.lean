module

public import Carleman.Spatial.DirichletDomainOrders
public import Carleman.Weights.DirichletCommutator
public import Carleman.Weights.DirichletAllowedForm
public import Carleman.Section3.AllowedFamily

/-! Concrete A2/A3 data in the original transfer interfaces. Only the
H²-domain embedding from A1 is retained as an explicit independent premise. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

set_option maxHeartbeats 1600000 in
theorem dirichlet_allowed_data_uniform (hS : IsOpen S) (hd : 0 < d)
    (hb : Bornology.IsBounded S) (ρ : SpatialProfile (volume.restrict S))
    (hρ : SmoothOnClosure ρ.value S) :
    ∃ C Ccomm : ℝ, 1 ≤ C ∧ 0 < Ccomm ∧
    ∀ (hD : (boundedDirichletOriginalForm hS hd hb).model.domain ≤
        sobolevSubspace d 2 (volume.restrict S) S)
      (w : TimeWeight) (τ η : ℝ), |η|=1 →
      AllowedWeightData hS (ae_restrict_mem hS.measurableSet) (dirichletSubspace_sobolev S) hD
        (boundedDirichletOriginalForm hS hd hb).scalarForm
        (boundedDirichletOriginalForm hS hd hb).model.operator (ρ.scaled η) w τ (1/2) C Ccomm := by
  obtain ⟨C0,hC0,hlo⟩ := dirichlet_allowed_form_lower_uniform hS hd hb ρ hρ
  obtain ⟨Ccomm,hCc,hcomm⟩ := dirichlet_allowed_commutator_uniform hS hd hb ρ hρ
  refine ⟨max 1 C0,Ccomm,le_max_left _ _,hCc,?_⟩
  intro hD w τ η hη
  have hneg : ρ.scaled (-η)=(ρ.scaled η).neg := by
    cases ρ
    simp only [SpatialProfile.scaled,SpatialProfile.neg,neg_mul,abs_neg,Pi.neg_def]
  let hp := fun t (v : dirichletSubspace S) =>
    allowed_weight_mem_dirichlet hS hb ρ hρ w τ t η hη v v.property
  let hDσ := fun t => allowed_weight_mem_dirichlet_domain hS hd hb ρ hρ w τ t η hη
  have hDξ : ∀ t (z : (boundedDirichletOriginalForm hS hd hb).model.domain),
      ((ρ.scaled η).neg.multiplier w (-τ) t).map (z : Lp ℝ 2 (volume.restrict S)) ∈
        (boundedDirichletOriginalForm hS hd hb).model.domain := by
    rw [← hneg]
    exact fun t => allowed_weight_mem_dirichlet_domain hS hd hb ρ hρ w (-τ) t (-η) (by simpa using hη)
  refine ⟨hp,hDσ,hDξ,?_,?_⟩
  · intro t v
    have hl := hlo w τ t η hη v
    have hm : (1/2:ℝ)*(conformingWeightedNorm hS (ae_restrict_mem hS.measurableSet)
        (dirichletSubspace_sobolev S) (w.q t) ((ρ.scaled η).multiplier w τ t) v)^2-
        max 1 C0*(w.q t*((ρ.scaled η).multiplier w τ t).seminorm (v : Lp ℝ 2 (volume.restrict S)))^2 ≤
      (1/2:ℝ)*(conformingWeightedNorm hS (ae_restrict_mem hS.measurableSet)
        (dirichletSubspace_sobolev S) (w.q t) ((ρ.scaled η).multiplier w τ t) v)^2-
        C0*(w.q t*((ρ.scaled η).multiplier w τ t).seminorm (v : Lp ℝ 2 (volume.restrict S)))^2 :=
      sub_le_sub_left (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)) _
    simpa only [pow_one] using hm.trans hl
  · intro t z
    have hh := hcomm w τ t η hη z
    have ho := dirichlet_domain_lower_sum hS hd hb hD (w.q t) z
    change ‖conjugatedCommutator (boundedDirichletOriginalForm hS hd hb).model.operator
      ((ρ.scaled η).multiplier w τ t) ((ρ.scaled η).neg.multiplier w (-τ) t) (hDσ t) (hDξ t) z‖ ≤ _
    simpa only [Nat.mul_one,ho,hneg] using hh

set_option maxHeartbeats 1600000 in
theorem dirichlet_allowed_family_uniform (hS : IsOpen S) (hd : 0 < d)
    (hb : Bornology.IsBounded S) (ρ : SpatialProfile (volume.restrict S))
    (hρ : SmoothOnClosure ρ.value S) :
    ∃ C Ccomm : ℝ, 1 ≤ C ∧ 0 < Ccomm ∧
    ∀ (hD : (boundedDirichletOriginalForm hS hd hb).model.domain ≤
        sobolevSubspace d 2 (volume.restrict S) S) (w : TimeWeight) (τStar : ℝ),
      Section3.AllowedFamily hS (ae_restrict_mem hS.measurableSet) (dirichletSubspace_sobolev S) hD
        (boundedDirichletOriginalForm hS hd hb).scalarForm
        (boundedDirichletOriginalForm hS hd hb).model.operator ρ w (1/2) C Ccomm τStar := by
  obtain ⟨C,Ccomm,hC,hCc,hdata⟩ := dirichlet_allowed_data_uniform hS hd hb ρ hρ
  refine ⟨C,Ccomm,hC,hCc,?_⟩
  intro hD w τStar
  have hs (e : Bool) : ρ.signed e=ρ.scaled (if e then -1 else 1) := by
    cases e <;> simp only [SpatialProfile.signed,Bool.false_eq_true,ite_false,ite_true,
      SpatialProfile.scaled_one,SpatialProfile.scaled_neg_one]
  have hn (e : Bool) : (ρ.signed e).neg=ρ.scaled (-(if e then -1 else 1)) := by
    cases e <;> simp only [SpatialProfile.signed,Bool.false_eq_true,ite_false,ite_true,
      neg_neg,SpatialProfile.neg_neg_profile,SpatialProfile.scaled_one,SpatialProfile.scaled_neg_one]
  constructor
  · intro e τ _
    rw [hs]
    exact hdata hD w τ _ (by cases e <;> norm_num)
  · intro e τ _ t u v
    rw [hn,hs]
    have hu := dirichlet_allowed_form_upper hS hd hb ρ w τ t (if e then -1 else 1) u v
    exact hu.trans (by
      have hN : 0 ≤ conformingWeightedNorm hS (ae_restrict_mem hS.measurableSet)
          (dirichletSubspace_sobolev S) (w.q t) ((ρ.scaled (if e then -1 else 1)).multiplier w τ t) u :=
        WeakSobolevJet.weightedNorm_nonneg _ _ _
      have hI : 0 ≤ conformingWeightedNorm hS (ae_restrict_mem hS.measurableSet)
          (dirichletSubspace_sobolev S) (w.q t) ((ρ.scaled (-(if e then -1 else 1))).multiplier w (-τ) t) v :=
        WeakSobolevJet.weightedNorm_nonneg _ _ _
      nlinarith only [mul_le_mul_of_nonneg_right hC (mul_nonneg hN hI)])

end Carleman
