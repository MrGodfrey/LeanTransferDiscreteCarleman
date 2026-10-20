module

public import Carleman.Spatial.CoefficientCommutator
public import Carleman.Weights.DirichletAllowedData

/-! The full allowed family for the original general weak coefficient form. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000
open MeasureTheory Set Filter
open scoped BigOperators ContDiff
namespace Carleman
variable {d m : ℕ} {S : Set (SpatialCoordinates d)}

theorem higherCoefficient_valueEquiv_jet (hS : IsOpen S)
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedMultiplier (volume.restrict S))
    (hsym : ∀ α β, (a α β).value =ᵐ[volume.restrict S] (a β α).value)
    (hcoer : ∃ c > (0:ℝ), ∀ v : HigherDirichletEnergy S m,
      c*‖v‖*‖v‖ ≤ higherCoefficientForm S m a v v)
    (v : higherDirichletSubspace S m) :
    higherDirichletToJet S m ((higherCoefficientOriginalForm hS a hsym hcoer).valueEquiv.symm v)=
      domainSobolevJet hS (ae_restrict_mem hS.measurableSet) (higherDirichletSubspace_sobolev S m) v := by
  apply WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)
  rw [domainSobolevJet_value]
  exact congrArg Subtype.val ((higherCoefficientOriginalForm hS a hsym hcoer).valueEquiv.apply_symm_apply v)

theorem higherCoefficient_scalarForm_canonical (hS : IsOpen S)
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedMultiplier (volume.restrict S))
    (hsym : ∀ α β, (a α β).value =ᵐ[volume.restrict S] (a β α).value)
    (hcoer : ∃ c > (0:ℝ), ∀ v : HigherDirichletEnergy S m,
      c*‖v‖*‖v‖ ≤ higherCoefficientForm S m a v v)
    (u v : higherDirichletSubspace S m) :
    (higherCoefficientOriginalForm hS a hsym hcoer).scalarForm u v=
      coefficientJetForm a
        (domainSobolevJet hS (ae_restrict_mem hS.measurableSet) (higherDirichletSubspace_sobolev S m) u)
        (domainSobolevJet hS (ae_restrict_mem hS.measurableSet) (higherDirichletSubspace_sobolev S m) v) := by
  change higherCoefficientForm S m a _ _ = _
  erw [higherCoefficientForm_apply,higherCoefficient_valueEquiv_jet,higherCoefficient_valueEquiv_jet]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem higherCoefficient_allowed_form_lower_uniform
    (hΩ : IsBoundedLipschitzDomain S F)
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedMultiplier (volume.restrict S))
    (hsym : ∀ α β, (a α β).value =ᵐ[volume.restrict S] (a β α).value)
    (hcoer : ∃ c > (0:ℝ), ∀ v : HigherDirichletEnergy S m,
      c*‖v‖*‖v‖ ≤ higherCoefficientForm S m a v v)
    (ρ : SpatialProfile (volume.restrict S)) (hρ : SmoothOnClosure ρ.value S) :
    ∃ c > (0:ℝ), ∃ C > (0:ℝ), ∀ (w : TimeWeight) (τ t η : ℝ) (_hη : |η|=1),
      let σ := (ρ.scaled η).multiplier w τ t
      ∀ (hp : ∀ v : higherDirichletSubspace S m, σ.map (v : Lp ℝ 2 (volume.restrict S)) ∈ higherDirichletSubspace S m)
        (v : higherDirichletSubspace S m),
      c*(conformingWeightedNorm hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet)
        (higherDirichletSubspace_sobolev S m) (w.q t) σ v)^2-
        C*(w.q t^m*σ.seminorm (v : Lp ℝ 2 (volume.restrict S)))^2 ≤
        (higherCoefficientOriginalForm hΩ.isOpen a hsym hcoer).scalarForm v
          (conformingWeight σ hp (conformingWeight σ hp v)) := by
  obtain ⟨c,hc,C,hC,hl⟩ := higherCoefficientForm_allowedWeight_lower hΩ
    (hρ.boundedSmoothOn hΩ.isBounded) a hcoer
  refine ⟨c,hc,C,hC,?_⟩
  intro w τ t η hη
  dsimp only
  intro hp v
  let σ := (ρ.scaled η).multiplier w τ t
  let z := conformingWeight σ hp (conformingWeight σ hp v)
  let f := higherCoefficientOriginalForm hΩ.isOpen a hsym hcoer
  have he : σ.value=(fun x => w.q t^τ*Real.exp (w.q t*(η*ρ.value x))) := by
    funext x
    change w.q t^τ*Real.exp ((η*ρ.value x)*w.q t)=_
    rw [mul_comm (η*ρ.value x)]
  have hv (u : higherDirichletSubspace S m) :
      WeakSobolevJet.value (higherDirichletToJet S m (f.valueEquiv.symm u))=(u : Lp ℝ 2 (volume.restrict S)) := by
    rw [higherCoefficient_valueEquiv_jet,domainSobolevJet_value]
  have hz : WeakSobolevJet.value (higherDirichletToJet S m (f.valueEquiv.symm z))=
      σ.map (σ.map (WeakSobolevJet.value (higherDirichletToJet S m (f.valueEquiv.symm v)))) := by
    rw [hv,hv]
    rfl
  have hh := hl (w.q t) (w.lower t) τ η hη σ he (f.valueEquiv.symm v) (f.valueEquiv.symm z) hz
  rw [higherCoefficient_valueEquiv_jet,domainSobolevJet_value] at hh
  exact hh

variable [IsFiniteMeasure (volume.restrict S)]

theorem higherCoefficient_allowed_data_uniform
    (hΩ : IsBoundedLipschitzDomain S F)
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedWeakCoefficient S (2*m))
    (hsym : ∀ α β, ((a α β).derivative []).value =ᵐ[volume.restrict S] ((a β α).derivative []).value)
    (hcoer : ∃ c > (0:ℝ), ∀ v : HigherDirichletEnergy S m,
      c*‖v‖*‖v‖ ≤ higherCoefficientForm S m (fun α β => (a α β).derivative []) v v)
    (ρ : SpatialProfile (volume.restrict S)) (hρ : SmoothOnClosure ρ.value S) :
    let f := higherCoefficientOriginalForm hΩ.isOpen (fun α β => (a α β).derivative []) hsym hcoer
    ∃ c > (0:ℝ), ∃ C Ccomm : ℝ, 0 < C ∧ 0 < Ccomm ∧
      ∀ (hD : f.model.domain ≤ sobolevSubspace d (2*m) (volume.restrict S) S)
        (w : TimeWeight) (τ η : ℝ), |η|=1 →
        AllowedWeightData hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet)
          (higherDirichletSubspace_sobolev S m) hD f.scalarForm f.model.operator
          (ρ.scaled η) w τ c C Ccomm := by
  dsimp only
  obtain ⟨c,hc,C,hC,hl⟩ := higherCoefficient_allowed_form_lower_uniform hΩ
    (fun α β => (a α β).derivative []) hsym hcoer ρ hρ
  -- The constant is independent of the regularity witness, time weight and state.
  obtain ⟨Ccomm,hCc,hcomm⟩ := coefficientDifferentialOperator_allowed_commutator hΩ.isOpen
    (hρ.boundedSmoothOn hΩ.isBounded) a
  refine ⟨c,hc,C,Ccomm,hC,hCc,?_⟩
  intro hD w τ η hη
  let f := higherCoefficientOriginalForm hΩ.isOpen (fun α β => (a α β).derivative []) hsym hcoer
  have hneg : ρ.scaled (-η)=(ρ.scaled η).neg := by
    cases ρ
    simp only [SpatialProfile.scaled,SpatialProfile.neg,neg_mul,abs_neg,Pi.neg_def]
  have hsmooth (t : ℝ) : BoundedSmoothOn (((ρ.scaled η).multiplier w τ t).value) S :=
    allowed_multiplier_boundedSmooth hΩ.isOpen hΩ.isBounded ρ hρ w τ t η hη
  let hp := fun t (v : higherDirichletSubspace S m) =>
    boundedSmooth_map_mem_higherDirichlet hΩ.isOpen ((ρ.scaled η).multiplier w τ t) (hsmooth t) v.val v.property
  let hDσ := fun t => higherCoefficient_operator_multiplier_preserves hΩ.isOpen a hsym hcoer hD
    ((ρ.scaled η).multiplier w τ t) (hsmooth t)
  have hDξ : ∀ t (z : f.model.domain),
      ((ρ.scaled η).neg.multiplier w (-τ) t).map (z : Lp ℝ 2 (volume.restrict S)) ∈ f.model.domain := by
    rw [←hneg]
    exact fun t => higherCoefficient_operator_multiplier_preserves hΩ.isOpen a hsym hcoer hD
      ((ρ.scaled (-η)).multiplier w (-τ) t)
      (allowed_multiplier_boundedSmooth hΩ.isOpen hΩ.isBounded ρ hρ w (-τ) t (-η) (by simpa using hη))
  refine ⟨hp,hDσ,hDξ,?_,?_⟩
  · intro t v
    exact hl w τ t η hη (hp t) v
  · intro t z
    let σ := (ρ.scaled η).multiplier w τ t
    let ξ := (ρ.scaled η).neg.multiplier w (-τ) t
    have hi : ∀ᵐ x ∂volume.restrict S, σ.value x*ξ.value x=1 :=
      Filter.Eventually.of_forall ((ρ.scaled η).multiplier_inverse w τ t)
    have he : σ.value=(fun x => w.q t^τ*Real.exp (w.q t*(η*ρ.value x))) := by
      funext x
      change w.q t^τ*Real.exp ((η*ρ.value x)*w.q t)=_
      rw [mul_comm (η*ρ.value x)]
    change ‖conjugatedCommutator f.model.operator σ ξ (hDσ t) (hDξ t) z‖ ≤ _
    rw [conjugatedCommutator_eq _ _ _ _ _ hi,
      higherCoefficient_operator_canonical hΩ.isOpen a hsym hcoer hD z,
      higherCoefficient_operator_canonical hΩ.isOpen a hsym hcoer hD (conformingWeight ξ (hDξ t) z)]
    apply hcomm (w.q t) (w.lower t) τ η hη σ he
    simp only [domainSobolevJet_value]
    exact (σ.map_inverse ξ hi z.val).symm

theorem higherCoefficient_allowed_family_uniform
    (hΩ : IsBoundedLipschitzDomain S F)
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedWeakCoefficient S (2*m))
    (hsym : ∀ α β, ((a α β).derivative []).value =ᵐ[volume.restrict S] ((a β α).derivative []).value)
    (hcoer : ∃ c > (0:ℝ), ∀ v : HigherDirichletEnergy S m,
      c*‖v‖*‖v‖ ≤ higherCoefficientForm S m (fun α β => (a α β).derivative []) v v)
    (ρ : SpatialProfile (volume.restrict S)) (hρ : SmoothOnClosure ρ.value S) :
    let f := higherCoefficientOriginalForm hΩ.isOpen (fun α β => (a α β).derivative []) hsym hcoer
    ∃ c > (0:ℝ), ∃ C Ccomm : ℝ, 0 < C ∧ 0 < Ccomm ∧
      ∀ (hD : f.model.domain ≤ sobolevSubspace d (2*m) (volume.restrict S) S)
        (w : TimeWeight) (τStar : ℝ),
        Section3.AllowedFamily hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet)
          (higherDirichletSubspace_sobolev S m) hD f.scalarForm f.model.operator
          ρ w c C Ccomm τStar := by
  dsimp only
  obtain ⟨c,hc,C0,Ccomm,hC0,hCc,hdata⟩ := higherCoefficient_allowed_data_uniform hΩ a hsym hcoer ρ hρ
  let B := ∑ α, ∑ β, ((a α β).derivative []).bound
  let C := max C0 B
  have hC : 0 < C := lt_of_lt_of_le hC0 (le_max_left _ _)
  refine ⟨c,hc,C,Ccomm,hC,hCc,?_⟩
  intro hD w τStar
  have hs (e : Bool) : ρ.signed e=ρ.scaled (if e then -1 else 1) := by
    cases e <;> simp only [SpatialProfile.signed,Bool.false_eq_true,ite_false,ite_true,
      SpatialProfile.scaled_one,SpatialProfile.scaled_neg_one]
  constructor
  · intro e τ _
    rw [hs]
    have hh := hdata hD w τ (if e then -1 else 1) (by cases e <;> norm_num)
    refine ⟨hh.form_preserving,hh.domain_preserving,hh.inverse_preserving,?_,hh.commutator⟩
    intro t v
    exact (sub_le_sub_left (mul_le_mul_of_nonneg_right (le_max_left C0 B) (sq_nonneg _)) _).trans (hh.coercive t v)
  · intro e τ _ t u v
    rw [higherCoefficient_scalarForm_canonical]
    have hi : ∀ᵐ x ∂volume.restrict S, ((ρ.signed e).multiplier w τ t).value x*
        ((ρ.signed e).neg.multiplier w (-τ) t).value x=1 :=
      Filter.Eventually.of_forall ((ρ.signed e).multiplier_inverse w τ t)
    have hu := coefficientJetForm_weighted_upper (fun α β => (a α β).derivative [])
      ((ρ.signed e).multiplier w τ t) ((ρ.signed e).neg.multiplier w (-τ) t) hi (w.lower t)
      (domainSobolevJet hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) (higherDirichletSubspace_sobolev S m) u)
      (domainSobolevJet hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) (higherDirichletSubspace_sobolev S m) v)
    exact hu.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right C0 B) (WeakSobolevJet.weightedNorm_nonneg _ _ _))
      (WeakSobolevJet.weightedNorm_nonneg _ _ _))


end Carleman
