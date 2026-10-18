module

public import Carleman.Spatial.DirichletScalarForm

/-! Both original A3 estimates for the actual Dirichlet gradient form and
all original smooth-on-closure allowed weights. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem allowed_weak_form_lower_uniform (hS : IsOpen S) (hb : Bornology.IsBounded S)
    (ρ : SpatialProfile (volume.restrict S)) (hρ : SmoothOnClosure ρ.value S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : TimeWeight) (τ t η : ℝ), |η|=1 →
      ∀ (u v z : WeakSobolevJet d 1 (volume.restrict S) S),
      WeakSobolevJet.value v=((ρ.scaled η).multiplier w τ t).map (WeakSobolevJet.value u) →
      WeakSobolevJet.value z=((ρ.scaled η).multiplier w τ t).map (WeakSobolevJet.value v) →
      (1/2:ℝ)*(WeakSobolevJet.weightedNorm (w.q t) ((ρ.scaled η).multiplier w τ t) u)^2-
        C*(w.q t*((ρ.scaled η).multiplier w τ t).seminorm (WeakSobolevJet.value u))^2 ≤
          weakGradientPairing u z := by
  obtain ⟨B,hB,hcoeff⟩ := (hρ.boundedSmoothOn hb).allowedWeight_word_uniform hS 1
  refine ⟨(1/2:ℝ)+2*(d:ℝ)*B^2,by positivity,?_⟩
  intro w τ t η hη u v z hv hz
  let σ := (ρ.scaled η).multiplier w τ t
  have hσ := allowed_multiplier_boundedSmooth hS hb ρ hρ w τ t η hη
  have hν : ∀ᵐ x ∂volume.restrict S, x ∈ S := ae_restrict_mem hS.measurableSet
  let dw := fun i => intrinsicWordMultiplier hS hν hσ [i]
  have hdw (i : Fin d) : (dw i).value =ᵐ[volume.restrict S]
      (fun x => fderiv ℝ σ.value x (EuclideanSpace.basisFun (Fin d) ℝ i)) := by
    change wordDerivative [i] σ.value =ᵐ[volume.restrict S] _
    simpa only [intrinsicWordMultiplier,wordDerivative_nil] using
      intrinsicWordMultiplier_derivative hS hν hσ [] i
  have he : σ.value=(fun x => w.q t^τ*Real.exp (w.q t*(η*ρ.value x))) := by
    funext x
    change w.q t^τ*Real.exp ((η*ρ.value x)*w.q t)= _
    rw [mul_comm (η*ρ.value x)]
  have hbound (i : Fin d) : ∀ᵐ x ∂volume.restrict S, |(dw i).value x| ≤ B*w.q t*|σ.value x| := by
    apply hν.mono
    intro x hx
    change |wordDerivative [i] σ.value x| ≤ _
    rw [he,abs_of_pos (mul_pos (Real.rpow_pos_of_pos (w.pos t) _) (Real.exp_pos _))]
    simpa using hcoeff (w.q t) (w.lower t) τ η hη [i] (by simp) x hx
  exact weakGradientPairing_weighted_lower hS hν σ dw hσ.1 hdw u v z hv hz
    (w.nonneg t) hB.le hbound

set_option maxHeartbeats 1000000 in
theorem dirichlet_allowed_form_lower_uniform (hS : IsOpen S) (hd : 0 < d)
    (hb : Bornology.IsBounded S) (ρ : SpatialProfile (volume.restrict S))
    (hρ : SmoothOnClosure ρ.value S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : TimeWeight) (τ t η : ℝ) (hη : |η|=1),
    let σ := (ρ.scaled η).multiplier w τ t
    let hp := fun v : dirichletSubspace S => allowed_weight_mem_dirichlet hS hb ρ hρ w τ t η hη v v.property
    ∀ u : dirichletSubspace S,
      (1/2:ℝ)*(conformingWeightedNorm hS (ae_restrict_mem hS.measurableSet)
        (dirichletSubspace_sobolev S) (w.q t) σ u)^2-
        C*(w.q t*σ.seminorm (u : Lp ℝ 2 (volume.restrict S)))^2 ≤
          (boundedDirichletOriginalForm hS hd hb).scalarForm u
            (conformingWeight σ hp (conformingWeight σ hp u)) := by
  obtain ⟨C,hC,hbound⟩ := allowed_weak_form_lower_uniform hS hb ρ hρ
  refine ⟨C,hC,?_⟩
  intro w τ t η hη
  dsimp only
  intro u
  let σ := (ρ.scaled η).multiplier w τ t
  let hp := fun v : dirichletSubspace S => allowed_weight_mem_dirichlet hS hb ρ hρ w τ t η hη v v.property
  let J := domainSobolevJet hS (ae_restrict_mem hS.measurableSet) (dirichletSubspace_sobolev S)
  have hv : WeakSobolevJet.value (J (conformingWeight σ hp u))=σ.map (WeakSobolevJet.value (J u)) := by
    simp only [J,domainSobolevJet_value]
    rfl
  have hz : WeakSobolevJet.value (J (conformingWeight σ hp (conformingWeight σ hp u)))=
      σ.map (WeakSobolevJet.value (J (conformingWeight σ hp u))) := by
    simp only [J,domainSobolevJet_value]
    rfl
  have hh := hbound w τ t η hη (J u) (J (conformingWeight σ hp u))
    (J (conformingWeight σ hp (conformingWeight σ hp u))) hv hz
  rw [dirichlet_scalarForm_canonical]
  simpa only [J,domainSobolevJet_value,conformingWeightedNorm] using hh

set_option maxHeartbeats 800000 in
theorem dirichlet_allowed_form_upper (hS : IsOpen S) (hd : 0 < d)
    (hb : Bornology.IsBounded S) (ρ : SpatialProfile (volume.restrict S))
    (w : TimeWeight) (τ t η : ℝ) (u v : dirichletSubspace S) :
    |(boundedDirichletOriginalForm hS hd hb).scalarForm u v| ≤
      conformingWeightedNorm hS (ae_restrict_mem hS.measurableSet) (dirichletSubspace_sobolev S)
        (w.q t) ((ρ.scaled η).multiplier w τ t) u*
      conformingWeightedNorm hS (ae_restrict_mem hS.measurableSet) (dirichletSubspace_sobolev S)
        (w.q t) ((ρ.scaled (-η)).multiplier w (-τ) t) v := by
  have hinv : ∀ᵐ x ∂volume.restrict S,
      ((ρ.scaled η).multiplier w τ t).value x*((ρ.scaled (-η)).multiplier w (-τ) t).value x=1 := by
    apply Filter.Eventually.of_forall
    intro x
    change (w.q t^τ*Real.exp ((η*ρ.value x)*w.q t))*
      (w.q t^(-τ)*Real.exp (((-η)*ρ.value x)*w.q t))=1
    have he : (-η)*ρ.value x*w.q t=-(η*ρ.value x*w.q t) := by ring
    rw [he,Real.exp_neg,Real.rpow_neg (w.nonneg t)]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos (w.pos t) τ)]
  rw [dirichlet_scalarForm_canonical]
  exact weakGradientPairing_weighted_upper _ _ hinv (w.nonneg t) _ _

end Carleman
