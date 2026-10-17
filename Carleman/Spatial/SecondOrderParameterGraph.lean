module

public import Carleman.Spatial.SecondOrderCommutatorEnergy
public import Carleman.Spatial.EnergyLowOrderAbsorption

/-! Full R₂ control from forward A1, A2 and A3 on D(A). No extension of
arbitrary Sobolev functions and no reverse A1 estimate is required. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {V D : Submodule ℝ (Lp ℝ 2 ν)}
  (hV : V ≤ sobolevSubspace d 1 ν S) (hDV : D ≤ V)
  (hD : D ≤ sobolevSubspace d 2 ν S)
  (a : V → V → ℝ) (A : D →ₗ[ℝ] Lp ℝ 2 ν)
  (htest : ∀ u : D, ∀ v : V, a (D.inclusion hDV u) v = inner ℝ (A u) (v : Lp ℝ 2 ν))

include htest
theorem secondOrder_parameter_graph_uniform (hbounded : Bornology.IsBounded S)
    (ρ : SpatialProfile ν) (hρ : SmoothOnClosure ρ.value S)
    (c C Ccomm Creg : ℝ) (hc : 0 < c) (hCcomm : 0 ≤ Ccomm)
    (hell : ∀ v : D, ‖domainSobolevJet hS hν hD v‖ ≤ Creg*‖A v‖) :
    ∃ H K : ℝ, 1 ≤ H ∧ 0 < K ∧ ∀ (w : TimeWeight) (τ t μ : ℝ), H*w.q t^2 ≤ μ →
      ∀ (hwV : ∀ v : V, (ρ.multiplier w τ t).map (v : Lp ℝ 2 ν) ∈ V)
        (hw : ∀ u : D, (ρ.multiplier w τ t).map (u : Lp ℝ 2 ν) ∈ D)
        (hξ : ∀ u : D, (ρ.neg.multiplier w (-τ) t).map (u : Lp ℝ 2 ν) ∈ D),
      (∀ v : V, c*(conformingWeightedNorm hS hν hV (w.q t) (ρ.multiplier w τ t) v)^2 -
        C*(w.q t*(ρ.multiplier w τ t).seminorm (v : Lp ℝ 2 ν))^2 ≤
          a v (conformingWeight (ρ.multiplier w τ t) hwV
            (conformingWeight (ρ.multiplier w τ t) hwV v))) →
      (∀ v : D, ‖conjugatedCommutator A (ρ.multiplier w τ t) (ρ.neg.multiplier w (-τ) t) hw hξ v‖ ≤
        Ccomm*∑ k : Fin 2, w.q t^(2-k.val)*
          ‖WeakSobolevJet.field k.castSucc (domainSobolevJet hS hν hD v)‖) →
      ∀ u : D, conformingParameterNorm hS hν hD (w.q t) (ρ.multiplier w τ t) u ≤
        K*(‖(ρ.multiplier w τ t).map (A u)‖ +
          ‖μ • (ρ.multiplier w τ t).map (u : Lp ℝ 2 ν)‖) := by
  obtain ⟨H₁,hH₁,hlow⟩ := weighted_lowOrder_absorption hS hν hV hDV a A htest
    (by decide : 0 < 1) c C 1 hc zero_lt_one
  obtain ⟨H₂,hH₂,hcomm⟩ := secondOrder_commutator_small_shift hS hν hV hDV hD a A htest
    hbounded ρ hρ c C Ccomm 1 hc hCcomm zero_lt_one
  obtain ⟨J₁,hJ₁,hconj₁⟩ := closure_conforming_conjugation_uniform hS hbounded hν hV ρ hρ
  obtain ⟨J₂,hJ₂,hconj₂⟩ := closure_conforming_conjugation_uniform hS hbounded hν hD ρ hρ
  let B := max 0 Creg
  let K := J₂*(2*J₁+2*B)
  refine ⟨max H₁ H₂,K,hH₁.trans (le_max_left _ _),by dsimp [K,B]; positivity,?_⟩
  intro w τ t μ hμ hwV hw hξ ha hA2 u
  let σ := ρ.multiplier w τ t
  let v := conformingWeight σ hw u
  let X := ‖σ.map (A u)‖
  let Y := ‖μ • σ.map (u : Lp ℝ 2 ν)‖
  have h₁ : H₁*w.q t^2 ≤ μ :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)).trans hμ
  have h₂ : H₂*w.q t^2 ≤ μ :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)).trans hμ
  have hN := (hlow (w.q t) μ (w.lower t) h₁ σ hwV (by simpa only [pow_one] using ha) u).1
  simp only [pow_one,one_mul] at hN
  have hcomm' := hcomm w τ t μ h₂ hwV hw hξ ha hA2 u
  rw [conjugatedCommutator_weighted_eq A _ _ hw hξ
    (Filter.Eventually.of_forall (ρ.multiplier_inverse w τ t)),one_mul] at hcomm'
  have hA : ‖A v‖ ≤ 2*(X+Y) := by
    have ht := norm_add_le (A v-σ.map (A u)) (σ.map (A u))
    rw [sub_add_cancel] at ht
    have hy : 0 ≤ Y := norm_nonneg _
    change ‖A v-σ.map (A u)‖ ≤ X+Y at hcomm'
    change ‖A v‖ ≤ ‖A v-σ.map (A u)‖+X at ht
    linarith
  have hv : D.inclusion hDV v = conformingWeight σ hwV (D.inclusion hDV u) := by
    apply Subtype.ext
    rfl
  have hn := (hconj₁ w τ t false hwV (D.inclusion hDV u)).2.2.1
  change conformingWeightedNorm hS hν hV (w.q t) BoundedMultiplier.one
    (conformingWeight σ hwV (D.inclusion hDV u)) ≤
      J₁*conformingWeightedNorm hS hν hV (w.q t) σ (D.inclusion hDV u) at hn
  have hlo := secondOrder_lower_sum_le hS hν hV hDV hD (w.nonneg t) v
  rw [hv] at hlo
  have hlower : (∑ k : Fin 2, w.q t^(2-k.val)*
      ‖WeakSobolevJet.field k.castSucc (domainSobolevJet hS hν hD v)‖) ≤ 2*J₁*(X+Y) := by
    have hp := mul_le_mul_of_nonneg_left hn (show 0 ≤ 2*w.q t by positivity [w.pos t])
    have hp' := mul_le_mul_of_nonneg_left hN (show 0 ≤ 2*J₁ by positivity)
    change _ ≤ 2*J₁*(X+Y) at hp'
    nlinarith only [hlo,hp,hp']
  have htop : ‖WeakSobolevJet.field (Fin.last 2) (domainSobolevJet hS hν hD v)‖ ≤ 2*B*(X+Y) := by
    calc
      _ ≤ ‖domainSobolevJet hS hν hD v‖ := WeakSobolevJet.norm_field_le _ _
      _ ≤ Creg*‖A v‖ := hell v
      _ ≤ B*‖A v‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
      _ ≤ B*(2*(X+Y)) := mul_le_mul_of_nonneg_left hA (le_max_left _ _)
      _ = 2*B*(X+Y) := by ring
  have hR : conformingParameterNorm hS hν hD (w.q t) BoundedMultiplier.one v ≤ (2*J₁+2*B)*(X+Y) := by
    unfold conformingParameterNorm WeakSobolevJet.parameterNorm
    simp only [BoundedMultiplier.one_seminorm]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_last,Fin.val_castSucc,Nat.sub_self,pow_zero,one_mul]
    nlinarith only [hlower,htop]
  calc
    _ ≤ J₂*conformingParameterNorm hS hν hD (w.q t) BoundedMultiplier.one v :=
      (hconj₂ w τ t false hw u).2.1
    _ ≤ J₂*((2*J₁+2*B)*(X+Y)) := mul_le_mul_of_nonneg_left hR hJ₂.le
    _ = K*(X+Y) := by dsimp [K]; ring
end Carleman
