module

public import Carleman.Spatial.InterpolatedCommutator

/-! Actual full R_n norm from forward A1 and A2, with the remaining
original-domain interpolation input explicit. No reverse elliptic estimate. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {D : Submodule ℝ (Lp ℝ 2 ν)} (hD : D ≤ sobolevSubspace d n ν S)
  (A : D →ₗ[ℝ] Lp ℝ 2 ν)

theorem interpolated_parameter_graph_uniform (hbounded : Bornology.IsBounded S)
    (ρ : SpatialProfile ν) (hρ : SmoothOnClosure ρ.value S)
    (Cinterp Creg Ccomm : ℝ) (hCi : 1 ≤ Cinterp) (hCcomm : 0 ≤ Ccomm)
    (hI : DomainParameterInterpolation hS hν hD Cinterp)
    (hell : ∀ v : D, ‖domainSobolevJet hS hν hD v‖ ≤ Creg*‖A v‖) :
    ∃ H K : ℝ, 1 ≤ H ∧ 0 < K ∧ ∀ (w : TimeWeight) (τ t μ : ℝ), H*w.q t^n ≤ μ →
      ∀ (hw : ∀ u : D, (ρ.multiplier w τ t).map (u : Lp ℝ 2 ν) ∈ D)
        (hξ : ∀ u : D, (ρ.neg.multiplier w (-τ) t).map (u : Lp ℝ 2 ν) ∈ D),
      (∀ v : D, ‖conjugatedCommutator A (ρ.multiplier w τ t) (ρ.neg.multiplier w (-τ) t) hw hξ v‖ ≤
        Ccomm*∑ k : Fin n, w.q t^(n-k.val)*
          ‖WeakSobolevJet.field k.castSucc (domainSobolevJet hS hν hD v)‖) →
      ∀ u : D, conformingParameterNorm hS hν hD (w.q t) (ρ.multiplier w τ t) u ≤
        K*(‖(ρ.multiplier w τ t).map (A u)‖ +
          ‖μ • (ρ.multiplier w τ t).map (u : Lp ℝ 2 ν)‖) := by
  obtain ⟨H,hH,hcomm⟩ := interpolated_commutator_small_shift hS hν hD A
    Cinterp Creg Ccomm 1 hCi hCcomm zero_lt_one hI hell
  obtain ⟨J,hJ,hconj⟩ := closure_conforming_conjugation_uniform hS hbounded hν hD ρ hρ
  let B := max 0 Creg
  let K := J*Cinterp*(2*B+1)
  refine ⟨H,K,hH,by dsimp [K,B]; positivity,?_⟩
  intro w τ t μ hμ hw hξ hA2 u
  let σ := ρ.multiplier w τ t
  let v := conformingWeight σ hw u
  let X := ‖σ.map (A u)‖
  let Y := ‖μ • σ.map (u : Lp ℝ 2 ν)‖
  have hqμ : w.q t^n ≤ μ :=
    (le_mul_of_one_le_left (pow_nonneg (w.nonneg t) n) hH).trans hμ
  have hμ0 : 0 ≤ μ := (pow_nonneg (w.nonneg t) n).trans hqμ
  have hinv : ∀ᵐ x ∂ν, (ρ.multiplier w τ t).value x*(ρ.neg.multiplier w (-τ) t).value x=1 :=
    Filter.Eventually.of_forall (ρ.multiplier_inverse w τ t)
  have hsmall := hcomm (w.q t) μ (w.lower t) hμ _ _ hw hξ hinv hA2 u
  rw [conjugatedCommutator_weighted_eq A _ _ hw hξ hinv,one_mul] at hsmall
  have hA : ‖A v‖ ≤ 2*(X+Y) := by
    have ht := norm_add_le (A v-σ.map (A u)) (σ.map (A u))
    rw [sub_add_cancel] at ht
    change ‖A v-σ.map (A u)‖ ≤ X+Y at hsmall
    change ‖A v‖ ≤ ‖A v-σ.map (A u)‖+X at ht
    linarith [norm_nonneg (μ • σ.map (u : Lp ℝ 2 ν))]
  have hjet : ‖domainSobolevJet hS hν hD v‖ ≤ 2*B*(X+Y) := by
    calc
      _ ≤ Creg*‖A v‖ := hell v
      _ ≤ B*‖A v‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
      _ ≤ B*(2*(X+Y)) := mul_le_mul_of_nonneg_left hA (le_max_left _ _)
      _ = 2*B*(X+Y) := by ring
  have hzero : w.q t^n*‖(v : Lp ℝ 2 ν)‖ ≤ Y := by
    dsimp [Y,v,conformingWeight]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hμ0]
    exact mul_le_mul_of_nonneg_right hqμ (norm_nonneg _)
  have hR : conformingParameterNorm hS hν hD (w.q t) BoundedMultiplier.one v ≤
      Cinterp*((2*B+1)*(X+Y)) := by
    apply (hI (w.q t) (w.lower t) v).trans
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hCi)
    nlinarith only [hjet,hzero,norm_nonneg (σ.map (A u))]
  calc
    _ ≤ J*conformingParameterNorm hS hν hD (w.q t) BoundedMultiplier.one v :=
      (hconj w τ t false hw u).2.1
    _ ≤ J*(Cinterp*((2*B+1)*(X+Y))) := mul_le_mul_of_nonneg_left hR hJ.le
    _ = K*(X+Y) := by dsimp [K]; ring
end Carleman
