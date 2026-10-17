module

public import Carleman.Spatial.LowerShiftEnergy
public import Carleman.Spatial.SobolevTruncation
public import Carleman.Weights.ClosureConforming
public import Carleman.Weights.SpacetimeCommutator

/-! For second-order operators, all original A2 commutator orders are within
the A3 energy range. This proves their smallness on actual operator-domain
states without an arbitrary-domain Sobolev extension or reverse elliptic bound.
The higher-order commutator gap is not discharged by this special case. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {V D : Submodule ℝ (Lp ℝ 2 ν)}
  (hV : V ≤ sobolevSubspace d 1 ν S) (hDV : D ≤ V)
  (hD : D ≤ sobolevSubspace d 2 ν S)

theorem secondOrder_lower_sum_le {q : ℝ} (hq : 0 ≤ q) (v : D) :
    (∑ k : Fin 2, q^(2-k.val)*‖WeakSobolevJet.field k.castSucc (domainSobolevJet hS hν hD v)‖) ≤
      2*q*conformingWeightedNorm hS hν hV q BoundedMultiplier.one (D.inclusion hDV v) := by
  let J := domainSobolevJet hS hν hD v
  let K := domainSobolevJet hS hν hV (D.inclusion hDV v)
  have he : K = WeakSobolevJet.truncate (by decide : 1 ≤ 2) J := by
    apply WeakSobolevJet.value_injective hS hν
    simp only [K,J,WeakSobolevJet.truncate_value,domainSobolevJet_value,Submodule.coe_inclusion]
  have h0 := WeakSobolevJet.weighted_component_le hq BoundedMultiplier.one K (0 : Fin 2)
  have h1 := WeakSobolevJet.weighted_component_le hq BoundedMultiplier.one K (1 : Fin 2)
  simp only [BoundedMultiplier.one_seminorm] at h0 h1
  have hf0 : WeakSobolevJet.field (0 : Fin 2) K = WeakSobolevJet.field (0 : Fin 3) J := by rw [he]; rfl
  have hf1 : WeakSobolevJet.field (1 : Fin 2) K = WeakSobolevJet.field (1 : Fin 3) J := by rw [he]; rfl
  rw [hf0] at h0
  rw [hf1] at h1
  norm_num only [Fin.val_zero,Fin.val_one,Nat.sub_zero,Nat.sub_self,pow_one,pow_zero,one_mul] at h0 h1
  change (∑ k : Fin 2, q^(2-k.val)*‖WeakSobolevJet.field k.castSucc J‖) ≤
    2*q*WeakSobolevJet.weightedNorm q BoundedMultiplier.one K
  rw [Fin.sum_univ_two]
  norm_num only [Fin.val_zero,Fin.val_one,Nat.sub_zero,Nat.reduceSub,pow_one]
  change q^2*‖WeakSobolevJet.field (0 : Fin 3) J‖ +
    q*‖WeakSobolevJet.field (1 : Fin 3) J‖ ≤ 2*q*WeakSobolevJet.weightedNorm q BoundedMultiplier.one K
  nlinarith [mul_le_mul_of_nonneg_left h0 hq,mul_le_mul_of_nonneg_left h1 hq]

variable (a : V → V → ℝ) (A : D →ₗ[ℝ] Lp ℝ 2 ν)
  (htest : ∀ u : D, ∀ v : V, a (D.inclusion hDV u) v = inner ℝ (A u) (v : Lp ℝ 2 ν))

omit [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν] in
theorem conjugatedCommutator_weighted_eq (σ ξ : BoundedMultiplier ν)
    (hw : ∀ u : D, σ.map (u : Lp ℝ 2 ν) ∈ D)
    (hξ : ∀ u : D, ξ.map (u : Lp ℝ 2 ν) ∈ D)
    (hinv : ∀ᵐ x ∂ν, σ.value x*ξ.value x=1) (u : D) :
    conjugatedCommutator A σ ξ hw hξ (conformingWeight σ hw u) =
      A (conformingWeight σ hw u) - σ.map (A u) := by
  rw [conjugatedCommutator_eq A σ ξ hw hξ hinv]
  have he : conformingWeight ξ hξ (conformingWeight σ hw u) = u := by
    apply Subtype.ext
    exact ξ.map_inverse σ (hinv.mono fun x hx => by rwa [mul_comm]) _
  rw [he]

include htest
/-- The threshold is structural and precedes the weight/time/exponent/state.
Only original A2/A3 hypotheses enter; the full commutator is the real D(A)
expression, and the small right side consists of the weighted A and shift. -/
theorem secondOrder_commutator_small_shift (hbounded : Bornology.IsBounded S)
    (ρ : SpatialProfile ν) (hρ : SmoothOnClosure ρ.value S)
    (c C Ccomm η : ℝ) (hc : 0 < c) (hCcomm : 0 ≤ Ccomm) (hη : 0 < η) :
    ∃ H : ℝ, 1 ≤ H ∧ ∀ (w : TimeWeight) (τ t μ : ℝ), H*w.q t^2 ≤ μ →
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
      ∀ u : D,
      ‖conjugatedCommutator A (ρ.multiplier w τ t) (ρ.neg.multiplier w (-τ) t) hw hξ
        (conformingWeight (ρ.multiplier w τ t) hw u)‖ ≤
        η*(‖(ρ.multiplier w τ t).map (A u)‖ +
          ‖μ • (ρ.multiplier w τ t).map (u : Lp ℝ 2 ν)‖) := by
  obtain ⟨J,hJ,hconj⟩ := closure_conforming_conjugation_uniform hS hbounded hν hV ρ hρ
  let K := 2*Ccomm*J
  let H := max 1 (max C (K^2/(c*η^2)))
  refine ⟨H,le_max_left _ _,?_⟩
  intro w τ t μ hμ hwV hw hξ ha hA2 u
  let σ := ρ.multiplier w τ t
  let v := conformingWeight σ hw u
  let N := conformingWeightedNorm hS hν hV (w.q t) σ (D.inclusion hDV u)
  let R := ‖conjugatedCommutator A σ (ρ.neg.multiplier w (-τ) t) hw hξ v‖
  let X := ‖σ.map (A u)‖
  let Y := ‖μ • σ.map (u : Lp ℝ 2 ν)‖
  have hq := w.pos t
  have hμ0 : 0 ≤ μ := (by positivity : 0 ≤ H*w.q t^2).trans hμ
  have hHC : C ≤ H := (le_max_left _ _).trans (le_max_right _ _)
  have hHK : K^2 ≤ c*η^2*H := by
    have hd : 0 < c*η^2 := by positivity
    have hz := (div_le_iff₀ hd).mp ((le_max_right C (K^2/(c*η^2))).trans (le_max_right 1 _))
    nlinarith only [hz]
  have hN0 : 0 ≤ N := WeakSobolevJet.weightedNorm_nonneg _ _ _
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hv : D.inclusion hDV v = conformingWeight σ hwV (D.inclusion hDV u) := by
    apply Subtype.ext
    rfl
  have hconv := (hconj w τ t false hwV (D.inclusion hDV u)).2.2.1
  change conformingWeightedNorm hS hν hV (w.q t) BoundedMultiplier.one
    (conformingWeight σ hwV (D.inclusion hDV u)) ≤ J*N at hconv
  have hR : R ≤ K*w.q t*N := by
    have hlo := secondOrder_lower_sum_le hS hν hV hDV hD hq.le v
    rw [hv] at hlo
    have h₁ := mul_le_mul_of_nonneg_left hlo hCcomm
    have h₂ := mul_le_mul_of_nonneg_left hconv (show 0 ≤ Ccomm*(2*w.q t) by positivity)
    dsimp [K,R]
    nlinarith [hA2 v]
  have henergy := shiftedOperator_weighted_energy_of_lower hS hν hV hDV a A htest
    (by decide : 0 < 1) (w.lower t)
    ((mul_le_mul_of_nonneg_right hHC (sq_nonneg (w.q t))).trans hμ) σ hwV
    (by simpa only [pow_one] using ha) u
  change c*N^2 ≤ σ.seminorm (A u + μ • (u : Lp ℝ 2 ν))*σ.seminorm (u : Lp ℝ 2 ν) at henergy
  have hf : σ.seminorm (A u + μ • (u : Lp ℝ 2 ν)) ≤ X+Y := by
    change ‖σ.map (_ + _)‖ ≤ X+Y
    rw [BoundedMultiplier.map_add,BoundedMultiplier.map_smul]
    exact norm_add_le _ _
  have henergy' : c*N^2 ≤ (X+Y)*‖σ.map (u : Lp ℝ 2 ν)‖ :=
    henergy.trans (mul_le_mul_of_nonneg_right hf (apply_nonneg σ.seminorm _))
  have hY : Y = μ*‖σ.map (u : Lp ℝ 2 ν)‖ := by
    dsimp [Y]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hμ0]
  have hRY : c*R^2 ≤ c*η^2*(X+Y)*Y := by
    have hsq : R^2 ≤ (K*w.q t*N)^2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hR
    have h₁ := mul_le_mul_of_nonneg_left hsq hc.le
    have h₂ := mul_le_mul_of_nonneg_left henergy' (sq_nonneg (K*w.q t))
    have h₃ := mul_le_mul_of_nonneg_right hHK (sq_nonneg (w.q t))
    have h₄ := mul_le_mul_of_nonneg_left hμ (show 0 ≤ c*η^2 by positivity)
    have hcoef : K^2*w.q t^2 ≤ c*η^2*μ := by nlinarith only [h₃,h₄]
    have h₅ := mul_le_mul_of_nonneg_right hcoef
      (show 0 ≤ (X+Y)*‖σ.map (u : Lp ℝ 2 ν)‖ by dsimp [X,Y]; positivity)
    calc
      c*R^2 ≤ c*(K*w.q t*N)^2 := h₁
      _ = (K*w.q t)^2*(c*N^2) := by ring
      _ ≤ (K*w.q t)^2*((X+Y)*‖σ.map (u : Lp ℝ 2 ν)‖) := h₂
      _ = K^2*w.q t^2*((X+Y)*‖σ.map (u : Lp ℝ 2 ν)‖) := by ring
      _ ≤ c*η^2*μ*((X+Y)*‖σ.map (u : Lp ℝ 2 ν)‖) := h₅
      _ = c*η^2*(X+Y)*Y := by rw [hY]; ring
  change R ≤ η*(X+Y)
  have hX : 0 ≤ X := norm_nonneg _
  have hY0 : 0 ≤ Y := norm_nonneg _
  have hlast := mul_le_mul_of_nonneg_left (show (X+Y)*Y ≤ (X+Y)^2 by nlinarith)
    (show 0 ≤ c*η^2 by positivity)
  have hsq : R^2 ≤ (η*(X+Y))^2 := by nlinarith only [hRY,hlast,hc]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq
end Carleman
