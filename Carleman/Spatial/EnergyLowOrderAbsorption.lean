module

public import Carleman.Spatial.LowerShiftEnergy
public import Carleman.Spatial.ParameterConjugation
public import Carleman.Weights.ConformingConjugation

/-! A3 absorbs the actual lower half of the spatial parameter graph for every
order. Derivatives above m are not included and are not claimed controlled. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {V D : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d m ν S) (hDV : D ≤ V)
  (a : V → V → ℝ) (A : D →ₗ[ℝ] Lp ℝ 2 ν)
  (htest : ∀ u : D, ∀ v : V, a (D.inclusion hDV u) v = inner ℝ (A u) (v : Lp ℝ 2 ν))

include htest
theorem weighted_lowOrder_absorption (hm : 0 < m) (c C η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ H : ℝ, 1 ≤ H ∧ ∀ q μ : ℝ, 1 ≤ q → H*q^(2*m) ≤ μ →
      ∀ (σ : BoundedMultiplier ν) (hw : ∀ v : V, σ.map (v : Lp ℝ 2 ν) ∈ V),
      (∀ v : V, c*(conformingWeightedNorm hS hν hV q σ v)^2 -
        C*(q^m*σ.seminorm (v : Lp ℝ 2 ν))^2 ≤
          a v (conformingWeight σ hw (conformingWeight σ hw v))) →
      ∀ u : D,
      q^m*conformingWeightedNorm hS hν hV q σ (D.inclusion hDV u) ≤
        η*(‖σ.map (A u)‖+‖μ • σ.map (u : Lp ℝ 2 ν)‖) ∧
      q^m*conformingParameterNorm hS hν hV q σ (D.inclusion hDV u) ≤
        (m+1:ℝ)*η*(‖σ.map (A u)‖+‖μ • σ.map (u : Lp ℝ 2 ν)‖) := by
  let H := max 1 (max C (1/(c*η^2)))
  refine ⟨H,le_max_left _ _,?_⟩
  intro q μ hq hμ σ hw ha u
  let N := conformingWeightedNorm hS hν hV q σ (D.inclusion hDV u)
  let X := ‖σ.map (A u)‖
  let Y := ‖μ • σ.map (u : Lp ℝ 2 ν)‖
  have hHC : C ≤ H := (le_max_left _ _).trans (le_max_right _ _)
  have hμ0 : 0 ≤ μ := (by positivity : 0 ≤ H*q^(2*m)).trans hμ
  have hHK : 1 ≤ c*η^2*H := by
    have hd : 0 < c*η^2 := by positivity
    have he := (div_le_iff₀ hd).mp ((le_max_right C (1/(c*η^2))).trans (le_max_right 1 _))
    nlinarith only [he]
  have he := shiftedOperator_weighted_energy_of_lower hS hν hV hDV a A htest hm hq
    ((mul_le_mul_of_nonneg_right hHC (pow_nonneg (zero_le_one.trans hq) _)).trans hμ) σ hw ha u
  have hf : σ.seminorm (A u+μ • (u : Lp ℝ 2 ν)) ≤ X+Y := by
    change ‖σ.map (_+_)‖ ≤ _
    rw [BoundedMultiplier.map_add,BoundedMultiplier.map_smul]
    exact norm_add_le _ _
  have he' : c*N^2 ≤ (X+Y)*‖σ.map (u : Lp ℝ 2 ν)‖ :=
    he.trans (mul_le_mul_of_nonneg_right hf (apply_nonneg σ.seminorm _))
  have hcoef : q^(2*m) ≤ c*η^2*μ := by
    have h₁ := mul_le_mul_of_nonneg_right hHK (pow_nonneg (zero_le_one.trans hq) (2*m))
    have h₂ := mul_le_mul_of_nonneg_left hμ (show 0 ≤ c*η^2 by positivity)
    nlinarith only [h₁,h₂]
  have hY : Y = μ*‖σ.map (u : Lp ℝ 2 ν)‖ := by
    dsimp [Y]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hμ0]
  have hsq : c*(q^m*N)^2 ≤ c*(η*(X+Y))^2 := by
    have h₁ := mul_le_mul_of_nonneg_left he' (pow_nonneg (zero_le_one.trans hq) (2*m))
    have h₂ := mul_le_mul_of_nonneg_right hcoef
      (show 0 ≤ (X+Y)*‖σ.map (u : Lp ℝ 2 ν)‖ by dsimp [X,Y]; positivity)
    have hp : (q^m)^2 = q^(2*m) := by rw [← pow_mul]; congr 1; omega
    calc
      c*(q^m*N)^2 = q^(2*m)*(c*N^2) := by rw [mul_pow,hp]; ring
      _ ≤ q^(2*m)*((X+Y)*‖σ.map (u : Lp ℝ 2 ν)‖) := h₁
      _ ≤ c*η^2*μ*((X+Y)*‖σ.map (u : Lp ℝ 2 ν)‖) := h₂
      _ = c*η^2*(X+Y)*Y := by rw [hY]; ring
      _ ≤ c*(η*(X+Y))^2 := by
        have hX : 0 ≤ X := norm_nonneg _
        have hY0 : 0 ≤ Y := norm_nonneg _
        nlinarith [mul_nonneg (show 0 ≤ c*η^2*(X+Y) by positivity) hX]
  have hN0 : 0 ≤ N := WeakSobolevJet.weightedNorm_nonneg _ _ _
  have hsmall : q^m*N ≤ η*(X+Y) :=
    (sq_le_sq₀ (mul_nonneg (pow_nonneg (zero_le_one.trans hq) m) hN0)
      (by dsimp [X,Y]; positivity)).mp ((mul_le_mul_iff_right₀ hc).mp hsq)
  refine ⟨hsmall,?_⟩
  have hp := mul_le_mul_of_nonneg_left (WeakSobolevJet.parameterNorm_le_weightedNorm
    (zero_le_one.trans hq) σ (domainSobolevJet hS hν hV (D.inclusion hDV u)))
    (pow_nonneg (zero_le_one.trans hq) m)
  have hm' := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ (m+1:ℝ) by positivity)
  change q^m*conformingParameterNorm hS hν hV q σ (D.inclusion hDV u) ≤ (m+1:ℝ)*η*(X+Y)
  change q^m*conformingParameterNorm hS hν hV q σ (D.inclusion hDV u) ≤ q^m*((m+1:ℝ)*N) at hp
  nlinarith only [hp,hm']
end Carleman
