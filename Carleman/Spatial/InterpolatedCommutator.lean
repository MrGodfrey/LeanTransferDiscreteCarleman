module

public import Carleman.Spatial.DomainParameterInterpolation
public import Carleman.Spatial.SecondOrderCommutatorEnergy

/-! General-order actual spatial commutator absorption, with the remaining
original-domain parameter interpolation input explicit. A1 is only used forward;
no derivative is assumed to preserve the operator domain. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {D : Submodule ℝ (Lp ℝ 2 ν)} (hD : D ≤ sobolevSubspace d n ν S)
  (A : D →ₗ[ℝ] Lp ℝ 2 ν)

/-- H is structural and precedes q, both weights, μ and every D(A) state.
The only unproved geometric input is explicitly `DomainParameterInterpolation`. -/
theorem interpolated_commutator_small_shift (Cinterp Creg Ccomm η : ℝ)
    (hCi : 1 ≤ Cinterp) (hCcomm : 0 ≤ Ccomm) (hη : 0 < η)
    (hI : DomainParameterInterpolation hS hν hD Cinterp)
    (hell : ∀ v : D, ‖domainSobolevJet hS hν hD v‖ ≤ Creg*‖A v‖) :
    ∃ H : ℝ, 1 ≤ H ∧ ∀ q μ : ℝ, 1 ≤ q → H*q^n ≤ μ →
      ∀ (σ ξ : BoundedMultiplier ν)
        (hw : ∀ u : D, σ.map (u : Lp ℝ 2 ν) ∈ D)
        (hξ : ∀ u : D, ξ.map (u : Lp ℝ 2 ν) ∈ D),
      (∀ᵐ x ∂ν, σ.value x*ξ.value x=1) →
      (∀ v : D, ‖conjugatedCommutator A σ ξ hw hξ v‖ ≤
        Ccomm*∑ k : Fin n, q^(n-k.val)*
          ‖WeakSobolevJet.field k.castSucc (domainSobolevJet hS hν hD v)‖) →
      ∀ u : D, ‖conjugatedCommutator A σ ξ hw hξ (conformingWeight σ hw u)‖ ≤
        η*(‖σ.map (A u)‖+‖μ • σ.map (u : Lp ℝ 2 ν)‖) := by
  let B := max 0 Creg
  let K := Ccomm*Cinterp
  let r := max 1 (max (2*K*B) (2*K*B/η))
  have hr : 1 ≤ r := le_max_left _ _
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hB : 0 ≤ B := le_max_left _ _
  have hK : 0 ≤ K := mul_nonneg hCcomm (zero_le_one.trans hCi)
  have h₁ : 2*K*B ≤ r := (le_max_left _ _).trans (le_max_right _ _)
  have h₂ : 2*K*B ≤ r*η :=
    (div_le_iff₀ hη).mp ((le_max_right _ _).trans (le_max_right _ _))
  let H := max 1 (2*K*r^n/(r*η))
  refine ⟨H,le_max_left _ _,?_⟩
  intro q μ hq hμ σ ξ hw hξ hinv hA2 u
  let v := conformingWeight σ hw u
  let R := ‖conjugatedCommutator A σ ξ hw hξ v‖
  let X := ‖σ.map (A u)‖
  let U := ‖σ.map (u : Lp ℝ 2 ν)‖
  let Y := ‖μ • σ.map (u : Lp ℝ 2 ν)‖
  have hμ0 : 0 ≤ μ := (mul_nonneg (by dsimp [H]; positivity)
    (pow_nonneg (zero_le_one.trans hq) n)).trans hμ
  have hY : Y = μ*U := by dsimp [Y,U]; rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hμ0]
  have hR0 : 0 ≤ R := norm_nonneg _
  have hX0 : 0 ≤ X := norm_nonneg _
  have hU0 : 0 ≤ U := norm_nonneg _
  have hA : ‖A v‖ ≤ X+R := by
    have ht := norm_add_le (A v-σ.map (A u)) (σ.map (A u))
    rw [sub_add_cancel] at ht
    have he := congrArg norm (conjugatedCommutator_weighted_eq A σ ξ hw hξ hinv u)
    change R = ‖A v-σ.map (A u)‖ at he
    rw [← he] at ht
    linarith
  have hjet : ‖domainSobolevJet hS hν hD v‖ ≤ B*(X+R) :=
    ((hell v).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))).trans
      (mul_le_mul_of_nonneg_left hA hB)
  have hlow := WeakSobolevJet.lower_parameterNorm_le (zero_le_one.trans hq) hr
    BoundedMultiplier.one (domainSobolevJet hS hν hD v)
  simp only [BoundedMultiplier.one_seminorm] at hlow
  have hi := hI (r*q) (one_le_mul_of_one_le_of_one_le hr hq) v
  have hrough : r*R ≤ K*(B*(X+R)+r^n*q^n*U) := by
    have hprod := mul_le_mul_of_nonneg_left (hA2 v) hr0.le
    change r*R ≤ r*(Ccomm*_) at hprod
    have hp := mul_le_mul_of_nonneg_left hlow hCcomm
    have hi' := mul_le_mul_of_nonneg_left hi hCcomm
    change Ccomm*WeakSobolevJet.parameterNorm (r*q) BoundedMultiplier.one
      (domainSobolevJet hS hν hD v) ≤ Ccomm*(Cinterp*(‖domainSobolevJet hS hν hD v‖+(r*q)^n*U)) at hi'
    calc
      r*R ≤ _ := hprod
      _ = Ccomm*(r*_) := by ring
      _ ≤ _ := hp
      _ ≤ Ccomm*(Cinterp*(‖domainSobolevJet hS hν hD v‖+(r*q)^n*U)) := hi'
      _ = K*(‖domainSobolevJet hS hν hD v‖+r^n*q^n*U) := by rw [mul_pow]; dsimp [K]; ring
      _ ≤ K*(B*(X+R)+r^n*q^n*U) := mul_le_mul_of_nonneg_left (add_le_add hjet le_rfl) hK
  have hH : 2*K*r^n ≤ r*η*H := by
    have hh := (div_le_iff₀ (mul_pos hr0 hη)).mp (le_max_right 1 (2*K*r^n/(r*η)))
    nlinarith only [hh]
  have hcoef : 2*K*r^n*q^n ≤ r*η*μ := by
    have ha := mul_le_mul_of_nonneg_right hH (pow_nonneg (zero_le_one.trans hq) n)
    have hb := mul_le_mul_of_nonneg_left hμ (mul_nonneg hr0.le hη.le)
    nlinarith only [ha,hb]
  have hterm := mul_le_mul_of_nonneg_right hcoef hU0
  have htermX := mul_le_mul_of_nonneg_right h₂ hX0
  have htermR := mul_le_mul_of_nonneg_right h₁ hR0
  change R ≤ η*(X+Y)
  rw [hY]
  nlinarith only [hrough,hterm,htermX,htermR,hr0]
end Carleman
