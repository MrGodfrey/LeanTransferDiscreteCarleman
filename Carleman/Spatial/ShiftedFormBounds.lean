module

public import Carleman.Spatial.WeightedSobolevNorm
public import Carleman.Continuous.SobolevGraph
public import Carleman.Spatial.AllowedWeight

/-! Lemma 3.1's shifted form estimates on the original conforming states.
Inputs are exactly A2 preservation and the unshifted A3 inequalities on the
actual weak Sobolev norms. The shift and every prescribed margin are proved. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {V : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d m ν S)

/-- Multiplication inside the original V, using exactly A2 preservation. -/
def conformingWeight (w : BoundedMultiplier ν)
    (hw : ∀ v : V, w.map (v : Lp ℝ 2 ν) ∈ V) : V →ₗ[ℝ] V :=
  (w.linearMap.comp V.subtype).codRestrict V hw

/-- Original N_sigma, with actual unique weak derivative fields. -/
def conformingWeightedNorm (q : ℝ) (w : BoundedMultiplier ν) (v : V) : ℝ :=
  WeakSobolevJet.weightedNorm q w (domainSobolevJet hS hν hV v)

theorem conformingWeightedNorm_nonneg (q : ℝ) (w : BoundedMultiplier ν) (v : V) :
    0 ≤ conformingWeightedNorm hS hν hV q w v := WeakSobolevJet.weightedNorm_nonneg _ _ _

theorem conformingWeightedNorm_value {q : ℝ} (hq : 0 ≤ q) (w : BoundedMultiplier ν) (v : V) :
    q^m * w.seminorm (v : Lp ℝ 2 ν) ≤ conformingWeightedNorm hS hν hV q w v := by
  have hh := WeakSobolevJet.weighted_value_le hq w (domainSobolevJet hS hν hV v)
  rwa [domainSobolevJet_value] at hh

/-- The manuscript's a_mu, with the actual scalar L² pairing. -/
def shiftedForm (a : V → V → ℝ) (μ : ℝ) (v z : V) : ℝ :=
  a v z + μ * inner ℝ (v : Lp ℝ 2 ν) (z : Lp ℝ 2 ν)

theorem weighted_pairing_le {q : ℝ} (hq : 0 ≤ q) (w ξ : BoundedMultiplier ν)
    (hinv : ∀ᵐ x ∂ν, w.value x * ξ.value x = 1) (v z : V) :
    q^(2*m) * |inner ℝ (v : Lp ℝ 2 ν) (z : Lp ℝ 2 ν)| ≤
      conformingWeightedNorm hS hν hV q w v * conformingWeightedNorm hS hν hV q ξ z := by
  rw [← w.inner_inverse ξ hinv]
  have hi := abs_real_inner_le_norm (w.map (v : Lp ℝ 2 ν)) (ξ.map (z : Lp ℝ 2 ν))
  have hpair := mul_le_mul_of_nonneg_left hi (pow_nonneg hq (2*m))
  have hprod := mul_le_mul (conformingWeightedNorm_value hS hν hV hq w v)
    (conformingWeightedNorm_value hS hν hV hq ξ z)
    (mul_nonneg (pow_nonneg hq _) (apply_nonneg _ _))
    (conformingWeightedNorm_nonneg hS hν hV q w v)
  apply hpair.trans
  convert hprod using 1
  simp only [BoundedMultiplier.seminorm_apply]
  rw [show 2*m = m+m by omega, pow_add]
  ring

/-- The full original shifted-form upper bound, not a bound on unrelated scalars. -/
theorem shiftedForm_bound (a : V → V → ℝ) {q L C : ℝ} (hq : 0 ≤ q) (hL : 0 ≤ L)
    (w ξ : BoundedMultiplier ν) (hinv : ∀ᵐ x ∂ν, w.value x * ξ.value x = 1)
    (ha : ∀ v z, |a v z| ≤ C * conformingWeightedNorm hS hν hV q w v *
      conformingWeightedNorm hS hν hV q ξ z) (v z : V) :
    |shiftedForm a ((L*q)^(2*m)) v z| ≤
      (C+L^(2*m))*conformingWeightedNorm hS hν hV q w v * conformingWeightedNorm hS hν hV q ξ z := by
  have hp := mul_le_mul_of_nonneg_left (weighted_pairing_le hS hν hV hq w ξ hinv v z)
    (pow_nonneg hL (2*m))
  have hh := abs_add_le (a v z) ((L*q)^(2*m) * inner ℝ (v : Lp ℝ 2 ν) (z : Lp ℝ 2 ν))
  rw [abs_mul, abs_of_nonneg (pow_nonneg (mul_nonneg hL hq) _), mul_pow] at hh
  change |a v z + (L*q)^(2*m)*inner ℝ (v : Lp ℝ 2 ν) (z : Lp ℝ 2 ν)| ≤ _
  rw [mul_pow]
  nlinarith [ha v z]

omit [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν] in
/-- Exact shifted energy with σ²v formed by applying the same allowed multiplier twice. -/
theorem shiftedForm_weighted (a : V → V → ℝ) (μ : ℝ) (w : BoundedMultiplier ν)
    (hw : ∀ v : V, w.map (v : Lp ℝ 2 ν) ∈ V) (v : V) :
    shiftedForm a μ v (conformingWeight w hw (conformingWeight w hw v)) =
      a v (conformingWeight w hw (conformingWeight w hw v)) + μ*(w.seminorm (v : Lp ℝ 2 ν))^2 := by
  change a v _ + μ * inner ℝ (v : Lp ℝ 2 ν) (w.map (w.map (v : Lp ℝ 2 ν))) = _
  rw [w.inner_map_twice]
  rfl

/-- A3 yields the original shifted coercivity, with no margin sacrificed. -/
theorem shiftedForm_coercive (a : V → V → ℝ) {q L c C B : ℝ}
    (hm : 0 < m) (hq : 1 ≤ q) (hB : 0 ≤ B) (hmargin : C+B ≤ L^(2*m))
    (w : BoundedMultiplier ν) (hw : ∀ v : V, w.map (v : Lp ℝ 2 ν) ∈ V)
    (ha : ∀ v, c*(conformingWeightedNorm hS hν hV q w v)^2 -
      C*(q^m*w.seminorm (v : Lp ℝ 2 ν))^2 ≤
        a v (conformingWeight w hw (conformingWeight w hw v))) (v : V) :
    c*(conformingWeightedNorm hS hν hV q w v)^2 + B*(q*w.seminorm (v : Lp ℝ 2 ν))^2 ≤
      shiftedForm a ((L*q)^(2*m)) v (conformingWeight w hw (conformingWeight w hw v)) := by
  rw [shiftedForm_weighted]
  simp only [mul_pow]
  have hqpow : q^2 ≤ q^(2*m) := pow_le_pow_right₀ hq (by omega)
  have hs : (q^m)^2 = q^(2*m) := by rw [← pow_mul]; congr 1; omega
  have he := ha v
  rw [mul_pow, hs] at he
  have h₁ := mul_le_mul_of_nonneg_right hmargin
    (mul_nonneg (pow_nonneg (zero_le_one.trans hq) (2*m)) (sq_nonneg (w.seminorm (v : Lp ℝ 2 ν))))
  have h₂ := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hqpow (sq_nonneg (w.seminorm (v : Lp ℝ 2 ν)))) hB
  nlinarith

/-- The original prescribed margin is obtained by a threshold chosen before q, weights and states. -/
theorem shiftedForm_margin_threshold (m : ℕ) (hm : 0 < m) (C B : ℝ) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → C+B ≤ L^(2*m) := by
  refine ⟨max 1 (C+B), le_max_left _ _, ?_⟩
  intro L hL
  have hLone : 1 ≤ L := (le_max_left _ _).trans hL
  have hp : L ≤ L^(2*m) := by
    simpa only [pow_one] using pow_le_pow_right₀ hLone (show 1 ≤ 2*m by omega)
  exact ((le_max_right _ _).trans hL).trans hp

end Carleman
