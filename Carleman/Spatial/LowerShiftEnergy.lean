module

public import Carleman.Spatial.WeightedOperatorEnergy

/-! A3 energy for any shift with the required lower bound. In particular the
coefficient need not equal the smooth (Lq)^(2m); this applies directly to the
actual frozen coefficient without a shift-difference perturbation. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {V D : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d m ν S)

/-- The prescribed form margin is retained under a lower bound on μ. -/
theorem shiftedForm_coercive_of_lower (a : V → V → ℝ) {q μ c C B : ℝ}
    (hm : 0 < m) (hq : 1 ≤ q) (hB : 0 ≤ B) (hμ : (C+B)*q^(2*m) ≤ μ)
    (w : BoundedMultiplier ν) (hw : ∀ v : V, w.map (v : Lp ℝ 2 ν) ∈ V)
    (ha : ∀ v, c*(conformingWeightedNorm hS hν hV q w v)^2 -
      C*(q^m*w.seminorm (v : Lp ℝ 2 ν))^2 ≤
        a v (conformingWeight w hw (conformingWeight w hw v))) (v : V) :
    c*(conformingWeightedNorm hS hν hV q w v)^2 + B*(q*w.seminorm (v : Lp ℝ 2 ν))^2 ≤
      shiftedForm a μ v (conformingWeight w hw (conformingWeight w hw v)) := by
  rw [shiftedForm_weighted]
  have hs : (q^m)^2 = q^(2*m) := by rw [← pow_mul]; congr 1; omega
  have he := ha v
  rw [mul_pow, hs] at he
  have h₁ := mul_le_mul_of_nonneg_right hμ (sq_nonneg (w.seminorm (v : Lp ℝ 2 ν)))
  have hqpow : q^2 ≤ q^(2*m) := pow_le_pow_right₀ hq (by omega)
  have h₂ := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hqpow (sq_nonneg (w.seminorm (v : Lp ℝ 2 ν)))) hB
  simp only [mul_pow]
  nlinarith

variable (hDV : D ≤ V) (a : V → V → ℝ) (A : D →ₗ[ℝ] Lp ℝ 2 ν)
  (htest : ∀ u : D, ∀ v : V, a (D.inclusion hDV u) v = inner ℝ (A u) (v : Lp ℝ 2 ν))

include htest
theorem shiftedOperator_weighted_energy_of_lower {q μ c C : ℝ} (hm : 0 < m) (hq : 1 ≤ q)
    (hμ : C*q^(2*m) ≤ μ) (w : BoundedMultiplier ν)
    (hw : ∀ v : V, w.map (v : Lp ℝ 2 ν) ∈ V)
    (ha : ∀ v : V, c*(conformingWeightedNorm hS hν hV q w v)^2 -
      C*(q^m*w.seminorm (v : Lp ℝ 2 ν))^2 ≤
        a v (conformingWeight w hw (conformingWeight w hw v))) (u : D) :
    c*(conformingWeightedNorm hS hν hV q w (D.inclusion hDV u))^2 ≤
      w.seminorm (A u + μ • (u : Lp ℝ 2 ν))*w.seminorm (u : Lp ℝ 2 ν) := by
  have hh := shiftedForm_coercive_of_lower hS hν hV a hm hq (B := 0) le_rfl
    (by simpa using hμ) w hw ha (D.inclusion hDV u)
  simp only [zero_mul, add_zero] at hh
  rw [shiftedOperator_weighted_pair hDV a A htest] at hh
  exact hh.trans (real_inner_le_norm _ _)

/-- Only the a.e. lower bound enters; no derivative or continuity of μ is used. -/
theorem shiftedOperator_spacetime_energy_of_lower (g : TimeGrid) (w : TimeWeight)
    (σ : ℝ → BoundedMultiplier ν) (μ : ℝ → ℝ) {c C : ℝ} (hm : 0 < m)
    (hμ : ∀ᵐ t ∂g.timeMeasure, C*w.q t^(2*m) ≤ μ t)
    (hw : ∀ t (v : V), (σ t).map (v : Lp ℝ 2 ν) ∈ V)
    (ha : ∀ t (v : V), c*(conformingWeightedNorm hS hν hV (w.q t) (σ t) v)^2 -
      C*(w.q t^m*(σ t).seminorm (v : Lp ℝ 2 ν))^2 ≤
        a v (conformingWeight (σ t) (hw t) (conformingWeight (σ t) (hw t) v)))
    (u : ℝ → D)
    (hfields : ∀ k, MemLp (WeakSobolevJet.parameterTimeField w.q σ
      (fun t => domainSobolevJet hS hν hV (D.inclusion hDV (u t))) k) 2 g.timeMeasure)
    (hu : MemLp (fun t => (σ t).map (u t : Lp ℝ 2 ν)) 2 g.timeMeasure)
    (hAu : MemLp (fun t => (σ t).map (A (u t) + μ t • (u t : Lp ℝ 2 ν))) 2 g.timeMeasure) :
    c*(WeakSobolevJet.spacetimeWeightedNorm g w.q σ
      (fun t => domainSobolevJet hS hν hV (D.inclusion hDV (u t))))^2 ≤
      bochnerL2Norm g.timeMeasure (fun t => (σ t).map (A (u t) + μ t • (u t : Lp ℝ 2 ν)))*
        bochnerL2Norm g.timeMeasure (fun t => (σ t).map (u t : Lp ℝ 2 ν)) := by
  let f := fun t => (σ t).map (A (u t) + μ t • (u t : Lp ℝ 2 ν))
  let z := fun t => (σ t).map (u t : Lp ℝ 2 ν)
  let J := fun t => domainSobolevJet hS hν hV (D.inclusion hDV (u t))
  have hq : ∀ᵐ t ∂g.timeMeasure, 0 ≤ w.q t := Filter.Eventually.of_forall w.nonneg
  have hleft := (WeakSobolevJet.weightedSq_integrable g w.q σ J hfields hq).const_mul c
  have hp : (fun t => inner ℝ ((hAu.toLp f) t) ((hu.toLp z) t)) =ᵐ[g.timeMeasure]
      (fun t => inner ℝ (f t) (z t)) := by
    filter_upwards [hAu.coeFn_toLp, hu.coeFn_toLp] with t ht hs
    rw [ht, hs]
  have hpair := (L2.integrable_inner (hAu.toLp f) (hu.toLp z)).congr hp
  have he : c*(WeakSobolevJet.spacetimeWeightedNorm g w.q σ J)^2 ≤
      inner ℝ (hAu.toLp f) (hu.toLp z) := by
    rw [WeakSobolevJet.spacetimeWeightedNorm_sq,
      WeakSobolevJet.spacetimeWeightedSq_integral g w.q σ J hfields hq,
      ← integral_const_mul, L2.inner_def, integral_congr_ae hp]
    apply integral_mono_ae hleft hpair
    filter_upwards [hμ] with t ht
    have hh := shiftedForm_coercive_of_lower hS hν hV a hm (w.lower t) (B := 0) le_rfl
      (by simpa using ht) (σ t) (hw t) (ha t) (D.inclusion hDV (u t))
    simp only [zero_mul, add_zero] at hh
    rw [shiftedOperator_weighted_pair hDV a A htest] at hh
    simpa only [conformingWeightedNorm, WeakSobolevJet.weightedNorm_sq] using hh
  apply he.trans
  change inner ℝ (hAu.toLp f) (hu.toLp z) ≤ bochnerL2Norm g.timeMeasure f*bochnerL2Norm g.timeMeasure z
  rw [bochnerL2Norm_eq f hAu, bochnerL2Norm_eq z hu]
  exact real_inner_le_norm _ _
end Carleman
