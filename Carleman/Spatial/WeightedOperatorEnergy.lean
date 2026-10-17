module

public import Carleman.Spatial.ShiftedFormBounds
public import Carleman.Spatial.SpacetimeWeightedNorm

/-! The original A3 coercivity gives a weighted parameter-energy estimate
directly on D(A). This route uses the actual form/operator pairing and avoids
a separate Sobolev interpolation theorem for this energy step. It does not
provide the still-needed uniform weighted L² or operator graph estimates. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman

theorem BoundedMultiplier.inner_map_pair {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ν : Measure X}
    (w : BoundedMultiplier ν) (u v : Lp E 2 ν) :
    inner ℝ (w.map u) v = inner ℝ u (w.map v) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [w.map_ae u, w.map_ae v] with x hu hv
  rw [hu, hv, real_inner_smul_left, real_inner_smul_right]

variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {V D : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d m ν S) (hDV : D ≤ V)
  (a : V → V → ℝ) (A : D →ₗ[ℝ] Lp ℝ 2 ν)
  (htest : ∀ u : D, ∀ v : V, a (D.inclusion hDV u) v = inner ℝ (A u) (v : Lp ℝ 2 ν))

include htest
omit [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν] in
/-- The exact A1 form pairing identifies the shifted weighted energy. -/
theorem shiftedOperator_weighted_pair (μ : ℝ) (w : BoundedMultiplier ν)
    (hw : ∀ v : V, w.map (v : Lp ℝ 2 ν) ∈ V) (u : D) :
    shiftedForm a μ (D.inclusion hDV u)
      (conformingWeight w hw (conformingWeight w hw (D.inclusion hDV u))) =
      inner ℝ (w.map (A u + μ • (u : Lp ℝ 2 ν))) (w.map (u : Lp ℝ 2 ν)) := by
  rw [shiftedForm, htest]
  change inner ℝ (A u) (w.map (w.map (u : Lp ℝ 2 ν))) +
    μ*inner ℝ (u : Lp ℝ 2 ν) (w.map (w.map (u : Lp ℝ 2 ν))) = _
  rw [← real_inner_smul_left, ← inner_add_left, ← w.inner_map_pair]

/-- A3 and the original shift give a parameter N estimate on every actual
operator-domain state. No boundary condition or interpolation is added. -/
theorem shiftedOperator_weighted_energy {q L c C : ℝ} (hm : 0 < m) (hq : 1 ≤ q)
    (hmargin : C ≤ L^(2*m)) (w : BoundedMultiplier ν)
    (hw : ∀ v : V, w.map (v : Lp ℝ 2 ν) ∈ V)
    (ha : ∀ v : V, c*(conformingWeightedNorm hS hν hV q w v)^2 -
      C*(q^m*w.seminorm (v : Lp ℝ 2 ν))^2 ≤
        a v (conformingWeight w hw (conformingWeight w hw v))) (u : D) :
    c*(conformingWeightedNorm hS hν hV q w (D.inclusion hDV u))^2 ≤
      w.seminorm (A u + (L*q)^(2*m) • (u : Lp ℝ 2 ν))*w.seminorm (u : Lp ℝ 2 ν) := by
  have hh := shiftedForm_coercive hS hν hV a hm hq (B := 0) le_rfl
    (by simpa using hmargin) w hw ha (D.inclusion hDV u)
  simp only [zero_mul, add_zero] at hh
  rw [shiftedOperator_weighted_pair hDV a A htest] at hh
  exact hh.trans (real_inner_le_norm _ _)

/-- The same estimate integrated in time, for the genuine Bochner N norm.
All finiteness premises concern actual fields and no error estimate is assumed. -/
theorem shiftedOperator_spacetime_energy (g : TimeGrid) (w : TimeWeight)
    (σ : ℝ → BoundedMultiplier ν) {L c C : ℝ} (hm : 0 < m) (hmargin : C ≤ L^(2*m))
    (hw : ∀ t (v : V), (σ t).map (v : Lp ℝ 2 ν) ∈ V)
    (ha : ∀ t (v : V), c*(conformingWeightedNorm hS hν hV (w.q t) (σ t) v)^2 -
      C*(w.q t^m*(σ t).seminorm (v : Lp ℝ 2 ν))^2 ≤
        a v (conformingWeight (σ t) (hw t) (conformingWeight (σ t) (hw t) v)))
    (u : ℝ → D)
    (hfields : ∀ k, MemLp (WeakSobolevJet.parameterTimeField w.q σ
      (fun t => domainSobolevJet hS hν hV (D.inclusion hDV (u t))) k) 2 g.timeMeasure)
    (hu : MemLp (fun t => (σ t).map (u t : Lp ℝ 2 ν)) 2 g.timeMeasure)
    (hAu : MemLp (fun t => (σ t).map (A (u t) + (L*w.q t)^(2*m) • (u t : Lp ℝ 2 ν)))
      2 g.timeMeasure) :
    c*(WeakSobolevJet.spacetimeWeightedNorm g w.q σ
      (fun t => domainSobolevJet hS hν hV (D.inclusion hDV (u t))))^2 ≤
      bochnerL2Norm g.timeMeasure (fun t => (σ t).map (A (u t) + (L*w.q t)^(2*m) •
        (u t : Lp ℝ 2 ν)))*bochnerL2Norm g.timeMeasure (fun t => (σ t).map (u t : Lp ℝ 2 ν)) := by
  let f := fun t => (σ t).map (A (u t) + (L*w.q t)^(2*m) • (u t : Lp ℝ 2 ν))
  let z := fun t => (σ t).map (u t : Lp ℝ 2 ν)
  let J := fun t => domainSobolevJet hS hν hV (D.inclusion hDV (u t))
  have hq : ∀ᵐ t ∂g.timeMeasure, 0 ≤ w.q t := Filter.Eventually.of_forall w.nonneg
  have hleft := (WeakSobolevJet.weightedSq_integrable g w.q σ J hfields hq).const_mul c
  have hp : (fun t => inner ℝ ((hAu.toLp f) t) ((hu.toLp z) t)) =ᵐ[g.timeMeasure]
      (fun t => inner ℝ (f t) (z t)) := by
    filter_upwards [hAu.coeFn_toLp, hu.coeFn_toLp] with t ht hs
    rw [ht, hs]
  have hpair : Integrable (fun t => inner ℝ (f t) (z t)) g.timeMeasure :=
    (L2.integrable_inner (hAu.toLp f) (hu.toLp z)).congr hp
  have he : c*(WeakSobolevJet.spacetimeWeightedNorm g w.q σ J)^2 ≤
      inner ℝ (hAu.toLp f) (hu.toLp z) := by
    rw [WeakSobolevJet.spacetimeWeightedNorm_sq,
      WeakSobolevJet.spacetimeWeightedSq_integral g w.q σ J hfields hq,
      ← integral_const_mul, L2.inner_def]
    rw [integral_congr_ae hp]
    apply integral_mono_ae hleft hpair
    apply Filter.Eventually.of_forall
    intro t
    have hh := shiftedForm_coercive hS hν hV a hm (w.lower t) (B := 0) le_rfl
      (by simpa using hmargin) (σ t) (hw t) (ha t) (D.inclusion hDV (u t))
    simp only [zero_mul, add_zero] at hh
    rw [shiftedOperator_weighted_pair hDV a A htest] at hh
    simpa only [conformingWeightedNorm, WeakSobolevJet.weightedNorm_sq] using hh
  apply he.trans
  change inner ℝ (hAu.toLp f) (hu.toLp z) ≤ bochnerL2Norm g.timeMeasure f*bochnerL2Norm g.timeMeasure z
  rw [bochnerL2Norm_eq f hAu, bochnerL2Norm_eq z hu]
  exact real_inner_le_norm _ _

end Carleman
