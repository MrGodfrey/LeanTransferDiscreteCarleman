module

public import Carleman.Spatial.ParameterConjugation
public import Carleman.Spatial.WeightedTime
public import Carleman.Continuous.BochnerNorm

/-! The manuscript's space-time R norm is the sum of the Bochner L² norms
of all scaled derivative collections. It is not the L² norm of their sum. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman.WeakSobolevJet
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
  {S : Set (SpatialCoordinates d)}

def parameterTimeField (r : ℝ → ℝ) (σ : ℝ → BoundedMultiplier ν)
    (u : ℝ → WeakSobolevJet d n ν S) (k : Fin (n+1)) (t : ℝ) :
    Lp (DerivativeFiber d k.val) 2 ν := r t^(n-k.val) • (σ t).map (field k (u t))

def spacetimeParameterNorm (g : TimeGrid) (r : ℝ → ℝ) (σ : ℝ → BoundedMultiplier ν)
    (u : ℝ → WeakSobolevJet d n ν S) : ℝ :=
  ∑ k, bochnerL2Norm g.timeMeasure (parameterTimeField r σ u k)

theorem parameterTimeField_norm (r : ℝ → ℝ) (σ : ℝ → BoundedMultiplier ν)
    (u : ℝ → WeakSobolevJet d n ν S) (k : Fin (n+1)) {t : ℝ} (ht : 0 ≤ r t) :
    ‖parameterTimeField r σ u k t‖ = r t^(n-k.val)*(σ t).seminorm (field k (u t)) := by
  rw [parameterTimeField, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht _)]
  rfl

theorem parameterNorm_eq_sum_timeField (r : ℝ → ℝ) (σ : ℝ → BoundedMultiplier ν)
    (u : ℝ → WeakSobolevJet d n ν S) {t : ℝ} (ht : 0 ≤ r t) :
    parameterNorm (r t) (σ t) (u t) = ∑ k, ‖parameterTimeField r σ u k t‖ := by
  simp_rw [parameterTimeField_norm r σ u _ ht]
  rfl

/-- Scaled multiplication preserves Bochner L²; this finite bound may use
qmax, but none of the subsequent comparison constants use it. -/
theorem memLp_parameterTimeField (g : TimeGrid) (w : TimeWeight) (ρ : SpatialProfile ν)
    (τ L : ℝ) (hq : AEStronglyMeasurable w.q g.timeMeasure)
    {u : ℝ → WeakSobolevJet d n ν S} (hu : MemLp u 2 g.timeMeasure) (k : Fin (n+1)) :
    MemLp (parameterTimeField (fun t => L*w.q t) (ρ.multiplier w τ) u k) 2 g.timeMeasure := by
  have hv := ρ.memLp_map w τ hq (memLp_field hu k)
  apply hv.of_le_mul (c := (|L| *w.max)^(n-k.val))
    (((hq.const_mul L).pow _).smul hv.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro t
  change ‖(L*w.q t)^(n-k.val) • (ρ.multiplier w τ t).map (field k (u t))‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_mul, abs_of_pos (w.pos t)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity [w.pos t])
    (mul_le_mul_of_nonneg_left (w.upper t) (abs_nonneg L)) _) (norm_nonneg _)

theorem memLp_unweightedParameterTimeField (g : TimeGrid) (w : TimeWeight) (L : ℝ)
    (hq : AEStronglyMeasurable w.q g.timeMeasure)
    {u : ℝ → WeakSobolevJet d n ν S} (hu : MemLp u 2 g.timeMeasure) (k : Fin (n+1)) :
    MemLp (parameterTimeField (fun t => L*w.q t) (fun _ => BoundedMultiplier.one) u k)
      2 g.timeMeasure := by
  change MemLp (fun t => (L*w.q t)^(n-k.val) •
    BoundedMultiplier.one.map (field k (u t))) 2 g.timeMeasure
  simp only [BoundedMultiplier.one_map]
  have hv := memLp_field hu k
  apply hv.of_le_mul (c := (|L| *w.max)^(n-k.val))
    (((hq.const_mul L).pow _).smul hv.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro t
  change ‖(L*w.q t)^(n-k.val) • field k (u t)‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_mul, abs_of_pos (w.pos t)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity [w.pos t])
    (mul_le_mul_of_nonneg_left (w.upper t) (abs_nonneg L)) _) (norm_nonneg _)

/-- A spatial R comparison lifts to the actual space-time R comparison.
The finite order loss n+1 is independent of T and of all weight parameters. -/
theorem spacetimeParameterNorm_le (g : TimeGrid) (r s : ℝ → ℝ)
    (σ ξ : ℝ → BoundedMultiplier ν) (u v : ℝ → WeakSobolevJet d n ν S)
    (hu : ∀ k, MemLp (parameterTimeField r σ u k) 2 g.timeMeasure)
    (hv : ∀ k, MemLp (parameterTimeField s ξ v k) 2 g.timeMeasure)
    (hr : ∀ᵐ t ∂g.timeMeasure, 0 ≤ r t) (hs : ∀ᵐ t ∂g.timeMeasure, 0 ≤ s t)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ t ∂g.timeMeasure, parameterNorm (r t) (σ t) (u t) ≤
      C*parameterNorm (s t) (ξ t) (v t)) :
    spacetimeParameterNorm g r σ u ≤ (n+1:ℝ)*C*spacetimeParameterNorm g s ξ v := by
  have hk (k : Fin (n+1)) : bochnerL2Norm g.timeMeasure (parameterTimeField r σ u k) ≤
      C*spacetimeParameterNorm g s ξ v := by
    apply bochnerL2Norm_le_sum (hu k) _ hv hC
    filter_upwards [hr, hs, hb] with t ht ht' hb'
    rw [parameterTimeField_norm _ _ _ _ ht]
    exact (parameterNorm_component ht _ _ k).trans
      (hb'.trans_eq (congrArg (C*·) (parameterNorm_eq_sum_timeField s ξ v ht')))
  calc
    _ ≤ ∑ _k : Fin (n+1), C*spacetimeParameterNorm g s ξ v :=
      Finset.sum_le_sum fun k _ => hk k
    _ = _ := by simp [mul_assoc]
end Carleman.WeakSobolevJet
