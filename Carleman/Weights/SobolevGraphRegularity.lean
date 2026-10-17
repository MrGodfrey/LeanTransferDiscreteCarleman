module

public import Carleman.Spatial.SobolevMeasurability
public import Carleman.Weights.ConformingConjugation

/-! Actual time-dependent multiplication preserves the weak Sobolev graph
in Bochner L². Measurability is derived before applying norm domination. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.WeakSobolevJet
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
  {S : Set (SpatialCoordinates d)}

theorem norm_le_parameterNorm {q : ℝ} (hq : 1 ≤ q) (u : WeakSobolevJet d n ν S) :
    ‖u‖ ≤ parameterNorm q BoundedMultiplier.one u := by
  apply (norm_le_sum_fields u).trans
  apply Finset.sum_le_sum
  intro k _
  simpa only [BoundedMultiplier.one_seminorm, one_mul] using
    mul_le_mul_of_nonneg_right (one_le_pow₀ hq) (norm_nonneg (field k u))

/-- Finiteness bound only; it is never used as a uniform graph estimate. -/
theorem parameterNorm_global_le (w : TimeWeight) (ρ : SpatialProfile ν) (τ t : ℝ)
    (u : WeakSobolevJet d n ν S) :
    parameterNorm (w.q t) (ρ.multiplier w τ t) u ≤
      ((n+1:ℝ)*w.max^n*(max 1 (w.max^τ)*Real.exp (ρ.bound*w.max)))*‖u‖ := by
  let B := max 1 (w.max^τ)*Real.exp (ρ.bound*w.max)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hqmax : 1 ≤ w.max := (w.lower t).trans (w.upper t)
  have hk (k : Fin (n+1)) : w.q t^(n-k.val)*(ρ.multiplier w τ t).seminorm (field k u) ≤
      w.max^n*B*‖u‖ := by
    have hp : w.q t^(n-k.val) ≤ w.max^n :=
      (pow_le_pow_left₀ (w.nonneg t) (w.upper t) _).trans
        (pow_le_pow_right₀ hqmax (Nat.sub_le _ _))
    have hs := (ρ.seminorm_global_le w τ t (field k u)).trans
      (mul_le_mul_of_nonneg_left (norm_field_le k u) hB)
    exact (mul_le_mul hp hs (apply_nonneg _ _) (by positivity [w.nonneg t])).trans_eq (by ring)
  calc
    _ ≤ ∑ _k : Fin (n+1), w.max^n*B*‖u‖ := Finset.sum_le_sum fun k _ => hk k
    _ = _ := by simp [B]; ring

variable [IsLocallyFiniteMeasure ν]

theorem memLp_of_weighted_value (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
    (g : TimeGrid) (w : TimeWeight) (ρ : SpatialProfile ν) (τ : ℝ)
    (hq : AEStronglyMeasurable w.q g.timeMeasure)
    {u v : ℝ → WeakSobolevJet d n ν S} (hu : MemLp u 2 g.timeMeasure)
    (hv : ∀ t, value (v t) = (ρ.multiplier w τ t).map (value (u t)))
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t, parameterNorm (w.q t) BoundedMultiplier.one (v t) ≤
      C*parameterNorm (w.q t) (ρ.multiplier w τ t) (u t)) :
    MemLp v 2 g.timeMeasure := by
  have hmu : AEStronglyMeasurable (fun t => value (u t)) g.timeMeasure :=
    valueCLM.continuous.comp_aestronglyMeasurable hu.aestronglyMeasurable
  have hmv := ρ.aestronglyMeasurable_map w τ hq hmu
  have hvalue : AEStronglyMeasurable (fun t => value (v t)) g.timeMeasure := by
    simpa only [hv] using hmv
  apply hu.of_le_mul (c := C*((n+1:ℝ)*w.max^n*(max 1 (w.max^τ)*Real.exp (ρ.bound*w.max))))
    (aestronglyMeasurable_of_value hS hν hvalue)
  apply Filter.Eventually.of_forall
  intro t
  exact (norm_le_parameterNorm (w.lower t) (v t)).trans ((hb t).trans
    ((mul_le_mul_of_nonneg_left (parameterNorm_global_le w ρ τ t (u t)) hC).trans_eq (by ring)))
end Carleman.WeakSobolevJet
