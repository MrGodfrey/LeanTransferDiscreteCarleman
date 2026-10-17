module

public import Carleman.Spatial.MultiplierContinuity
public import Carleman.Spatial.SobolevTopology

/-! Finite, actual weighted space-time norms from Bochner L² regularity.
These proofs supply measurability before using domination. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman.SpatialProfile
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  {ν : Measure Ω} (ρ : SpatialProfile ν)

theorem timeSquareIntegrable_of_memLp [NormedSpace ℝ E] (g : TimeGrid) (w : TimeWeight) (τ s : ℝ)
    (hq : AEStronglyMeasurable w.q g.timeMeasure) {u : ℝ → Lp E 2 ν}
    (hu : MemLp u 2 g.timeMeasure) :
    TimeSquareIntegrable g w.q s (fun t => (ρ.multiplier w τ t).seminorm) u := by
  have hm := ρ.memLp_map w (τ+s/2) hq hu
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  change Integrable (fun t => w.q t^s * ((ρ.multiplier w τ t).seminorm (u t))^2) _
  simp_rw [ρ.density_eq_shifted_seminorm_sq]
  exact hi

/-- The finite density has exactly the norm of the actual Bochner L² class. -/
theorem timeSq_eq_norm_toLp_sq [InnerProductSpace ℝ E]
    (g : TimeGrid) (w : TimeWeight) (τ s : ℝ)
    (hq : AEStronglyMeasurable w.q g.timeMeasure) {u : ℝ → Lp E 2 ν}
    (hu : MemLp u 2 g.timeMeasure) :
    timeSq g w.q s (fun t => (ρ.multiplier w τ t).seminorm) u =
      ‖(ρ.memLp_map w (τ+s/2) hq hu).toLp
        (fun t => (ρ.multiplier w (τ+s/2) t).map (u t))‖^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(ρ.memLp_map w (τ+s/2) hq hu).coeFn_toLp] with t ht
  rw [ht, real_inner_self_eq_norm_sq]
  exact ρ.density_eq_shifted_seminorm_sq w τ s t (u t)

theorem timeNorm_eq_norm_toLp [InnerProductSpace ℝ E]
    (g : TimeGrid) (w : TimeWeight) (τ s : ℝ)
    (hq : AEStronglyMeasurable w.q g.timeMeasure) {u : ℝ → Lp E 2 ν}
    (hu : MemLp u 2 g.timeMeasure) :
    timeNorm g w.q s (fun t => (ρ.multiplier w τ t).seminorm) u =
      ‖(ρ.memLp_map w (τ+s/2) hq hu).toLp
        (fun t => (ρ.multiplier w (τ+s/2) t).map (u t))‖ := by
  rw [timeNorm, ρ.timeSq_eq_norm_toLp_sq g w τ s hq hu, Real.sqrt_sq (norm_nonneg _)]

end Carleman.SpatialProfile
namespace Carleman.DifferentialExpression
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
  {m : ℕ} {E : Fin (m+1) → Type*}
  [∀ k, NormedAddCommGroup (E k)] [∀ k, NormedSpace ℝ (E k)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {j : ℕ} (D : DifferentialExpression ν E F j)

theorem memLp_apply {μ : Measure ℝ} (u : ∀ k, ℝ → Lp (E k) 2 ν)
    (hu : ∀ k, MemLp (u k) 2 μ) :
    MemLp (fun t => D.apply (fun k => u k t)) 2 μ := by
  apply memLp_finsetSum
  intro k _
  apply (hu k).of_le_mul (c := (D.coefficient k).bound)
    ((D.coefficient k).continuousLinearMap.continuous.comp_aestronglyMeasurable
      (hu k).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun t => (D.coefficient k).norm_map_le (u k t)

/-- This proves the previously separate left-side finiteness obligation;
it does not infer integrability from the numerical value of a totalized integral. -/
theorem timeSquareIntegrable_apply (g : TimeGrid) (w : TimeWeight)
    (ρ : SpatialProfile ν) (τ s : ℝ) (hq : AEStronglyMeasurable w.q g.timeMeasure)
    (u : ∀ k, ℝ → Lp (E k) 2 ν) (hu : ∀ k, MemLp (u k) 2 g.timeMeasure) :
    TimeSquareIntegrable g w.q s (fun t => (ρ.multiplier w τ t).seminorm)
      (fun t => D.apply (fun k => u k t)) :=
  ρ.timeSquareIntegrable_of_memLp g w τ s hq (D.memLp_apply u hu)

end Carleman.DifferentialExpression
namespace Carleman.WeakSobolevJet
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] {S : Set (SpatialCoordinates d)}

/-- One true graph-space L² assumption supplies every weighted derivative
density, for every finite allowed exponent. -/
theorem timeSquareIntegrable_field (g : TimeGrid) (w : TimeWeight)
    (ρ : SpatialProfile ν) (τ s : ℝ) (hq : AEStronglyMeasurable w.q g.timeMeasure)
    {u : ℝ → WeakSobolevJet d m ν S} (hu : MemLp u 2 g.timeMeasure) (k : Fin (m+1)) :
    TimeSquareIntegrable g w.q s
      (fun t => (ρ.multiplier w τ t).seminorm.comp (field k)) u :=
  ρ.timeSquareIntegrable_of_memLp g w τ s hq (memLp_field hu k)

end Carleman.WeakSobolevJet
