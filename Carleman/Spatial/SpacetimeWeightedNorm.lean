module

public import Carleman.Spatial.SobolevTimeGraph

/-! The original space-time N norm: a finite square sum of actual Bochner
L² derivative norms. Its square is exactly the integral of spatial N². -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman

theorem bochnerL2Norm_sq_integral {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure X}
    {f : X → E} (hf : MemLp f 2 μ) :
    (bochnerL2Norm μ f)^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [bochnerL2Norm_eq _ hf, ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

namespace WeakSobolevJet
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
  {S : Set (SpatialCoordinates d)}

def spacetimeWeightedSq (g : TimeGrid) (r : ℝ → ℝ) (σ : ℝ → BoundedMultiplier ν)
    (u : ℝ → WeakSobolevJet d n ν S) : ℝ :=
  ∑ k, (bochnerL2Norm g.timeMeasure (parameterTimeField r σ u k))^2

def spacetimeWeightedNorm (g : TimeGrid) (r : ℝ → ℝ) (σ : ℝ → BoundedMultiplier ν)
    (u : ℝ → WeakSobolevJet d n ν S) : ℝ := Real.sqrt (spacetimeWeightedSq g r σ u)

theorem spacetimeWeightedNorm_nonneg (g : TimeGrid) (r : ℝ → ℝ) (σ : ℝ → BoundedMultiplier ν)
    (u : ℝ → WeakSobolevJet d n ν S) : 0 ≤ spacetimeWeightedNorm g r σ u := Real.sqrt_nonneg _

theorem spacetimeWeightedNorm_sq (g : TimeGrid) (r : ℝ → ℝ) (σ : ℝ → BoundedMultiplier ν)
    (u : ℝ → WeakSobolevJet d n ν S) :
    (spacetimeWeightedNorm g r σ u)^2 = spacetimeWeightedSq g r σ u :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem weightedSq_eq_timeFields (r : ℝ → ℝ) (σ : ℝ → BoundedMultiplier ν)
    (u : ℝ → WeakSobolevJet d n ν S) {t : ℝ} (ht : 0 ≤ r t) :
    weightedSq (r t) (σ t) (u t) = ∑ k, ‖parameterTimeField r σ u k t‖^2 := by
  simp_rw [parameterTimeField_norm _ _ _ _ ht]
  rfl

theorem weightedSq_integrable (g : TimeGrid) (r : ℝ → ℝ) (σ : ℝ → BoundedMultiplier ν)
    (u : ℝ → WeakSobolevJet d n ν S)
    (hu : ∀ k, MemLp (parameterTimeField r σ u k) 2 g.timeMeasure)
    (hr : ∀ᵐ t ∂g.timeMeasure, 0 ≤ r t) :
    Integrable (fun t => weightedSq (r t) (σ t) (u t)) g.timeMeasure := by
  have hi : ∀ k, Integrable (fun t => ‖parameterTimeField r σ u k t‖^2) g.timeMeasure :=
    fun k => (memLp_two_iff_integrable_sq_norm (hu k).aestronglyMeasurable).mp (hu k)
  exact (integrable_finsetSum _ (fun k _ => hi k)).congr
    (hr.mono fun t ht => (weightedSq_eq_timeFields r σ u ht).symm)

/-- Finiteness is explicit, and the square sum agrees with the actual energy
integral without a dimension or time-length loss. -/
theorem spacetimeWeightedSq_integral (g : TimeGrid) (r : ℝ → ℝ) (σ : ℝ → BoundedMultiplier ν)
    (u : ℝ → WeakSobolevJet d n ν S)
    (hu : ∀ k, MemLp (parameterTimeField r σ u k) 2 g.timeMeasure)
    (hr : ∀ᵐ t ∂g.timeMeasure, 0 ≤ r t) :
    spacetimeWeightedSq g r σ u = ∫ t, weightedSq (r t) (σ t) (u t) ∂g.timeMeasure := by
  unfold spacetimeWeightedSq
  simp_rw [bochnerL2Norm_sq_integral (hu _)]
  rw [← integral_finsetSum _ (fun k _ =>
    (memLp_two_iff_integrable_sq_norm (hu k).aestronglyMeasurable).mp (hu k))]
  exact integral_congr_ae (hr.mono fun t ht => (weightedSq_eq_timeFields r σ u ht).symm)

/-- A spatial N estimate lifts with exactly the same constant. -/
theorem spacetimeWeightedNorm_le (g : TimeGrid) (r s : ℝ → ℝ)
    (σ ξ : ℝ → BoundedMultiplier ν) (u v : ℝ → WeakSobolevJet d n ν S)
    (hu : ∀ k, MemLp (parameterTimeField r σ u k) 2 g.timeMeasure)
    (hv : ∀ k, MemLp (parameterTimeField s ξ v k) 2 g.timeMeasure)
    (hr : ∀ᵐ t ∂g.timeMeasure, 0 ≤ r t) (hs : ∀ᵐ t ∂g.timeMeasure, 0 ≤ s t)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ t ∂g.timeMeasure, weightedNorm (r t) (σ t) (u t) ≤
      C*weightedNorm (s t) (ξ t) (v t)) :
    spacetimeWeightedNorm g r σ u ≤ C*spacetimeWeightedNorm g s ξ v := by
  apply (sq_le_sq₀ (spacetimeWeightedNorm_nonneg _ _ _ _)
    (mul_nonneg hC (spacetimeWeightedNorm_nonneg _ _ _ _))).mp
  rw [mul_pow, spacetimeWeightedNorm_sq, spacetimeWeightedNorm_sq,
    spacetimeWeightedSq_integral g r σ u hu hr, spacetimeWeightedSq_integral g s ξ v hv hs,
    ← integral_const_mul]
  apply integral_mono_ae (weightedSq_integrable g r σ u hu hr)
    ((weightedSq_integrable g s ξ v hv hs).const_mul _)
  filter_upwards [hb] with t ht
  have hh := (sq_le_sq₀ (weightedNorm_nonneg _ _ _)
    (mul_nonneg hC (weightedNorm_nonneg _ _ _))).mpr ht
  simpa only [mul_pow, weightedNorm_sq] using hh

end WeakSobolevJet
end Carleman
