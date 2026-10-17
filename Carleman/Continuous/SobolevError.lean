module

public import Carleman.Continuous.SobolevGraph
public import Carleman.Periodic.CellIntegral

/-! Genuine graph-space reconstruction errors and their weighted finiteness.
Both orientations and every discrete sequence are included. No mesh smallness
is needed for finiteness; such thresholds belong to uniform error estimates. -/
@[expose] public noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Carleman.Orientation
variable (s : Orientation) (g : TimeGrid)

theorem aestronglyMeasurable_extension {E : Type*} [NormedAddCommGroup E]
    (u : g.Sequence E) : AEStronglyMeasurable (s.extension g u) g.timeMeasure := by
  let j := s.extension g (fun i => i)
  have hs : ∀ i, MeasurableSet {t | j t = i} := fun i =>
    (s.measurable_cell_index g) (measurableSet_singleton i)
  have he : s.extension g u =
      (fun t => ∑ i : g.Index, ({t | j t = i}.indicator (fun _ => u i)) t) := by
    funext t
    have hx : s.extension g u t = u (j t) := by cases s <;> rfl
    rw [hx]
    simp [Set.indicator, eq_comm]
  rw [he]
  exact Finset.univ.aestronglyMeasurable_fun_sum fun i _ =>
    aestronglyMeasurable_const.indicator (hs i)

theorem memLp_extension {E : Type*} [NormedAddCommGroup E] (u : g.Sequence E) :
    MemLp (s.extension g u) 2 g.timeMeasure := by
  apply (memLp_two_iff_integrable_sq_norm (s.aestronglyMeasurable_extension g u)).mpr
  have he : (fun t => ‖s.extension g u t‖^2) =
      s.extension g (fun i => ‖u i‖^2) := by cases s <;> rfl
  rw [he]
  exact s.integrable_extension g _

/-- Every frozen scalar sequence is bounded, so multiplication preserves L².
The bound here serves finiteness only and is not an error-estimate constant. -/
theorem memLp_smul_extension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : g.Sequence ℝ) {u : ℝ → E} (hu : MemLp u 2 g.timeMeasure) :
    MemLp (fun t => s.extension g a t • u t) 2 g.timeMeasure := by
  apply hu.of_le_mul (c := ∑ i : g.Index, |a i|)
    ((s.aestronglyMeasurable_extension g a).smul hu.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro t
  change ‖s.extension g a t • u t‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have he : s.extension g a t = a (s.extension g (fun i => i) t) := by cases s <;> rfl
  rw [he]
  exact Finset.single_le_sum (fun i _ => abs_nonneg (a i)) (Finset.mem_univ _)

end Carleman.Orientation
namespace Carleman.PeriodicWeakTrajectory
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {D : Submodule ℝ (Lp ℝ 2 ν)} (hD : D ≤ sobolevSubspace d n ν S)
  {g : TimeGrid} {A : D →ₗ[ℝ] Lp ℝ 2 ν} (u : PeriodicWeakTrajectory g D A)

/-- v is the genuine Sobolev reconstruction of the original arbitrary nodes. -/
def sobolevError (s : Orientation) (v : g.Sequence (WeakSobolevJet d n ν S))
    (t : ℝ) : WeakSobolevJet d n ν S :=
  domainSobolevJet hS hν hD (u.domainValue t) - s.extension g v t

theorem sobolevError_value_ae (s : Orientation)
    (v : g.Sequence (WeakSobolevJet d n ν S)) :
    (fun t => WeakSobolevJet.value (u.sobolevError hS hν hD s v t)) =ᵐ[g.timeMeasure]
      (fun t => u.value t - s.extension g (fun i => WeakSobolevJet.value (v i)) t) := by
  filter_upwards [u.domainValue_ae] with t ht
  simp only [sobolevError, map_sub, domainSobolevJet_value, ht]
  cases s <;> rfl

theorem sobolevError_L2 (C : ℝ)
    (hell : ∀ v : D, ‖domainSobolevJet hS hν hD v‖ ≤ C * ‖A v‖)
    (s : Orientation) (v : g.Sequence (WeakSobolevJet d n ν S)) :
    MemLp (u.sobolevError hS hν hD s v) 2 g.timeMeasure :=
  (u.domainSobolev_L2 hS hν hD C hell).sub (s.memLp_extension g v)

/-- Finite weighted error fields, obtained from A1 and genuine B1 regularity. -/
theorem sobolevError_field_finite (C : ℝ)
    (hell : ∀ v : D, ‖domainSobolevJet hS hν hD v‖ ≤ C * ‖A v‖)
    (s : Orientation) (v : g.Sequence (WeakSobolevJet d n ν S))
    (w : TimeWeight) (ρ : SpatialProfile ν) (τ b : ℝ)
    (hq : AEStronglyMeasurable w.q g.timeMeasure) (k : Fin (n+1)) :
    TimeSquareIntegrable g w.q b (fun t =>
      (ρ.multiplier w τ t).seminorm.comp (WeakSobolevJet.field k))
      (u.sobolevError hS hν hD s v) :=
  WeakSobolevJet.timeSquareIntegrable_field g w ρ τ b hq
    (u.sobolevError_L2 hS hν hD C hell s v) k

theorem sobolevError_expression_finite {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {j : ℕ}
    (P : DifferentialExpression ν (fun k : Fin (n+1) => DerivativeFiber d k.val) F j)
    (C : ℝ) (hell : ∀ v : D, ‖domainSobolevJet hS hν hD v‖ ≤ C * ‖A v‖)
    (s : Orientation) (v : g.Sequence (WeakSobolevJet d n ν S))
    (w : TimeWeight) (ρ : SpatialProfile ν) (τ b : ℝ)
    (hq : AEStronglyMeasurable w.q g.timeMeasure) :
    TimeSquareIntegrable g w.q b (fun t =>
      (ρ.multiplier w τ t).seminorm.comp (P.onFields WeakSobolevJet.field))
      (u.sobolevError hS hν hD s v) :=
  P.timeSquareIntegrable_apply g w ρ τ b hq _
    (fun k => WeakSobolevJet.memLp_field (u.sobolevError_L2 hS hν hD C hell s v) k)

end Carleman.PeriodicWeakTrajectory
