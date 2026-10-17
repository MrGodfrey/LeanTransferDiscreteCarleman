module

public import Carleman.Transfer.Weights
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Function.Floor

/-! Exact integration of the existing two half-open periodic extensions. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
open Fin.NatCast Fin.IntCast
namespace Carleman.TimeGrid
variable (g : Carleman.TimeGrid)

/-- Cell endpoints before reduction modulo N; the endpoint N is T. -/
def cellTime (n : ℕ) : ℝ := (n : ℝ) * g.dt

theorem cellTime_succ_sub (n : ℕ) : g.cellTime (n+1) - g.cellTime n = g.dt := by
  simp only [cellTime, Nat.cast_add, Nat.cast_one]
  ring

theorem cellTime_lt_succ (n : ℕ) : g.cellTime n < g.cellTime (n+1) := by
  have := g.cellTime_succ_sub n
  linarith [g.dt_pos]

theorem extensionPlus_on_open_cell {E : Type*} (u : g.Sequence E) (n : ℕ)
    {t : ℝ} (ht : t ∈ Ioo (g.cellTime n) (g.cellTime (n+1))) :
    g.extensionPlus u t = u (↑(n+1) : g.Index) := by
  have h := g.extensionPlus_on_cell u (n+1 : ℕ) t (by
    constructor
    · simpa [cellTime, Nat.cast_add, Nat.cast_one] using ht.1
    · simpa [cellTime] using ht.2.le)
  change g.extensionPlus u t = u (Fin.intCast (↑(n+1 : ℕ))) at h
  simpa only [Fin.intCast, Int.natCast_nonneg, ite_eq_left, Int.natAbs_natCast, Fin.ofNat_eq_cast] using h

theorem extensionMinus_on_open_cell {E : Type*} (u : g.Sequence E) (n : ℕ)
    {t : ℝ} (ht : t ∈ Ioo (g.cellTime n) (g.cellTime (n+1))) :
    g.extensionMinus u t = u (↑n : g.Index) := by
  have h := g.extensionMinus_on_cell u (n : ℤ) t (by
    constructor
    · simpa [cellTime] using ht.1.le
    · simpa [cellTime, Nat.cast_add, Nat.cast_one] using ht.2)
  simpa [Fin.intCast] using h

theorem intervalIntegrable_extensionPlus_cell (u : g.Sequence ℝ) (n : ℕ) :
    IntervalIntegrable (g.extensionPlus u) volume (g.cellTime n) (g.cellTime (n+1)) := by
  apply intervalIntegrable_const.congr_uIoo
  rw [uIoo_of_le (g.cellTime_lt_succ n).le]
  intro t ht
  exact (g.extensionPlus_on_open_cell u n ht).symm

theorem intervalIntegrable_extensionMinus_cell (u : g.Sequence ℝ) (n : ℕ) :
    IntervalIntegrable (g.extensionMinus u) volume (g.cellTime n) (g.cellTime (n+1)) := by
  apply intervalIntegrable_const.congr_uIoo
  rw [uIoo_of_le (g.cellTime_lt_succ n).le]
  intro t ht
  exact (g.extensionMinus_on_open_cell u n ht).symm

theorem integral_extensionPlus_cell (u : g.Sequence ℝ) (n : ℕ) :
    (∫ t in g.cellTime n..g.cellTime (n+1), g.extensionPlus u t) =
      g.dt * u (↑(n+1) : g.Index) := by
  rw [intervalIntegral.integral_congr_Ioo_of_le (g.cellTime_lt_succ n).le
    (fun t ht => g.extensionPlus_on_open_cell u n ht), intervalIntegral.integral_const,
    g.cellTime_succ_sub, smul_eq_mul]

theorem integral_extensionMinus_cell (u : g.Sequence ℝ) (n : ℕ) :
    (∫ t in g.cellTime n..g.cellTime (n+1), g.extensionMinus u t) =
      g.dt * u (↑n : g.Index) := by
  rw [intervalIntegral.integral_congr_Ioo_of_le (g.cellTime_lt_succ n).le
    (fun t ht => g.extensionMinus_on_open_cell u n ht), intervalIntegral.integral_const,
    g.cellTime_succ_sub, smul_eq_mul]

theorem integrable_extensionPlus (u : g.Sequence ℝ) :
    Integrable (g.extensionPlus u) g.timeMeasure := by
  have h := IntervalIntegrable.trans_iterate (n := g.steps)
    (fun n _ => g.intervalIntegrable_extensionPlus_cell u n)
  have h0 : g.cellTime 0 = 0 := by simp [cellTime]
  have hN : g.cellTime g.steps = g.period := rfl
  rw [h0, hN] at h
  exact h.1.mono_set Ioo_subset_Ioc_self

theorem integrable_extensionMinus (u : g.Sequence ℝ) :
    Integrable (g.extensionMinus u) g.timeMeasure := by
  have h := IntervalIntegrable.trans_iterate (n := g.steps)
    (fun n _ => g.intervalIntegrable_extensionMinus_cell u n)
  have h0 : g.cellTime 0 = 0 := by simp [cellTime]
  have hN : g.cellTime g.steps = g.period := rfl
  rw [h0, hN] at h
  exact h.1.mono_set Ioo_subset_Ioc_self

theorem integral_extensionPlus (u : g.Sequence ℝ) :
    (∫ t, g.extensionPlus u t ∂g.timeMeasure) = g.dt * ∑ i, u i := by
  change (∫ t in Ioo 0 g.period, g.extensionPlus u t) = _
  rw [MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
  rw [← intervalIntegral.integral_of_le g.period_pos.le]
  have h := intervalIntegral.sum_integral_adjacent_intervals (n := g.steps)
    (fun n _ => g.intervalIntegrable_extensionPlus_cell u n)
  have h0 : g.cellTime 0 = 0 := by simp [cellTime]
  have hN : g.cellTime g.steps = g.period := rfl
  rw [h0, hN] at h
  rw [← h]
  simp_rw [g.integral_extensionPlus_cell]
  rw [← Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
  congr 1
  have he : (fun i : g.Index => u (↑(i.val+1) : g.Index)) = fun i => u (g.next i) := by
    funext i
    rw [g.next_eq_add_one, Nat.cast_add, Nat.cast_one, Fin.cast_val_eq_self]
  rw [he]
  exact Equiv.sum_comp g.next u

theorem integral_extensionMinus (u : g.Sequence ℝ) :
    (∫ t, g.extensionMinus u t ∂g.timeMeasure) = g.dt * ∑ i, u i := by
  change (∫ t in Ioo 0 g.period, g.extensionMinus u t) = _
  rw [MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
  rw [← intervalIntegral.integral_of_le g.period_pos.le]
  have h := intervalIntegral.sum_integral_adjacent_intervals (n := g.steps)
    (fun n _ => g.intervalIntegrable_extensionMinus_cell u n)
  have h0 : g.cellTime 0 = 0 := by simp [cellTime]
  have hN : g.cellTime g.steps = g.period := rfl
  rw [h0, hN] at h
  rw [← h]
  simp_rw [g.integral_extensionMinus_cell]
  rw [← Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
  simp only [Fin.cast_val_eq_self]

end Carleman.TimeGrid

namespace Carleman.Orientation
variable (s : Orientation) (g : TimeGrid)

/-- The cell selector itself is measurable; this also handles the wrap at T. -/
theorem measurable_cell_index : Measurable (s.extension g (fun i => i)) := by
  cases s
  · exact (measurable_of_countable (Fin.intCast : ℤ → g.Index)).comp
      (Int.measurable_ceil.comp (measurable_id.div_const g.dt))
  · exact (measurable_of_countable (Fin.intCast : ℤ → g.Index)).comp
      (Int.measurable_floor.comp (measurable_id.div_const g.dt))

/-- A finite cell selection of measurable time families is measurable. -/
theorem aestronglyMeasurable_cell_select (f : g.Index → ℝ → ℝ)
    (hf : ∀ i, AEStronglyMeasurable (f i) g.timeMeasure) :
    AEStronglyMeasurable (fun t => f (s.extension g (fun i => i) t) t) g.timeMeasure := by
  let j := s.extension g (fun i => i)
  have hs : ∀ i, MeasurableSet {t | j t = i} := fun i =>
    (s.measurable_cell_index g) (measurableSet_singleton i)
  have he : (fun t => f (j t) t) =
      (fun t => ∑ i : g.Index, ({t | j t = i}.indicator (f i)) t) := by
    funext t
    simp [Set.indicator, eq_comm]
  rw [he]
  exact Finset.univ.aestronglyMeasurable_fun_sum fun i _ => (hf i).indicator (hs i)

theorem integral_extension (u : g.Sequence ℝ) :
    (∫ t, s.extension g u t ∂g.timeMeasure) = g.dt * ∑ i, u i := by
  cases s
  · exact g.integral_extensionPlus u
  · exact g.integral_extensionMinus u

theorem integrable_extension (u : g.Sequence ℝ) :
    Integrable (s.extension g u) g.timeMeasure := by
  cases s
  · exact g.integrable_extensionPlus u
  · exact g.integrable_extensionMinus u

/-- Exact frozen-node norm identity, before comparing a varying continuous weight. -/
theorem integral_frozen_weightedSq {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : g.Index → Seminorm ℝ E) (u : g.Sequence E) :
    (∫ t, ((s.extension g p t) (s.extension g u t)) ^ 2 ∂g.timeMeasure) = g.weightedSq p u := by
  have h : (fun t => ((s.extension g p t) (s.extension g u t)) ^ 2) =
      s.extension g (fun i => (p i (u i)) ^ 2) := by cases s <;> rfl
  rw [h, s.integral_extension]
  rfl
/-- Finiteness of the frozen density is proved, not a comparison premise. -/
theorem integrable_frozen_density {E : Type*} [AddCommGroup E] [Module ℝ E]
    (q : g.Sequence ℝ) (a : ℝ) (p : g.Index → Seminorm ℝ E) (u : g.Sequence E) :
    TimeSquareIntegrable g (s.extension g q) a (s.extension g p) (s.extension g u) := by
  have h : timeDensity (s.extension g q) a (s.extension g p) (s.extension g u) =
      s.extension g (fun i => q i ^ a * (p i (u i)) ^ 2) := by cases s <;> rfl
  unfold TimeSquareIntegrable
  rw [h]
  exact s.integrable_extension g _

theorem timeSq_frozen_eq_powerSq {E : Type*} [AddCommGroup E] [Module ℝ E]
    (q : g.Sequence ℝ) (a : ℝ) (p : g.Index → Seminorm ℝ E) (u : g.Sequence E) :
    timeSq g (s.extension g q) a (s.extension g p) (s.extension g u) =
      g.powerSq q a p u := by
  have h : timeDensity (s.extension g q) a (s.extension g p) (s.extension g u) =
      s.extension g (fun i => q i ^ a * (p i (u i)) ^ 2) := by cases s <;> rfl
  unfold timeSq
  rw [h, s.integral_extension]
  rfl
end Carleman.Orientation
