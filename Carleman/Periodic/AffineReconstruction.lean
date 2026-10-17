module

public import Carleman.Continuous.EulerTimeEmbedding
public import Carleman.Continuous.WeakTimeProduct
public import Carleman.Periodic.CellAnchor

/-! The genuine periodic affine interpolant of every H-valued grid state.
It is constructed as a Bochner primitive. Cell formulas, endpoint traces and
its H-valued weak derivative are proved; no operator-domain regularity is used. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
open Fin.NatCast
namespace Carleman.TimeGrid
variable (g : TimeGrid) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

def forwardSlope (u : g.Sequence H) : g.Sequence H :=
  fun i => g.dt⁻¹ • (u (g.next i) - u i)

def affineReconstruction (u : g.Sequence H) (t : ℝ) : H :=
  u 0 + ∫ x in 0..t, g.extensionMinus (g.forwardSlope u) x

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem intervalIntegrable_extensionMinus_vector_cell (v : g.Sequence H) (n : ℕ) :
    IntervalIntegrable (g.extensionMinus v) volume (g.cellTime n) (g.cellTime (n+1)) := by
  apply intervalIntegrable_const.congr_uIoo
  rw [uIoo_of_le (g.cellTime_lt_succ n).le]
  intro t ht
  exact (g.extensionMinus_on_open_cell v n ht).symm

theorem affineReconstruction_node (u : g.Sequence H) (n : ℕ) :
    g.affineReconstruction u (g.cellTime n) = u (n : g.Index) := by
  induction n with
  | zero => simp [affineReconstruction, cellTime]
  | succ n ih =>
    have hi := IntervalIntegrable.trans_iterate (n := n)
      (fun k _ => g.intervalIntegrable_extensionMinus_vector_cell (g.forwardSlope u) k)
    have h0 : g.cellTime 0 = 0 := by simp [cellTime]
    rw [h0] at hi
    have hc := g.intervalIntegrable_extensionMinus_vector_cell (g.forwardSlope u) n
    have he := intervalIntegral.integral_add_adjacent_intervals hi hc
    have hp : (∫ t in g.cellTime n..g.cellTime (n+1), g.extensionMinus (g.forwardSlope u) t) =
        u ((n+1 : ℕ) : g.Index) - u (n : g.Index) := by
      rw [intervalIntegral.integral_congr_Ioo_of_le (g.cellTime_lt_succ n).le
        (fun t ht => g.extensionMinus_on_open_cell (g.forwardSlope u) n ht),
        intervalIntegral.integral_const, g.cellTime_succ_sub]
      simp only [forwardSlope, smul_smul, mul_inv_cancel₀ (ne_of_gt g.dt_pos), one_smul,
        g.next_eq_add_one, Nat.cast_add, Nat.cast_one]
    rw [hp] at he
    change u 0 + _ = _
    rw [← he, ← add_assoc]
    change g.affineReconstruction u (g.cellTime n) + _ = _
    rw [ih]
    abel

theorem affineReconstruction_cell (u : g.Sequence H) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (g.cellTime n) (g.cellTime (n+1))) :
    g.affineReconstruction u t = u (n : g.Index) +
      (t-g.cellTime n) • g.forwardSlope u (n : g.Index) := by
  have hi := IntervalIntegrable.trans_iterate (n := n)
    (fun k _ => g.intervalIntegrable_extensionMinus_vector_cell (g.forwardSlope u) k)
  have h0 : g.cellTime 0 = 0 := by simp [cellTime]
  rw [h0] at hi
  have hc := (g.intervalIntegrable_extensionMinus_vector_cell (g.forwardSlope u) n).mono_set
    (show uIcc (g.cellTime n) t ⊆ uIcc (g.cellTime n) (g.cellTime (n+1)) by
      rw [uIcc_of_le ht.1, uIcc_of_le (g.cellTime_lt_succ n).le]
      exact Icc_subset_Icc le_rfl ht.2)
  have he := intervalIntegral.integral_add_adjacent_intervals hi hc
  have hp : (∫ x in g.cellTime n..t, g.extensionMinus (g.forwardSlope u) x) =
      (t-g.cellTime n) • g.forwardSlope u (n : g.Index) := by
    rw [intervalIntegral.integral_congr_Ioo_of_le ht.1 (fun x hx =>
      g.extensionMinus_on_open_cell (g.forwardSlope u) n ⟨hx.1, hx.2.trans_le ht.2⟩),
      intervalIntegral.integral_const]
  rw [hp] at he
  change u 0 + _ = _
  rw [← he, ← add_assoc]
  exact congrArg (fun x => x + _) (g.affineReconstruction_node u n)

omit [CompleteSpace H] in
theorem affineReconstruction_continuousOn (u : g.Sequence H) :
    ContinuousOn (g.affineReconstruction u) (Icc 0 g.period) :=
  continuousOn_const.add (TimeGrid.primitive_continuousOn (Orientation.minus.memLp_extension g (g.forwardSlope u)))

theorem affineReconstruction_periodic_trace (u : g.Sequence H) :
    g.affineReconstruction u 0 = g.affineReconstruction u g.period := by
  have hn := g.affineReconstruction_node u g.steps
  have h0 := g.affineReconstruction_node u 0
  simpa only [cellTime, Nat.cast_zero, Fin.natCast_self, zero_mul] using
    (h0.trans (by simpa [cellTime, period] using hn.symm))

theorem affineReconstruction_weakDerivative (u : g.Sequence H) :
    HasWeakTimeDerivative g (g.affineReconstruction u) (g.extensionMinus (g.forwardSlope u)) := by
  have hm := Orientation.minus.memLp_extension g (g.forwardSlope u)
  have hp := HasWeakTimeDerivative.primitive hm
  have hc : HasWeakTimeDerivative g (fun _ => u 0) (fun _ => 0) :=
    HasWeakTimeDerivative.of_hasDerivAt continuousOn_const (fun t _ => hasDerivAt_const t _)
      intervalIntegrable_const
  intro φ hφ hcompact hsupp
  have hφm := g.memLp_of_continuousOn (hφ.continuous_deriv (by simp)).continuousOn
  have hi1 := memLp_one_iff_integrable.mp (hφm.smul (g.memLp_of_continuousOn
    (show ContinuousOn (fun _ : ℝ => u 0) (Icc 0 g.period) from continuousOn_const)))
  have hi2 := memLp_one_iff_integrable.mp (hφm.smul (g.memLp_of_continuousOn
    (TimeGrid.primitive_continuousOn hm)))
  change Integrable (fun t => deriv φ t • u 0) g.timeMeasure at hi1
  change Integrable (fun t => deriv φ t • ∫ x in 0..t, g.extensionMinus (g.forwardSlope u) x) g.timeMeasure at hi2
  simp only [Orientation.extension] at hp
  simp only [affineReconstruction, smul_add]
  rw [integral_add hi1 hi2, hc φ hφ hcompact hsupp, hp φ hφ hcompact hsupp]
  simp

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Grid nodes form a null set; every remaining time belongs to a genuine open cell. -/
theorem ae_open_cell : ∀ᵐ t ∂g.timeMeasure, ∃ n : ℕ, n < g.steps ∧
    t ∈ Ioo (g.cellTime n) (g.cellTime (n+1)) := by
  have hz : ∀ᵐ t ∂volume, t ∉ Set.range g.cellTime := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using (Set.countable_range g.cellTime).measure_zero volume
  filter_upwards [ae_restrict_of_ae hz, ae_restrict_mem measurableSet_Ioo] with t ht hm
  let n := ⌊t/g.dt⌋₊
  have hnon := div_nonneg hm.1.le g.dt_pos.le
  have hn : n < g.steps := (Nat.floor_lt hnon).mpr ((div_lt_iff₀ g.dt_pos).mpr hm.2)
  have hlo : g.cellTime n ≤ t := (le_div_iff₀ g.dt_pos).mp (Nat.floor_le hnon)
  have hhi : t < g.cellTime (n+1) := by
    have hh := (div_lt_iff₀ g.dt_pos).mp (Nat.lt_floor_add_one (t/g.dt))
    simpa only [cellTime, Nat.cast_add, Nat.cast_one] using hh
  exact ⟨n, hn, lt_of_le_of_ne hlo (fun he => ht ⟨n, he⟩), hhi⟩

omit [CompleteSpace H] in
theorem forwardSlope_step (u : g.Sequence H) (n : ℕ) :
    u ((n+1 : ℕ) : g.Index) = u (n : g.Index) + g.dt • g.forwardSlope u (n : g.Index) := by
  simp only [forwardSlope, smul_smul, mul_inv_cancel₀ (ne_of_gt g.dt_pos), one_smul,
    g.next_eq_add_one, Nat.cast_add, Nat.cast_one]
  abel

end Carleman.TimeGrid

namespace Carleman.Orientation
variable (s : Orientation) (g : TimeGrid) {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem signed_difference_on_open_cell (u : g.Sequence H) (n : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (g.cellTime n) (g.cellTime (n+1))) :
    s.sign • s.extension g (s.difference g u) t = g.forwardSlope u (n : g.Index) := by
  cases s
  · change (1:ℝ) • g.extensionPlus (g.dPlus u) t = _
    rw [one_smul, g.extensionPlus_on_open_cell _ n ht]
    simp only [TimeGrid.dPlus, TimeGrid.forwardSlope, g.prev_eq_sub_one, g.next_eq_add_one,
      Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  · change (-1:ℝ) • g.extensionMinus (g.dMinus u) t = _
    rw [g.extensionMinus_on_open_cell _ n ht]
    simp only [TimeGrid.dMinus, TimeGrid.forwardSlope, neg_one_smul, ← smul_neg, neg_sub]

omit [CompleteSpace H] in
/-- The actual affine derivative is epsilon times the correct half-open difference. -/
theorem signed_difference_ae (u : g.Sequence H) :
    (fun t => s.sign • s.extension g (s.difference g u) t) =ᵐ[g.timeMeasure]
      g.extensionMinus (g.forwardSlope u) := by
  filter_upwards [g.ae_open_cell] with t ht
  obtain ⟨n, _, hn⟩ := ht
  rw [s.signed_difference_on_open_cell g u n hn, g.extensionMinus_on_open_cell _ n hn]

theorem affine_defect_on_open_cell (u : g.Sequence H) (n : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (g.cellTime n) (g.cellTime (n+1))) :
    ‖g.affineReconstruction u t - s.extension g u t‖ ≤
      g.dt * ‖s.extension g (s.difference g u) t‖ := by
  have hnorm : ‖s.extension g (s.difference g u) t‖ = ‖g.forwardSlope u (n : g.Index)‖ := by
    have he := congrArg norm (s.signed_difference_on_open_cell g u n ht)
    simpa only [norm_smul, Real.norm_eq_abs, show |s.sign|=1 by cases s <;> norm_num [sign], one_mul] using he
  rw [hnorm, g.affineReconstruction_cell u n ⟨ht.1.le,ht.2.le⟩]
  cases s
  · rw [extension, g.extensionPlus_on_open_cell u n ht, g.forwardSlope_step u n]
    rw [add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_eq_abs]
    have hb : |t-g.cellTime n-g.dt| ≤ g.dt := by
      have hd := g.cellTime_succ_sub n
      exact abs_le.mpr ⟨by linarith [ht.1], by linarith [g.dt_pos, ht.2]⟩
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  · rw [extension, g.extensionMinus_on_open_cell u n ht, add_sub_cancel_left,
      norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr ht.1)]
    exact mul_le_mul_of_nonneg_right (by linarith [g.cellTime_succ_sub n, ht.2]) (norm_nonneg _)

/-- Sharp order-dt interpolation defect for all states, both orientations, uniformly in T. -/
theorem affine_defect_ae (u : g.Sequence H) :
    ∀ᵐ t ∂g.timeMeasure, ‖g.affineReconstruction u t - s.extension g u t‖ ≤
      g.dt * ‖s.extension g (s.difference g u) t‖ := by
  filter_upwards [g.ae_open_cell] with t ht
  obtain ⟨n, _, hn⟩ := ht
  exact s.affine_defect_on_open_cell g u n hn

end Carleman.Orientation
