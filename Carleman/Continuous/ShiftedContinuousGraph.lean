module

public import Carleman.Continuous.VariableTimeEnergy
public import Carleman.Continuous.VariablePeriodicExistence
public import Carleman.Weights.TemporalDerivatives

/-! The actual paper coefficient μ=(Lq)^(2m): its time graph estimate uses
the already proved derivative ratio and retains q_c and T uniformity. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.TimeWeightRegularity
variable {g : TimeGrid} {w : TimeWeight} {β : ℝ} (h : TimeWeightRegularity w g β)

def shiftMultiplier (m : ℕ) (L : ℝ) (hL : 0 < L) : BoundedMultiplier g.timeMeasure where
  value t := (L*w.q t)^(2*m)
  measurable := (h.aestronglyMeasurable.const_mul L).pow _
  bound := (L*w.max)^(2*m)
  bound_nonneg := pow_nonneg (mul_nonneg hL.le (zero_le_one.trans w.max_ge_one)) _
  bounded := Filter.Eventually.of_forall fun t => by
    rw [abs_of_nonneg (pow_nonneg (mul_nonneg hL.le (w.nonneg t)) _)]
    exact pow_le_pow_left₀ (mul_nonneg hL.le (w.nonneg t))
      (mul_le_mul_of_nonneg_left (w.upper t) hL.le) _

theorem shiftMultiplier_nonneg (m : ℕ) (L : ℝ) (hL : 0 < L) (t : ℝ) :
    0 ≤ (h.shiftMultiplier m L hL).value t :=
  pow_nonneg (mul_nonneg hL.le (w.nonneg t)) _

theorem shiftMultiplier_endpoint (m : ℕ) (L : ℝ) (hL : 0 < L) :
    (h.shiftMultiplier m L hL).value 0 = (h.shiftMultiplier m L hL).value g.period := by
  change (L*w.q 0)^(2*m) = (L*w.q g.period)^(2*m)
  rw [h.endpoint]

theorem shiftMultiplier_derivative {m : ℕ} (hm : 0 < m) {L qc : ℝ} (hL : 0 < L)
    (hqc : 0 < qc) (hlower : ∀ t, qc ≤ w.q t) :
    ∀ᵐ t ∂g.timeMeasure, |deriv (h.shiftMultiplier m L hL).value t| ≤
      ((2*m : ℝ)*β / (L^(2*m)*qc^(2*m-1))) * ((h.shiftMultiplier m L hL).value t)^2 := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hmemb : t ∈ Icc 0 g.period := ⟨ht.1.le, ht.2.le⟩
  have hrate := h.shift_derivative_ratio hm hL hqc hlower hmemb
  have hpos := pow_pos (mul_pos hL (w.pos t)) (2*m)
  have hder : derivWithin (fun x => (L*w.q x)^(2*m)) (Icc 0 g.period) t =
      deriv (fun x => (L*w.q x)^(2*m)) t :=
    derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
  rw [hder] at hrate
  exact (div_le_iff₀ (sq_pos_of_pos hpos)).mp hrate

theorem shiftMultiplier_absolutelyContinuous {m : ℕ} (hm : 0 < m) (L : ℝ) (hL : 0 < L) :
    AbsolutelyContinuousOnInterval (h.shiftMultiplier m L hL).value 0 g.period := by
  let μ := h.shiftMultiplier m L hL
  let δ : ℝ := (2*m : ℝ)*β / L^(2*m)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity [h.beta_pos]
  have hM : 0 ≤ μ.bound := μ.bound_nonneg
  have hd : ∀ t ∈ Icc 0 g.period, HasDerivWithinAt μ.value
      (derivWithin μ.value (Icc 0 g.period) t) (Icc 0 g.period) t := by
    intro t ht
    exact (((h.hasDeriv t ht).const_mul L).fun_pow (2*m)).differentiableWithinAt.hasDerivWithinAt
  have hb : ∀ t ∈ Icc 0 g.period,
      ‖derivWithin μ.value (Icc 0 g.period) t‖ ≤ δ*μ.bound^2 := by
    intro t ht
    have hrate := h.shift_derivative_ratio hm hL zero_lt_one w.lower ht
    simp only [one_pow, mul_one] at hrate
    have hp : 0 < (L*w.q t)^(2*m) := pow_pos (mul_pos hL (w.pos t)) _
    have hlocal : |derivWithin μ.value (Icc 0 g.period) t| ≤ δ*(μ.value t)^2 :=
      (div_le_iff₀ (sq_pos_of_pos hp)).mp hrate
    have hv : μ.value t ≤ μ.bound := pow_le_pow_left₀ (mul_nonneg hL.le (w.nonneg t))
      (mul_le_mul_of_nonneg_left (w.upper t) hL.le) _
    have hv2 := (sq_le_sq₀ (h.shiftMultiplier_nonneg m L hL t) hM).mpr hv
    rw [Real.norm_eq_abs]
    exact hlocal.trans (mul_le_mul_of_nonneg_left hv2 hδ)
  have hLip : LipschitzOnWith (Real.toNNReal (δ*μ.bound^2)) μ.value (Icc 0 g.period) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [Real.coe_toNNReal _ (mul_nonneg hδ (sq_nonneg _)), Real.dist_eq, Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc 0 g.period) hy hx
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  simpa only [uIcc_of_le g.period_pos.le] using hLip

end Carleman.TimeWeightRegularity

namespace Carleman.CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V) (g : TimeGrid) (s : Orientation)

/-- The original μ=(Lq)^(2m), without any dependence of the displayed constant on T or qmax. -/
theorem shifted_periodic_graph_sq {w : TimeWeight} {β : ℝ} (h : TimeWeightRegularity w g β)
    {m : ℕ} (hm : 0 < m) {L qc : ℝ} (hL : 0 < L) (hqc : 0 < qc)
    (hlower : ∀ t, qc ≤ w.q t) (p : b.PeriodicGraph g) :
    ‖p.val.2.1‖^2 + ‖p.val.2.2‖^2 +
      (1-(2*m : ℝ)*β/(L^(2*m)*qc^(2*m-1))) * ‖(h.shiftMultiplier m L hL).map (g.pathL2 p.val.1)‖^2 ≤
      ‖b.evolution g s (h.shiftMultiplier m L hL) p‖^2 :=
  b.variable_periodic_graph_sq g s (h.shiftMultiplier m L hL)
    (Filter.Eventually.of_forall (h.shiftMultiplier_nonneg m L hL))
    (h.shiftMultiplier_absolutelyContinuous hm L hL) (h.shiftMultiplier_endpoint m L hL) _
    (h.shiftMultiplier_derivative hm hL hqc hlower) p

/-- Actual solvability and the three graph terms for every prescribed L² load. -/
theorem shifted_periodic_wellposed {w : TimeWeight} {β : ℝ} (h : TimeWeightRegularity w g β)
    {m : ℕ} (hm : 0 < m) {L qc : ℝ} (hL : 0 < L) (hqc : 0 < qc)
    (hlower : ∀ t, qc ≤ w.q t)
    (hsmall : (2*m : ℝ)*β/(L^(2*m)*qc^(2*m-1)) ≤ 1/2)
    (f : Lp H 2 g.timeMeasure) :
    ∃! p : b.PeriodicGraph g, b.evolution g s (h.shiftMultiplier m L hL) p = f ∧
      ‖p.val.2.1‖^2 + ‖p.val.2.2‖^2 + ‖(h.shiftMultiplier m L hL).map (g.pathL2 p.val.1)‖^2 ≤ 2*‖f‖^2 := by
  obtain ⟨p, hp, huniq⟩ := b.existsUnique_variable_periodic g s (h.shiftMultiplier m L hL)
    (Filter.Eventually.of_forall (h.shiftMultiplier_nonneg m L hL)) f
  refine ⟨p, ⟨hp, ?_⟩, fun q hq => huniq q hq.1⟩
  have he := b.shifted_periodic_graph_sq g s h hm hL hqc hlower p
  rw [hp] at he
  have hh := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖(h.shiftMultiplier m L hL).map (g.pathL2 p.val.1)‖)
  nlinarith [sq_nonneg ‖p.val.2.1‖, sq_nonneg ‖p.val.2.2‖]

end Carleman.CoerciveForm
