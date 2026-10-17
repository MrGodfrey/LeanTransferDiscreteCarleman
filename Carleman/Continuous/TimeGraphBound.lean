module

public import Carleman.Continuous.TimeGraphEnergy

/-! State estimates uniform in T, and the separate period-dependent
complete-graph norm bound needed to construct limits. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V)

theorem time_state_bound {g : TimeGrid} (s : Orientation) (r α : ℝ)
    (hα : ∀ x : b.domain, α * ‖(x : H)‖^2 ≤ inner ℝ (x : H) (b.operator x))
    (p : b.PeriodicGraph g) :
    (α+r) * ‖g.pathL2 p.val.1‖ ≤ ‖b.evolution g s (g.constantMultiplier r) p‖ := by
  let v := g.pathL2 p.val.1
  let f := b.evolution g s (g.constantMultiplier r) p
  have hpos := b.time_graph_positive α hα p
  have he : inner ℝ v f = inner ℝ v p.val.2.2 + r * ‖v‖^2 := by
    dsimp only [f]
    rw [b.evolution_constant, inner_add_right, inner_add_right, real_inner_smul_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq]
    have hz : inner ℝ v p.val.2.1 = 0 := by
      rw [real_inner_comm]
      exact b.periodic_time_inner_zero p
    rw [hz, mul_zero, zero_add]
  have hn := real_inner_le_norm v f
  rw [he] at hn
  rcases eq_or_lt_of_le (norm_nonneg v) with hv | hv
  · change (α+r)*‖v‖ ≤ ‖f‖
    rw [← hv, mul_zero]
    exact norm_nonneg _
  · have hh : ((α+r)*‖v‖)*‖v‖ ≤ ‖f‖*‖v‖ := by nlinarith
    exact (mul_le_mul_iff_left₀ hv).mp hh

theorem periodic_trace_bound {g : TimeGrid} (p : b.PeriodicGraph g) :
    ‖p.val.1‖ ≤ (Real.sqrt g.period / g.period) * ‖g.pathL2 p.val.1‖ +
      Real.sqrt g.period * ‖p.val.2.1‖ := by
  have hT := g.period_pos
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  have hb := p.toTrajectory.weak_derivative.trace_bound p.toTrajectory.continuous
    p.toTrajectory.derivative_L2 t.property
  have hv : (g.memLp_of_continuousOn p.toTrajectory.continuous).toLp p.toTrajectory.value =
      g.pathL2 p.val.1 := by
    apply Lp.ext
    exact (g.memLp_of_continuousOn p.toTrajectory.continuous).coeFn_toLp.trans
      (g.pathL2_ae p.val.1).symm
  have hd : p.toTrajectory.derivative_L2.toLp p.toTrajectory.derivative = p.val.2.1 := by
    apply Lp.ext
    exact p.toTrajectory.derivative_L2.coeFn_toLp
  rw [hv, hd] at hb
  change ‖g.clampPath p.val.1 t‖ ≤ _ at hb
  rw [g.clampPath_on _ _ t.property] at hb
  exact hb

/-- This actual C×L²×L² estimate uses the proved H¹ trace bound.
Its constant may depend on T; the graph and state estimates above do not. -/
theorem regularTimeCore_norm_bound (g : TimeGrid) (s : Orientation) (r : ℝ) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : b.PeriodicGraph g, p ∈ b.regularTimeCore g →
      ‖p‖ ≤ C * ‖b.evolution g s (g.constantMultiplier r) p‖ := by
  have hT := g.period_pos
  obtain ⟨α, hαpos, hα⟩ := b.exists_operator_positive_constant
  let C := Real.sqrt g.period / g.period * α⁻¹ + Real.sqrt g.period + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro p hp
  let F := ‖b.evolution g s (g.constantMultiplier r) p‖
  have hF : 0 ≤ F := norm_nonneg _
  have hg := b.regularTimeCore_graph_sq s r hr p hp
  have hd : ‖p.val.2.1‖ ≤ F := by
    dsimp [F]
    nlinarith [sq_nonneg ‖p.val.2.2‖, mul_nonneg (sq_nonneg r) (sq_nonneg ‖g.pathL2 p.val.1‖),
      norm_nonneg p.val.2.1, hF]
  have ha : ‖p.val.2.2‖ ≤ F := by
    dsimp [F]
    nlinarith [sq_nonneg ‖p.val.2.1‖, mul_nonneg (sq_nonneg r) (sq_nonneg ‖g.pathL2 p.val.1‖),
      norm_nonneg p.val.2.2, hF]
  have hv : ‖g.pathL2 p.val.1‖ ≤ α⁻¹ * F := by
    have hb := b.time_state_bound s r α hα p
    have hvn := norm_nonneg (g.pathL2 p.val.1)
    have hh : α * ‖g.pathL2 p.val.1‖ ≤ F := by nlinarith [mul_nonneg hr hvn]
    exact (le_inv_mul_iff₀ hαpos).mpr hh
  have ht := b.periodic_trace_bound p
  have ht' : ‖p.val.1‖ ≤ C*F := by
    have h₁ := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ Real.sqrt g.period / g.period)
    have h₂ := mul_le_mul_of_nonneg_left hd (Real.sqrt_nonneg g.period)
    dsimp [C]
    nlinarith
  have hC1 : 1 ≤ C := by
    have hh : 0 ≤ Real.sqrt g.period / g.period * α⁻¹ + Real.sqrt g.period := by positivity
    dsimp [C]
    linarith
  have hFC : F ≤ C*F := by nlinarith
  change max ‖p.val.1‖ (max ‖p.val.2.1‖ ‖p.val.2.2‖) ≤ C*F
  exact max_le ht' (max_le (hd.trans hFC) (ha.trans hFC))

end Carleman.CoerciveForm
