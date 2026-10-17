module

public import Carleman.Continuous.RegularTimeCore
public import Carleman.Continuous.WeakPeriodicUnique

/-! Integrated energy and graph bounds for actual time trajectories.
The spatial positivity constant is independent of the period. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V)

omit [CompleteSpace H] [CompleteSpace V] in
theorem exists_operator_positive_constant : ∃ α : ℝ, 0 < α ∧
    ∀ x : b.domain, α * ‖(x : H)‖^2 ≤ inner ℝ (x : H) (b.operator x) := by
  obtain ⟨c, hc, hbound⟩ := b.coercive
  let M : ℝ := ‖b.embed‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨c / M^2, div_pos hc (sq_pos_of_pos hM), ?_⟩
  intro x
  have he : inner ℝ (x : H) (b.operator x) = b.form (b.energy x) (b.energy x) := by
    rw [real_inner_comm, ← b.embed_energy x, b.operator_test]
  have hn : ‖(x : H)‖ ≤ M * ‖b.energy x‖ := by
    rw [← b.embed_energy x]
    exact (b.embed.le_opNorm _).trans (by dsimp [M]; nlinarith [norm_nonneg (b.energy x)])
  have hn2 : ‖(x : H)‖^2 ≤ M^2 * ‖b.energy x‖^2 := by
    calc
      _ ≤ (M * ‖b.energy x‖)^2 := (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg hM.le (norm_nonneg _))).mpr hn
      _ = _ := mul_pow _ _ _
  rw [he, div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_pos hM)]
  have h₁ := mul_le_mul_of_nonneg_left hn2 hc.le
  have h₂ := mul_le_mul_of_nonneg_right (hbound (b.energy x)) (sq_nonneg M)
  nlinarith

omit [CompleteSpace H] in
theorem time_graph_positive {g : TimeGrid} (α : ℝ)
    (hα : ∀ x : b.domain, α * ‖(x : H)‖^2 ≤ inner ℝ (x : H) (b.operator x))
    (p : b.PeriodicGraph g) :
    α * ‖g.pathL2 p.val.1‖^2 ≤ inner ℝ (g.pathL2 p.val.1) p.val.2.2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def, ← integral_const_mul]
  apply integral_mono_ae
    ((L2.integrable_inner (g.pathL2 p.val.1) (g.pathL2 p.val.1)).const_mul α)
    (L2.integrable_inner (g.pathL2 p.val.1) p.val.2.2)
  have hg := (b.timeOperatorGraph_ae g.timeMeasure _ _).mp
    ((b.periodicGraph_mem g p.val).mp p.property).2.1
  filter_upwards [hg] with t ht
  obtain ⟨x, hx, ha⟩ := (b.operatorGraph_mem _ _).mp ht
  rw [← hx, ← ha, real_inner_self_eq_norm_sq]
  exact hα x

theorem periodic_time_inner_zero {g : TimeGrid} (p : b.PeriodicGraph g) :
    inner ℝ p.val.2.1 (g.pathL2 p.val.1) = 0 := by
  rw [L2.inner_def]
  calc
    _ = ∫ t, inner ℝ (p.toTrajectory.value t) (p.toTrajectory.derivative t) ∂g.timeMeasure := by
      apply integral_congr_ae
      filter_upwards [g.pathL2_ae p.val.1] with t ht
      rw [ht, real_inner_comm]
      rfl
    _ = 0 := p.toTrajectory.time_energy_zero

/-- Symmetry cancels the time/operator cross term on the actual classical approximation core. -/
theorem regularTimeCore_cross_zero {g : TimeGrid} (p : b.PeriodicGraph g)
    (hp : p ∈ b.regularTimeCore g) : inner ℝ p.val.2.1 p.val.2.2 = 0 := by
  obtain ⟨U, dU, hU, hdU, hder, htrace⟩ := hp
  have hfields := b.regularTimeCore_fields p U dU hU hdU hder htrace
  have hper : U 0 = U g.period := by
    apply b.graphH_injective
    rw [← htrace ⟨0, ⟨le_rfl, g.period_pos.le⟩⟩,
      ← htrace ⟨g.period, ⟨g.period_pos.le, le_rfl⟩⟩]
    exact ((b.periodicGraph_mem g p.val).mp p.property).2.2
  have hD (t : ℝ) : HasDerivAt (fun t => inner ℝ (b.graphH (U t)) (b.graphA (U t)))
      (2 * inner ℝ (b.graphH (dU t)) (b.graphA (U t))) t := by
    have he := (b.graphH.hasFDerivAt.comp_hasDerivAt t (hder t)).inner ℝ
      (b.graphA.hasFDerivAt.comp_hasDerivAt t (hder t))
    simp only [Function.comp_apply] at he
    have hs := b.graph_symmetric (U t) (dU t)
    have heq : inner ℝ (b.graphH (U t)) (b.graphA (dU t)) =
        inner ℝ (b.graphH (dU t)) (b.graphA (U t)) := hs.symm.trans (real_inner_comm _ _)
    rw [heq, ← two_mul] at he
    exact he
  have hcont : Continuous (fun t => 2 * inner ℝ (b.graphH (dU t)) (b.graphA (U t))) :=
    continuous_const.mul ((b.graphH.continuous.comp hdU).inner (b.graphA.continuous.comp hU))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := g.period) (fun t _ => hD t)
    hcont.continuousOn.intervalIntegrable
  rw [← hper, sub_self, ← g.timeIntegral_eq_intervalIntegral, integral_const_mul] at he
  have hz : (∫ t, inner ℝ (b.graphH (dU t)) (b.graphA (U t)) ∂g.timeMeasure) = 0 := by linarith
  calc
    _ = ∫ t, inner ℝ (b.graphH (dU t)) (b.graphA (U t)) ∂g.timeMeasure := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hfields.2.1, hfields.2.2] with t hd ha
      rw [hd, ha]
    _ = 0 := hz

theorem evolution_constant (g : TimeGrid) (s : Orientation) (r : ℝ) (p : b.PeriodicGraph g) :
    b.evolution g s (g.constantMultiplier r) p =
      s.sign • p.val.2.1 + p.val.2.2 + r • g.pathL2 p.val.1 := by
  apply Lp.ext
  filter_upwards [b.evolution_ae g s (g.constantMultiplier r) p,
    Lp.coeFn_add (s.sign • p.val.2.1 + p.val.2.2) (r • g.pathL2 p.val.1),
    Lp.coeFn_add (s.sign • p.val.2.1) p.val.2.2, Lp.coeFn_smul s.sign p.val.2.1,
    Lp.coeFn_smul r (g.pathL2 p.val.1), g.pathL2_ae p.val.1, p.toTrajectory_operator_ae]
    with t he ht hsum hd hv hval ha
  simp only [Pi.add_apply, Pi.smul_apply] at ht hsum hd hv
  rw [he, ht, hsum, hd, hv, hval, ← ha]
  rfl

theorem regularTimeCore_graph_sq {g : TimeGrid} (s : Orientation) (r : ℝ) (hr : 0 ≤ r)
    (p : b.PeriodicGraph g) (hp : p ∈ b.regularTimeCore g) :
    ‖p.val.2.1‖^2 + ‖p.val.2.2‖^2 + r^2 * ‖g.pathL2 p.val.1‖^2 ≤
      ‖b.evolution g s (g.constantMultiplier r) p‖^2 := by
  have hs : s.sign^2 = 1 := by cases s <;> norm_num [Carleman.Orientation.sign]
  have hnon : 0 ≤ inner ℝ p.val.2.2 (g.pathL2 p.val.1) := by
    rw [real_inner_comm]
    simpa only [zero_mul] using b.time_graph_positive 0 (fun x => by
      simpa only [zero_mul, real_inner_comm] using b.operator_nonneg x) p
  rw [b.evolution_constant]
  simp only [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hs,
    one_mul, inner_add_left, real_inner_smul_left, real_inner_smul_right,
    b.regularTimeCore_cross_zero p hp, b.periodic_time_inner_zero p]
  nlinarith [mul_nonneg hr hnon]

end Carleman.CoerciveForm
