module

public import Carleman.Control.TimeTestDifference
public import Mathlib.Analysis.Calculus.MeanValue

/-! Left endpoint samples on the original cells: a quantitative error bound and strong consistency for C¹ interval tests. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology BigOperators NNReal
namespace Carleman

theorem time_test_left_sample_error (T : ℝ) (g : TimeGrid) (hT : g.period=T)
    (φ : ℝ → ℝ) (hφLp : MemLp φ 2 (volume.restrict (Ioc 0 T)))
    {C : ℝ≥0} (hφ : LipschitzOnWith C φ (Icc 0 T)) :
    ‖hφLp.toLp φ-fixedTimeCellReconstruction T g hT (fun i => φ (g.nodeTime i))‖
      ≤ C*g.dt*Real.sqrt T := by
  let μ := volume.restrict (Ioc 0 T)
  let u := hφLp.toLp φ
  let v : PhysicalFiniteSpace (Fin g.steps) g.dt g.dt_pos :=
    PhysicalFiniteSpace.valuesEquiv.symm (fun i => φ (g.nodeTime i))
  have hTpos : 0 ≤ T := hT ▸ g.period_pos.le
  have hn i : g.nodeTime i ∈ Icc 0 T := by
    refine ⟨g.nodeTime_nonneg i, ?_⟩
    rw [← hT]
    dsimp [TimeGrid.nodeTime,TimeGrid.period]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast i.isLt.le) g.dt_pos.le
  have hl i : ∀ᵐ t ∂μ, t ∈ g.physicalTimeCell i → |u t-v i| ≤ C*g.dt := by
    filter_upwards [hφLp.coeFn_toLp] with t ht hti
    change |u t-φ (g.nodeTime i)| ≤ _
    rw [ht]
    have hdom := g.physicalTimeCell_subset i hti
    have htm : t ∈ Icc 0 T := ⟨hdom.1.le,hT ▸ hdom.2⟩
    have hdist : dist t (g.nodeTime i) ≤ g.dt := by
      rw [Real.dist_eq,abs_of_pos (sub_pos.mpr hti.1)]
      linarith [hti.2]
    exact (hφ.dist_le_mul t htm (g.nodeTime i) (hn i)).trans
      (mul_le_mul_of_nonneg_left hdist C.coe_nonneg)
  have hb : ∀ᵐ t ∂μ, |u t| ≤ |φ 0|+C*T := by
    filter_upwards [hφLp.coeFn_toLp,ae_restrict_mem measurableSet_Ioc] with t ht htm
    rw [ht]
    have hd := hφ.dist_le_mul t ⟨htm.1.le,htm.2⟩ 0 ⟨le_rfl,hTpos⟩
    simp only [Real.dist_eq,sub_zero,abs_of_pos htm.1] at hd
    have hb := mul_le_mul_of_nonneg_left htm.2 C.coe_nonneg
    have ha : |φ t| ≤ |φ t-φ 0|+|φ 0| := by
      simpa only [sub_add_cancel] using abs_add_le (φ t-φ 0) (φ 0)
    linarith
  have he := finiteCellLinear_error_bound g.physicalTimeCell (fun _ => measurableSet_Ioc) g.dt_pos
    g.physicalTimeCell_disjoint v u (mul_nonneg C.coe_nonneg g.dt_pos.le)
      (add_nonneg (abs_nonneg _) (mul_nonneg C.coe_nonneg hTpos)) hl hb
  rw [fixedTimeCell_uncovered_volume T hTpos g hT,mul_zero,add_zero] at he
  have hm : μ.real univ=T := by
    simp only [μ,Measure.real,Measure.restrict_apply_univ]
    rw [← Measure.real,Real.volume_real_Ioc_of_le hTpos,sub_zero]
  rw [hm] at he
  have heq : finiteCellLinear (ν := μ) g.physicalTimeCell (fun _ => measurableSet_Ioc) g.dt_pos v=
      fixedTimeCellReconstruction T g hT (fun i => φ (g.nodeTime i)) :=
    fixedTimeCellIsometry_eq_reconstruction T g hT v
  rw [heq] at he
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg C.coe_nonneg g.dt_pos.le) (Real.sqrt_nonneg T))).mp
  simpa only [mul_pow,Real.sq_sqrt hTpos] using he

theorem time_test_left_sample_strong_convergence (T : ℝ)
    (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (htlim : Tendsto (fun n => (g n).dt) atTop (𝓝 0))
    (φ : ℝ → ℝ) (hφLp : MemLp φ 2 (volume.restrict (Ioc 0 T)))
    {C : ℝ≥0} (hφ : LipschitzOnWith C φ (Icc 0 T)) :
    Tendsto (fun n => fixedTimeCellReconstruction T (g n) (hT n)
      (fun i => φ ((g n).nodeTime i))) atTop (𝓝 (hφLp.toLp φ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => (norm_sub_rev _ _).trans_le (time_test_left_sample_error T (g n) (hT n) φ hφLp hφ))
  simpa only [mul_zero,zero_mul] using (tendsto_const_nhds.mul htlim).mul_const (Real.sqrt T)

theorem continuous_time_memLp (T : ℝ) (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Icc 0 T)) :
    MemLp φ 2 (volume.restrict (Ioc 0 T)) := by
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ
  apply MemLp.of_bound (hφ.mono Ioc_subset_Icc_self |>.aestronglyMeasurable measurableSet_Ioc) B
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact hB t (Ioc_subset_Icc_self ht)

theorem time_test_lipschitz (T : ℝ) (φ f : ℝ → ℝ)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt φ (f t) (Icc 0 T) t) (hf : ContinuousOn f (Icc 0 T)) :
    ∃ C : ℝ≥0, LipschitzOnWith C φ (Icc 0 T) := by
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine ⟨⟨max 0 B,le_max_left _ _⟩, ?_⟩
  apply (convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => hd t ht)
  intro t ht
  exact_mod_cast (hB t ht).trans (le_max_right 0 B)

theorem smooth_time_test_consistency (T : ℝ) (hTpos : 0 ≤ T)
    (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (htlim : Tendsto (fun n => (g n).dt) atTop (𝓝 0))
    (φ f : ℝ → ℝ) (hφ : ContinuousOn φ (Icc 0 T)) (hf : ContinuousOn f (Icc 0 T))
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt φ (f t) (Icc 0 T) t) :
    Tendsto (fun n => fixedTimeCellReconstruction T (g n) (hT n)
      (fun i => φ ((g n).nodeTime i))) atTop (𝓝 ((continuous_time_memLp T φ hφ).toLp φ)) ∧
    Tendsto (fun n => fixedTimeCellReconstruction T (g n) (hT n)
      (fun i => (g n).dt⁻¹*(φ (((i.val:ℝ)+1)*(g n).dt)-φ ((i.val:ℝ)*(g n).dt))))
      atTop (𝓝 ((continuous_time_memLp T f hf).toLp f)) := by
  obtain ⟨C,hC⟩ := time_test_lipschitz T φ f hd hf
  exact ⟨time_test_left_sample_strong_convergence T g hT htlim φ (continuous_time_memLp T φ hφ) hC,
    time_test_difference_strong_convergence T hTpos g hT htlim φ f (continuous_time_memLp T f hf) hd⟩

end Carleman
