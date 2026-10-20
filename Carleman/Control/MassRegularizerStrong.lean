module

public import Carleman.Control.PositiveMassRegularization
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.L2Space

/-! Strong mass regularization from the genuine dense range, including actual Bochner L2 convergence. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology
namespace Carleman
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem positiveMassRegularizer_strong (M : V →L[ℝ] V) (hM : ∀ v, 0 ≤ inner ℝ (M v) v)
    (hdense : DenseRange M) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) (x : V) :
    Tendsto (fun n => positiveMassRegularizer M hM (ε n) (hε n) x) atTop (𝓝 x) := by
  have hrange (v : V) : Tendsto (fun n => ‖M v-positiveMassRegularizer M hM (ε n) (hε n) (M v)‖)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => positiveMassRegularizer_range_error M hM (ε n) (hε n) v)
    simpa only [zero_mul] using hlim.mul_const ‖v‖
  have hn : Tendsto (fun n => ‖x-positiveMassRegularizer M hM (ε n) (hε n) x‖) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    obtain ⟨v,hv⟩ := hdense.exists_dist_lt x (half_pos hδ)
    have hsmall := (hrange v).eventually (gt_mem_nhds (half_pos hδ))
    filter_upwards [hsmall] with n hn
    let R : V →L[ℝ] V := ContinuousLinearMap.id ℝ V-positiveMassRegularizer M hM (ε n) (hε n)
    have he : R x=R (x-M v)+R (M v) := by rw [map_sub]; abel
    have hb : ‖R x‖ ≤ ‖x-M v‖+‖R (M v)‖ := by
      rw [he]
      exact (norm_add_le _ _).trans (add_le_add (positiveMassRegularizer_residual_norm M hM (ε n) (hε n) (x-M v)) le_rfl)
    rw [dist_eq_norm] at hv
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (norm_nonneg _)]
    change ‖R x‖ < δ
    change ‖R (M v)‖ < δ/2 at hn
    linarith
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [norm_sub_rev] using hn

theorem adjoint_mass_denseRange {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (E : V →L[ℝ] H) (hE : Function.Injective E) :
    DenseRange (E.adjoint.comp E) := by
  let M := E.adjoint.comp E
  have ha : M.adjoint=M := by simp only [M,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]
  have hk : M.ker=⊥ := by
    rw [ContinuousLinearMap.ker_adjoint_comp_self]
    exact LinearMap.ker_eq_bot.mpr hE
  change Dense (M.range : Set V)
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  calc
    M.range.topologicalClosure=M.adjoint.range.topologicalClosure := congrArg (fun L : V →L[ℝ] V => L.range.topologicalClosure) ha.symm
    _=M.kerᗮ := M.orthogonal_ker.symm
    _=⊤ := by simp [hk]


omit [CompleteSpace V] in
theorem compLpL_strong_of_contractions {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (L : ℕ → V →L[ℝ] V) (hL : ∀ n v, ‖L n v‖ ≤ ‖v‖)
    (hstrong : ∀ v, Tendsto (fun n => L n v) atTop (𝓝 v)) (Y : Lp V 2 μ) :
    Tendsto (fun n => (L n).compLpL 2 μ Y) atTop (𝓝 Y) := by
  have hnorm : Integrable (fun t => ‖Y t‖^2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp Y).aestronglyMeasurable).mp (Lp.memLp Y)
  have ht : Tendsto (fun n => ∫ t, ‖L n (Y t)-Y t‖^2 ∂μ) atTop (𝓝 0) := by
    have hh := tendsto_integral_of_dominated_convergence (μ := μ) (F := fun n t => ‖L n (Y t)-Y t‖^2)
      (f := fun _ => (0 : ℝ)) (fun t => 4*‖Y t‖^2)
      (fun n => (((L n).continuous.comp_aestronglyMeasurable (Lp.memLp Y).aestronglyMeasurable).sub
        (Lp.memLp Y).aestronglyMeasurable).norm.pow 2)
      (hnorm.const_mul 4) (fun n => Eventually.of_forall (fun t => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        have hb := (norm_sub_le (L n (Y t)) (Y t)).trans (add_le_add (hL n (Y t)) le_rfl)
        nlinarith [norm_nonneg (L n (Y t)-Y t),norm_nonneg (Y t)]))
      (Eventually.of_forall (fun t => by
        simpa only [sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0)] using
          ((hstrong (Y t)).sub (show Tendsto (fun _ : ℕ => Y t) atTop (𝓝 (Y t)) from tendsto_const_nhds)).norm.pow 2))
    simpa only [integral_zero] using hh
  have he n : ‖(L n).compLpL 2 μ Y-Y‖^2=∫ t, ‖L n (Y t)-Y t‖^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((L n).compLpL 2 μ Y) Y,(L n).coeFn_compLpL Y] with t hs hL
    simp only [hs,Pi.sub_apply,hL,real_inner_self_eq_norm_sq]
  have hs : Tendsto (fun n => ‖(L n).compLpL 2 μ Y-Y‖^2) atTop (𝓝 0) := by
    simpa only [he] using ht
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp hs

end Carleman
