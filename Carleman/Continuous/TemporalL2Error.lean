module

public import Carleman.Continuous.TemporalErrorIdentity
public import Carleman.Continuous.FrozenContinuousGraph

/-! The first genuine time-discretization error estimate. The continuous and
Euler solutions are both constructed for every load. The estimate is unweighted
and therefore an auxiliary result, not the full weighted Theorem 3.5. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V)

/-- Uniform order-dt error for the full periodic Euler state and the actual
frozen continuous solution. Thresholds precede T, grid, weight, L, sign and load. -/
theorem temporal_l2_error_uniform (m : ℕ) (hm : 0 < m) (β : ℝ) (hβ : 0 < β) :
    ∃ L₀ δ : ℝ, 1 ≤ L₀ ∧ 0 < δ ∧
      ∀ (g : TimeGrid) (s : Orientation) (w : TimeWeight) (_h : TimeWeightRegularity w g β)
        (L : ℝ), L₀ ≤ L → g.dt*w.max^2 ≤ δ → ∀ f : g.Sequence H,
        let μ := fun i => (L*w.nodes g i)^(2*m)
        let hμ : ∀ i, 0 ≤ μ i := fun _ => (even_two_mul m).pow_nonneg _
        let u := fun i => (b.eulerSolution g s μ hμ f i : H)
        ∃! p : b.PeriodicGraph g,
          b.evolution g s (s.frozenMultiplier g μ) p = s.extensionLp g f ∧
          ‖p.val.2.1‖^2 + ‖p.val.2.2‖^2 +
            ‖(s.frozenMultiplier g μ).map (g.pathL2 p.val.1)‖^2 ≤ 16*(g.l2Norm f)^2 ∧
          ‖g.pathL2 p.val.1 - s.extensionLp g u‖ ≤ 12*g.dt*g.l2Norm f := by
  obtain ⟨L₁,δ₁,hL₁,hδ₁,hsolve⟩ := b.frozen_periodic_uniform m hm β hβ
  refine ⟨max L₁ (eulerShiftThreshold m β), min δ₁ (cellThreshold β 0 0),
    hL₁.trans (le_max_left _ _), lt_min hδ₁ (cellThreshold_pos hβ le_rfl le_rfl), ?_⟩
  intro g s w h L hL hmesh f μ hμ u
  have hLf : L₁ ≤ L := (le_max_left _ _).trans hL
  have hLe : eulerShiftThreshold m β ≤ L := (le_max_right _ _).trans hL
  have hmf : g.dt*w.max^2 ≤ δ₁ := hmesh.trans (min_le_left _ _)
  have hme : g.dt*w.max^2 ≤ cellThreshold β 0 0 := hmesh.trans (min_le_right _ _)
  obtain ⟨p,hp,huniq⟩ := hsolve g s s w h L hLf hmf (s.extensionLp g f)
  refine ⟨p, ⟨hp.1, ?_, ?_⟩, ?_⟩
  · simpa only [s.extensionLp_norm] using hp.2
  · let e := g.pathL2 p.val.1 - s.extensionLp g u
    let Δ := g.affineLp u - s.extensionLp g u
    obtain ⟨q,hq,_⟩ := hsolve g s.opposite s w h L hLf hmf e
    have hd : ‖q.val.2.1‖ ≤ 4*‖e‖ := by
      nlinarith [hq.2, sq_nonneg ‖q.val.2.2‖,
        sq_nonneg ‖(s.frozenMultiplier g μ).map (g.pathL2 q.val.1)‖,
        norm_nonneg q.val.2.1, norm_nonneg e]
    have he := b.temporal_error_duality g s μ hμ f p q hp.1
    change inner ℝ e (b.evolution g s.opposite (s.frozenMultiplier g μ) q) =
      -s.sign * inner ℝ Δ q.val.2.1 at he
    rw [hq.1,real_inner_self_eq_norm_sq] at he
    have hab := congrArg abs he
    have hs : |s.sign|=1 := by cases s <;> norm_num [Orientation.sign]
    rw [abs_of_nonneg (sq_nonneg _), abs_mul, abs_neg, hs, one_mul] at hab
    have hcs : ‖e‖^2 ≤ ‖Δ‖*‖q.val.2.1‖ := hab.trans_le (abs_real_inner_le_norm _ _)
    have hdef := g.affineLp_defect_le s u
    change ‖Δ‖ ≤ g.dt*g.l2Norm (s.difference g u) at hdef
    have hg := b.eulerExtension_graph_bound g s hm hLe w h hme f
    simp only [s.extensionLp_norm] at hg
    change g.l2Norm (s.difference g u) + _ + _ ≤ 3*g.l2Norm f at hg
    have hD : g.l2Norm (s.difference g u) ≤ 3*g.l2Norm f := by
      linarith [g.l2Norm_nonneg (fun i => b.operator (b.eulerSolution g s μ hμ f i)),
        g.l2Norm_nonneg (fun i => μ i • u i)]
    have hdelt : ‖Δ‖ ≤ 3*g.dt*g.l2Norm f := by
      exact hdef.trans (by nlinarith [mul_le_mul_of_nonneg_left hD g.dt_pos.le])
    have hsq : ‖e‖^2 ≤ (12*g.dt*g.l2Norm f)*‖e‖ :=
      hcs.trans (by nlinarith [mul_le_mul hdelt hd (norm_nonneg _) (by positivity [g.dt_pos,g.l2Norm_nonneg f])])
    change ‖e‖ ≤ _
    by_cases he0 : ‖e‖ = 0
    · rw [he0]
      positivity [g.dt_pos,g.l2Norm_nonneg f]
    · rw [pow_two] at hsq
      exact (mul_le_mul_iff_right₀ (lt_of_le_of_ne (norm_nonneg e) (Ne.symm he0))).mp (by simpa only [mul_comm] using hsq)
  · intro q hq
    have hn : ∀ᵐ t ∂g.timeMeasure, 0 ≤ (s.frozenMultiplier g μ).value t := by
      apply Filter.Eventually.of_forall
      intro t
      change 0 ≤ s.extension g μ t
      cases s <;> exact hμ _
    exact b.evolution_injective g s _ hn (hq.1.trans hp.1.symm)

end Carleman.CoerciveForm
