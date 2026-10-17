module

public import Carleman.Continuous.TemporalL2Error
public import Carleman.Continuous.FormEnergyClass

/-! Actual order-sqrt(dt) error in L²(0,T;V), derived from the proved L²
error, the genuine operator graph bounds and A1 coercivity. This is the
unweighted energy space, not the still-unproved weighted parameter N norm. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman.CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V)

theorem temporal_energy_error_uniform (m : ℕ) (hm : 0 < m) (β : ℝ) (hβ : 0 < β) :
    ∃ L₀ δ C : ℝ, 1 ≤ L₀ ∧ 0 < δ ∧ 0 < C ∧
      ∀ (g : TimeGrid) (s : Orientation) (w : TimeWeight) (_h : TimeWeightRegularity w g β)
        (L : ℝ), L₀ ≤ L → g.dt*w.max^2 ≤ δ → ∀ f : g.Sequence H,
        let μ := fun i => (L*w.nodes g i)^(2*m)
        let hμ : ∀ i, 0 ≤ μ i := fun _ => (even_two_mul m).pow_nonneg _
        let u := b.eulerSolution g s μ hμ f
        ∃ p : b.PeriodicGraph g,
          b.evolution g s (s.frozenMultiplier g μ) p = s.extensionLp g f ∧
          ‖g.pathL2 p.val.1 - s.extensionLp g (fun i => (u i : H))‖ ≤ 12*g.dt*g.l2Norm f ∧
          ‖b.timeEnergy (g.pathL2 p.val.1 - s.extensionLp g (fun i => (u i : H)))
            (p.val.2.2 - s.extensionLp g (fun i => b.operator (u i)))‖^2 ≤ C*g.dt*(g.l2Norm f)^2 := by
  obtain ⟨c,hc,hcoer⟩ := b.coercive
  obtain ⟨L₁,δ₁,hL₁,hδ₁,hsolve⟩ := b.temporal_l2_error_uniform m hm β hβ
  refine ⟨max L₁ (eulerShiftThreshold m β), min δ₁ (cellThreshold β 0 0),84/c,
    hL₁.trans (le_max_left _ _),lt_min hδ₁ (cellThreshold_pos hβ le_rfl le_rfl),by positivity,?_⟩
  intro g s w h L hL hmesh f μ hμ u
  obtain ⟨p,hp,_⟩ := hsolve g s w h L ((le_max_left _ _).trans hL)
    (hmesh.trans (min_le_left _ _)) f
  refine ⟨p,hp.1,hp.2.2,?_⟩
  let e := g.pathL2 p.val.1 - s.extensionLp g (fun i => (u i : H))
  let a := p.val.2.2 - s.extensionLp g (fun i => b.operator (u i))
  have hg := (b.timeOperatorGraph g.timeMeasure).sub_mem
    ((b.periodicGraph_mem g p.val).mp p.property).2.1 (b.eulerExtension_graph g s μ hμ f)
  change (e,a) ∈ b.timeOperatorGraph g.timeMeasure at hg
  have hcoer2 : ∀ v : V, c*‖v‖^2 ≤ b.form v v := by
    simpa only [pow_two,mul_assoc] using hcoer
  have hen := b.timeEnergy_coercive hcoer2 hg
  have hcA : ‖p.val.2.2‖ ≤ 4*g.l2Norm f := by
    nlinarith [hp.2.1,sq_nonneg ‖p.val.2.1‖,
      sq_nonneg ‖(s.frozenMultiplier g μ).map (g.pathL2 p.val.1)‖,
      norm_nonneg p.val.2.2,g.l2Norm_nonneg f]
  have heul := b.eulerExtension_graph_bound g s hm ((le_max_right _ _).trans hL)
    w h (hmesh.trans (min_le_right _ _)) f
  have heA : ‖s.extensionLp g (fun i => b.operator (u i))‖ ≤ 3*g.l2Norm f := by
    simp only [s.extensionLp_norm] at heul ⊢
    change _ + g.l2Norm (fun i => b.operator (u i)) + _ ≤ 3*g.l2Norm f at heul
    linarith [g.l2Norm_nonneg (s.difference g (fun i => (u i : H))),
      g.l2Norm_nonneg (fun i => μ i • (u i : H))]
  have ha : ‖a‖ ≤ 7*g.l2Norm f :=
    (norm_sub_le _ _).trans (by linarith)
  have he : ‖e‖ ≤ 12*g.dt*g.l2Norm f := hp.2.2
  have hprod : inner ℝ e a ≤ 84*g.dt*(g.l2Norm f)^2 := by
    apply (real_inner_le_norm _ _).trans
    have hh := mul_le_mul he ha (norm_nonneg _) (by positivity [g.dt_pos,g.l2Norm_nonneg f])
    nlinarith only [hh]
  change ‖b.timeEnergy e a‖^2 ≤ _
  have hh := hen.trans hprod
  apply (mul_le_mul_iff_right₀ hc).mp
  calc
    c*‖b.timeEnergy e a‖^2 ≤ 84*g.dt*(g.l2Norm f)^2 := hh
    _ = c*((84/c)*g.dt*(g.l2Norm f)^2) := by field_simp
end Carleman.CoerciveForm
