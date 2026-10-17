module

public import Carleman.Continuous.TimeAdjoint

/-! Actual Euler/continuous error cancellation against the opposite evolution.
No error estimate, reconstruction equation, or adjoint solvability is assumed. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V) (g : TimeGrid) (s : Orientation)

omit [CompleteSpace H] in
/-- The original Euler equation as an equality of genuine L² classes. -/
theorem eulerExtension_equation (μ : g.Sequence ℝ) (hμ : ∀ i, 0 ≤ μ i) (f : g.Sequence H) :
    let u := b.eulerSolution g s μ hμ f
    s.extensionLp g (s.difference g (fun i => (u i : H))) +
      s.extensionLp g (fun i => b.operator (u i)) +
      (s.frozenMultiplier g μ).map (s.extensionLp g (fun i => (u i : H))) = s.extensionLp g f := by
  intro u
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (s.extensionLp g (s.difference g (fun i => (u i : H))) +
      s.extensionLp g (fun i => b.operator (u i)))
      ((s.frozenMultiplier g μ).map (s.extensionLp g (fun i => (u i : H)))),
    Lp.coeFn_add (s.extensionLp g (s.difference g (fun i => (u i : H))))
      (s.extensionLp g (fun i => b.operator (u i))),
    s.extensionLp_ae g (s.difference g (fun i => (u i : H))),
    s.extensionLp_ae g (fun i => b.operator (u i)), s.extensionLp_ae g (fun i => (u i : H)),
    s.extensionLp_ae g f, (s.frozenMultiplier g μ).map_ae (s.extensionLp g (fun i => (u i : H)))]
    with t h1 h2 hd ha hu hf hm
  simp only [Pi.add_apply] at h1 h2
  rw [h1,h2,hd,ha,hm,hu,hf]
  have he := b.eulerSolution_equation g s μ hμ f (s.extension g (fun i => i) t)
  cases s <;> exact he

/-- Testing the actual Euler solution uses its constructed affine H¹ path. -/
theorem eulerExtension_adjoint (μ : g.Sequence ℝ) (hμ : ∀ i, 0 ≤ μ i) (f : g.Sequence H)
    (q : b.PeriodicGraph g) :
    let u := fun i => (b.eulerSolution g s μ hμ f i : H)
    inner ℝ (s.extensionLp g f) (g.pathL2 q.val.1) =
      inner ℝ (s.extensionLp g u) (b.evolution g s.opposite (s.frozenMultiplier g μ) q) -
        s.sign * inner ℝ (g.affineLp u - s.extensionLp g u) q.val.2.1 := by
  intro u
  have hq := (b.periodicGraph_mem g q.val).mp q.property
  have hper : (g.affinePath u) ⟨0, by simp [g.period_pos.le]⟩ =
      (g.affinePath u) ⟨g.period, by simp [g.period_pos.le]⟩ := g.affineReconstruction_periodic_trace u
  have ht := g.weak_pairing_L2 (g.affinePath u) q.val.1
    (s.sign • s.extensionLp g (s.difference g u)) q.val.2.1
    (g.affine_weakTimeClass s u) hq.1 hper hq.2.2
  have ha := b.timeOperatorGraph_symmetric (b.eulerExtension_graph g s μ hμ f) hq.2.1
  change inner ℝ (s.extensionLp g (fun i => b.operator (b.eulerSolution g s μ hμ f i)))
    (g.pathL2 q.val.1) = inner ℝ (s.extensionLp g u) q.val.2.2 at ha
  rw [real_inner_smul_left] at ht
  change s.sign * inner ℝ (s.extensionLp g (s.difference g u)) (g.pathL2 q.val.1) +
    inner ℝ (g.affineLp u) q.val.2.1 = 0 at ht
  rw [← b.eulerExtension_equation g s μ hμ f]
  change inner ℝ (s.extensionLp g (s.difference g u) +
      s.extensionLp g (fun i => b.operator (b.eulerSolution g s μ hμ f i)) +
      (s.frozenMultiplier g μ).map (s.extensionLp g u)) (g.pathL2 q.val.1) =
    inner ℝ (s.extensionLp g u) (s.opposite.sign • q.val.2.1 + q.val.2.2 +
      (s.frozenMultiplier g μ).map (g.pathL2 q.val.1)) - _
  simp only [inner_add_left,inner_add_right,real_inner_smul_right,inner_sub_left,
    s.opposite_sign,ha,BoundedMultiplier.map_inner]
  cases s <;> norm_num only [Orientation.sign, one_mul, neg_mul, neg_one_mul] at ht ⊢ <;> linarith

/-- The paper's cancellation with arbitrary dual load, before any graph bound. -/
theorem temporal_error_duality (μ : g.Sequence ℝ) (hμ : ∀ i, 0 ≤ μ i) (f : g.Sequence H)
    (p q : b.PeriodicGraph g)
    (hp : b.evolution g s (s.frozenMultiplier g μ) p = s.extensionLp g f) :
    let u := fun i => (b.eulerSolution g s μ hμ f i : H)
    inner ℝ (g.pathL2 p.val.1 - s.extensionLp g u)
      (b.evolution g s.opposite (s.frozenMultiplier g μ) q) =
        -s.sign * inner ℝ (g.affineLp u - s.extensionLp g u) q.val.2.1 := by
  intro u
  rw [inner_sub_left, ← b.evolution_adjoint, hp, b.eulerExtension_adjoint g s μ hμ f q]
  ring

end Carleman.CoerciveForm
