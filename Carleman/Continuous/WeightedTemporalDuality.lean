module

public import Carleman.Continuous.TemporalErrorIdentity
public import Carleman.Continuous.FrozenContinuousGraph
public import Carleman.Weights.WeightedAffineDefect

/-! Exact weighted temporal duality with the actual periodic adjoint solution.
The derivative factor remains visible: its uniform weighted load bound is a
separate analytic obligation, not an assumed final error estimate. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman.CoerciveForm
variable {Ω E V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] {ν : Measure Ω} [SFinite ν]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm (Lp E 2 ν) V) (ρ : SpatialProfile ν)
  (g : TimeGrid) (s : Orientation) (w : TimeWeight) (τ : ℝ)
  (hq : AEStronglyMeasurable w.q g.timeMeasure)

omit [SFinite ν] in
/-- Both solution equations are the actual frozen evolution. The adjoint load
is multiplication twice, so it does not require a larger allowed weight family. -/
theorem weighted_temporal_duality (μ : g.Sequence ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (f : g.Sequence (Lp E 2 ν)) (p q : b.PeriodicGraph g)
    (hp : b.evolution g s (s.frozenMultiplier g μ) p = s.extensionLp g f)
    (hqeq : b.evolution g s.opposite (s.frozenMultiplier g μ) q =
      ρ.timeMap g w τ hq (ρ.timeMap g w τ hq
        (g.pathL2 p.val.1 - s.extensionLp g (fun i => (b.eulerSolution g s μ hμ f i : Lp E 2 ν))))) :
    let u := fun i => (b.eulerSolution g s μ hμ f i : Lp E 2 ν)
    ‖ρ.timeMap g w τ hq (g.pathL2 p.val.1 - s.extensionLp g u)‖^2 =
      -s.sign * inner ℝ (ρ.timeMap g w τ hq (g.affineLp u - s.extensionLp g u))
        (ρ.neg.timeMap g w (-τ) hq q.val.2.1) := by
  have he := b.temporal_error_duality g s μ hμ f p q hp
  dsimp only at he
  rw [hqeq, ρ.timeMap_inner_twice, ← ρ.timeMap_inner_inverse g w τ hq] at he
  exact he

omit [SFinite ν] in
theorem weighted_temporal_duality_bound (μ : g.Sequence ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (f : g.Sequence (Lp E 2 ν)) (p q : b.PeriodicGraph g)
    (hp : b.evolution g s (s.frozenMultiplier g μ) p = s.extensionLp g f)
    (hqeq : b.evolution g s.opposite (s.frozenMultiplier g μ) q =
      ρ.timeMap g w τ hq (ρ.timeMap g w τ hq
        (g.pathL2 p.val.1 - s.extensionLp g (fun i => (b.eulerSolution g s μ hμ f i : Lp E 2 ν))))) :
    let u := fun i => (b.eulerSolution g s μ hμ f i : Lp E 2 ν)
    ‖ρ.timeMap g w τ hq (g.pathL2 p.val.1 - s.extensionLp g u)‖^2 ≤
      ‖ρ.timeMap g w τ hq (g.affineLp u - s.extensionLp g u)‖ *
        ‖ρ.neg.timeMap g w (-τ) hq q.val.2.1‖ := by
  let u := fun i => (b.eulerSolution g s μ hμ f i : Lp E 2 ν)
  let e := ρ.timeMap g w τ hq (g.pathL2 p.val.1 - s.extensionLp g u)
  let d := ρ.timeMap g w τ hq (g.affineLp u - s.extensionLp g u)
  let y := ρ.neg.timeMap g w (-τ) hq q.val.2.1
  have hid := b.weighted_temporal_duality ρ g s w τ hq μ hμ f p q hp hqeq
  change ‖e‖^2 = -s.sign * inner ℝ d y at hid
  have he := congrArg abs hid
  have hs : |s.sign| = 1 := by cases s <;> norm_num [Orientation.sign]
  rw [abs_of_nonneg (sq_nonneg _), abs_mul, abs_neg, hs, one_mul] at he
  change ‖e‖^2 ≤ ‖d‖*‖y‖
  exact he.trans_le (abs_real_inner_le_norm d y)

omit g s w τ hq in
/-- Construct both periodic solutions for every load and prove the order-dt
weighted pairing bound. No adjoint existence or error estimate is assumed. -/
theorem weighted_temporal_duality_uniform (β τStar : ℝ) (hβ : 0 < β) (hτStar : 0 ≤ τStar) :
    ∃ δ > 0, ∀ (g : TimeGrid) (s : Orientation) (w : TimeWeight) (h : TimeWeightRegularity w g β),
      g.dt*w.max^2 ≤ δ → ∀ (τ : ℝ), |τ| ≤ τStar →
      ∀ (μ : g.Sequence ℝ) (hμ : ∀ i, 0 ≤ μ i) (f : g.Sequence (Lp E 2 ν)),
        let u := fun i => (b.eulerSolution g s μ hμ f i : Lp E 2 ν)
        ∃ p q : b.PeriodicGraph g,
          b.evolution g s (s.frozenMultiplier g μ) p = s.extensionLp g f ∧
          b.evolution g s.opposite (s.frozenMultiplier g μ) q =
            ρ.timeMap g w τ h.aestronglyMeasurable
              (ρ.timeMap g w τ h.aestronglyMeasurable (g.pathL2 p.val.1 - s.extensionLp g u)) ∧
          ‖ρ.timeMap g w τ h.aestronglyMeasurable (g.pathL2 p.val.1 - s.extensionLp g u)‖^2 ≤
            (3*g.dt*g.weightedNorm (fun i => (ρ.multiplier w τ (g.nodeTime i)).seminorm)
              (s.difference g u)) * ‖ρ.neg.timeMap g w (-τ) h.aestronglyMeasurable q.val.2.1‖ := by
  obtain ⟨δ,hδ,hdef⟩ := ρ.weighted_affine_defect_uniform (E := E) β τStar hβ hτStar
  refine ⟨δ,hδ,?_⟩
  intro g s w h hmesh τ hτ μ hμ f u
  have hn : ∀ᵐ t ∂g.timeMeasure, 0 ≤ (s.frozenMultiplier g μ).value t :=
    Filter.Eventually.of_forall fun t => by
      change 0 ≤ s.extension g μ t
      cases s <;> exact hμ _
  obtain ⟨p,hp,_⟩ := b.existsUnique_variable_periodic g s (s.frozenMultiplier g μ) hn (s.extensionLp g f)
  let F := ρ.timeMap g w τ h.aestronglyMeasurable
    (ρ.timeMap g w τ h.aestronglyMeasurable (g.pathL2 p.val.1 - s.extensionLp g u))
  obtain ⟨q,hq,_⟩ := b.existsUnique_variable_periodic g s.opposite (s.frozenMultiplier g μ) hn F
  refine ⟨p,q,hp,hq,?_⟩
  have he := b.weighted_temporal_duality_bound ρ g s w τ h.aestronglyMeasurable μ hμ f p q hp hq
  have hd := hdef g w h hmesh s τ hτ u
  exact he.trans (mul_le_mul_of_nonneg_right hd (norm_nonneg _))

end Carleman.CoerciveForm
