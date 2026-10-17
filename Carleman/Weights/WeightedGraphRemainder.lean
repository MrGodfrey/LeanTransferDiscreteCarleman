module

public import Carleman.Weights.TimeL2Multiplier
public import Carleman.Weights.FrozenTemporalPerturbation
public import Carleman.Continuous.FrozenContinuousGraph

/-! A weighted frozen graph estimate with the exact spatial commutator left
visible. The temporal perturbation is absorbed with thresholds uniform in T.
The weighted graph representative is constructed from A1/A2 in the next module. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman.SpatialProfile
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ν : Measure Ω} (ρ : SpatialProfile ν) (g : TimeGrid) (w : TimeWeight) (τ : ℝ)
  (hq : AEStronglyMeasurable w.q g.timeMeasure)

theorem timeMap_commute_multiplier (μ : BoundedMultiplier g.timeMeasure)
    (u : Lp (Lp E 2 ν) 2 g.timeMeasure) :
    ρ.timeMap g w τ hq (μ.map u) = μ.map (ρ.timeMap g w τ hq u) := by
  apply Lp.ext
  filter_upwards [ρ.timeMap_ae g w τ hq (μ.map u), μ.map_ae u,
    μ.map_ae (ρ.timeMap g w τ hq u), ρ.timeMap_ae g w τ hq u] with t h1 h2 h3 h4
  rw [h1,h2,h3,h4,BoundedMultiplier.map_smul]

end Carleman.SpatialProfile
namespace Carleman
/-- Linear algebra used for the actual evolution fields below. -/
theorem linear_evolution_residual {X : Type*} [AddCommGroup X] [Module ℝ X]
    (M : X →ₗ[ℝ] X) (s : ℝ) (B d a b c : X) :
    s • (B + M d) + a + M c = M (s • d + b + c) + (a - M b) + s • B := by
  simp only [map_add, map_smul, smul_add]
  abel
end Carleman
namespace Carleman.CoerciveForm
variable {Ω E V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] {ν : Measure Ω}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm (Lp E 2 ν) V) (ρ : SpatialProfile ν)

omit ρ [CompleteSpace E] in
/-- Algebra on the actual graph classes; no scalar proxy for a field is introduced. -/
theorem weighted_evolution_identity (g : TimeGrid) (s : Orientation)
    (μ : BoundedMultiplier g.timeMeasure)
    (M : Lp (Lp E 2 ν) 2 g.timeMeasure →ₗ[ℝ] Lp (Lp E 2 ν) 2 g.timeMeasure)
    (p q : b.PeriodicGraph g) (B : Lp (Lp E 2 ν) 2 g.timeMeasure)
    (hv : g.pathL2 q.val.1 = M (g.pathL2 p.val.1))
    (hd : q.val.2.1 = B + M p.val.2.1)
    (hcomm : M (μ.map (g.pathL2 p.val.1)) = μ.map (M (g.pathL2 p.val.1))) :
    b.evolution g s μ q = M (b.evolution g s μ p) + (q.val.2.2 - M p.val.2.2) + s.sign • B := by
  change s.sign • q.val.2.1 + q.val.2.2 + μ.map (g.pathL2 q.val.1) =
    M (s.sign • p.val.2.1 + p.val.2.2 + μ.map (g.pathL2 p.val.1)) + _ + _
  rw [hd,hv,← hcomm]
  exact linear_evolution_residual M s.sign B p.val.2.1 q.val.2.2 p.val.2.2 (μ.map (g.pathL2 p.val.1))

set_option maxHeartbeats 800000 in
/-- No graph estimate is a premise. The only two equalities identify the value
and derivative of the actual weighted graph trajectory; its construction uses
A1/A2 separately. The remaining operator difference is the real commutator. -/
theorem weighted_frozen_graph_remainder_uniform (m : ℕ) (hm : 0 < m)
    (β τStar : ℝ) (hβ : 0 < β) (hτStar : 0 ≤ τStar) :
    ∃ L₀ δ : ℝ, 1 ≤ L₀ ∧ 0 < δ ∧
      ∀ (g : TimeGrid) (s extension : Orientation) (w : TimeWeight)
        (h : TimeWeightRegularity w g β) (L τ : ℝ),
        L₀ ≤ L → g.dt*w.max^2 ≤ δ → |τ| ≤ τStar →
        ∀ p q : b.PeriodicGraph g,
        let M := ρ.timeMap g w τ h.aestronglyMeasurable
        let μ := extension.frozenMultiplier g (fun i => (L*w.nodes g i)^(2*m))
        let B := (ρ.memLp_logDerivativeAction h τ (Lp.memLp (g.pathL2 q.val.1))).toLp
          (fun t => ρ.logDerivativeAction h τ t (g.pathL2 q.val.1 t))
        g.pathL2 q.val.1 = M (g.pathL2 p.val.1) → q.val.2.1 = B + M p.val.2.1 →
          ‖M p.val.2.1‖ + ‖M p.val.2.2‖ + ‖μ.map (M (g.pathL2 p.val.1))‖ ≤
            30*(‖M (b.evolution g s μ p)‖ + ‖q.val.2.2 - M p.val.2.2‖) := by
  obtain ⟨L₁,δ₁,hL₁,hδ₁,hsolve⟩ := b.frozen_periodic_uniform m hm β hβ
  obtain ⟨L₂,δ₂,hL₂,hδ₂,hsmall⟩ := ρ.logDerivative_frozen_small_uniform
    (E := E) m hm β τStar (1/24) hβ hτStar (by norm_num)
  refine ⟨max L₁ L₂,min δ₁ δ₂,hL₁.trans (le_max_left _ _),lt_min hδ₁ hδ₂,?_⟩
  intro g s extension w h L τ hL hmesh hτ p q M μ B hv hd
  let R := q.val.2.2 - M p.val.2.2
  let F := M (b.evolution g s μ p)
  have hB : ‖B‖ ≤ (1/24)*‖μ.map (g.pathL2 q.val.1)‖ :=
    hsmall g extension w h L τ ((le_max_right _ _).trans hL)
      (hmesh.trans (min_le_right _ _)) hτ _
  have hs : |s.sign| = 1 := by cases s <;> norm_num [Orientation.sign]
  have hcomm := ρ.timeMap_commute_multiplier g w τ h.aestronglyMeasurable μ (g.pathL2 p.val.1)
  change M (μ.map (g.pathL2 p.val.1)) = μ.map (M (g.pathL2 p.val.1)) at hcomm
  have he : b.evolution g s μ q = F + R + s.sign • B :=
    b.weighted_evolution_identity g s μ M p q B hv hd hcomm
  have heN : ‖b.evolution g s μ q‖ ≤ ‖F‖ + ‖R‖ + ‖B‖ := by
    rw [he]
    have hh := norm_add_le (F+R) (s.sign • B)
    rw [norm_smul, Real.norm_eq_abs, hs, one_mul] at hh
    linarith [norm_add_le F R]
  obtain ⟨r,hr,hu⟩ := hsolve g s extension w h L ((le_max_left _ _).trans hL)
    (hmesh.trans (min_le_left _ _)) (b.evolution g s μ q)
  have hn : ∀ᵐ t ∂g.timeMeasure, 0 ≤ μ.value t := Filter.Eventually.of_forall fun t => by
    change 0 ≤ extension.extension g (fun i => (L*w.nodes g i)^(2*m)) t
    cases extension <;> exact (even_two_mul m).pow_nonneg _
  have hrq : r = q := b.evolution_injective g s μ hn hr.1
  rw [hrq] at hr
  have hG : ‖q.val.2.1‖ + ‖q.val.2.2‖ + ‖μ.map (g.pathL2 q.val.1)‖ ≤
      12*‖b.evolution g s μ q‖ := by
    have h1 : ‖q.val.2.1‖ ≤ 4*‖b.evolution g s μ q‖ := by
      nlinarith [hr.2,sq_nonneg ‖q.val.2.2‖,sq_nonneg ‖μ.map (g.pathL2 q.val.1)‖,norm_nonneg (b.evolution g s μ q)]
    have h2 : ‖q.val.2.2‖ ≤ 4*‖b.evolution g s μ q‖ := by
      nlinarith [hr.2,sq_nonneg ‖q.val.2.1‖,sq_nonneg ‖μ.map (g.pathL2 q.val.1)‖,norm_nonneg (b.evolution g s μ q)]
    have h3 : ‖μ.map (g.pathL2 q.val.1)‖ ≤ 4*‖b.evolution g s μ q‖ := by
      nlinarith [hr.2,sq_nonneg ‖q.val.2.1‖,sq_nonneg ‖q.val.2.2‖,norm_nonneg (b.evolution g s μ q)]
    linarith
  have hD : ‖M p.val.2.1‖ ≤ ‖q.val.2.1‖ + ‖B‖ := by
    have hid : M p.val.2.1 = q.val.2.1 - B := by rw [hd]; abel
    rw [hid]
    exact norm_sub_le _ _
  have hA : ‖M p.val.2.2‖ ≤ ‖q.val.2.2‖ + ‖R‖ := by
    have hid : M p.val.2.2 = q.val.2.2 - R := by dsimp [R]; abel
    rw [hid]
    exact norm_sub_le _ _
  rw [← hv]
  change _ ≤ 30*(‖F‖+‖R‖)
  linarith [norm_nonneg q.val.2.1,norm_nonneg q.val.2.2,norm_nonneg F,norm_nonneg R]

end Carleman.CoerciveForm
