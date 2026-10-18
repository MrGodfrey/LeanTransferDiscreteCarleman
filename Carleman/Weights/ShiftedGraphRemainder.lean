module

public import Carleman.Weights.WeightedGraphConstruction
public import Carleman.Continuous.ShiftedContinuousGraph

/-! The nonfrozen coefficient (L q(t))^(2m). The following estimates have no
mesh restriction: the grid parameter is used only to carry the period and its
Lebesgue measure. Every lower bound is chosen before that period. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman

theorem continuous_shift_margin_uniform (m : ℕ) (hm : 0 < m) (C : ℝ) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → C ≤ L^(2*m) := by
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro L hL
  apply ((le_max_right _ _).trans hL).trans
  simpa only [pow_one] using pow_le_pow_right₀ ((le_max_left _ _).trans hL) (show 1 ≤ 2*m by omega)

namespace SpatialProfile
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ν : Measure Ω} (ρ : SpatialProfile ν)

theorem logDerivative_shift_small_uniform (m : ℕ) (hm : 0 < m)
    (β τStar η : ℝ) (hβ : 0 < β) (_hτStar : 0 ≤ τStar) (hη : 0 < η) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧
      ∀ (g : TimeGrid) (w : TimeWeight) (h : TimeWeightRegularity w g β)
        (L τ : ℝ) (hL : 0 < L), L₀ ≤ L → |τ| ≤ τStar →
        ∀ u : Lp (Lp E 2 ν) 2 g.timeMeasure,
          ‖(ρ.memLp_logDerivativeAction h τ (Lp.memLp u)).toLp
            (fun t => ρ.logDerivativeAction h τ t (u t))‖ ≤
            η * ‖(h.shiftMultiplier m L hL).map u‖ := by
  obtain ⟨L₀,hL₀,hpow⟩ := continuous_shift_margin_uniform m hm (β*(τStar+ρ.bound)/η)
  refine ⟨L₀,hL₀,?_⟩
  intro g w h L τ hL hLL hτ u
  have he : (h.memLp_shift m hL (Lp.memLp u)).toLp (fun t => (L*w.q t)^(2*m) • u t) =
      (h.shiftMultiplier m L hL).map u := by
    apply Lp.ext
    filter_upwards [(h.memLp_shift m hL (Lp.memLp u)).coeFn_toLp,
      (h.shiftMultiplier m L hL).map_ae u] with t h1 h2
    exact h1.trans h2.symm
  have hh := ρ.logDerivative_spacetime_le h hm hL τ (Lp.memLp u)
  rw [he] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply (div_le_iff₀ (pow_pos hL _)).mpr
  have hp := (div_le_iff₀ hη).mp (hpow L hLL)
  have ht := mul_le_mul_of_nonneg_left (add_le_add_right hτ ρ.bound) hβ.le
  nlinarith
end SpatialProfile

namespace CoerciveForm
variable {Ω E V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] {ν : Measure Ω}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm (Lp E 2 ν) V) (ρ : SpatialProfile ν)

set_option maxHeartbeats 800000 in
theorem weighted_shift_graph_remainder_uniform (m : ℕ) (hm : 0 < m)
    (β τStar : ℝ) (hβ : 0 < β) (hτStar : 0 ≤ τStar) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧
      ∀ (g : TimeGrid) (s : Orientation) (w : TimeWeight)
        (h : TimeWeightRegularity w g β) (L τ : ℝ) (hLpos : 0 < L),
        L₀ ≤ L → |τ| ≤ τStar → ∀ p q : b.PeriodicGraph g,
        let M := ρ.timeMap g w τ h.aestronglyMeasurable
        let μ := h.shiftMultiplier m L hLpos
        let B := (ρ.memLp_logDerivativeAction h τ (Lp.memLp (g.pathL2 q.val.1))).toLp
          (fun t => ρ.logDerivativeAction h τ t (g.pathL2 q.val.1 t))
        g.pathL2 q.val.1 = M (g.pathL2 p.val.1) → q.val.2.1 = B + M p.val.2.1 →
          ‖M p.val.2.1‖ + ‖M p.val.2.2‖ + ‖μ.map (M (g.pathL2 p.val.1))‖ ≤
            30*(‖M (b.evolution g s μ p)‖ + ‖q.val.2.2 - M p.val.2.2‖) := by
  obtain ⟨L₁,hL₁,hpow⟩ := continuous_shift_margin_uniform m hm (4*m*β)
  obtain ⟨L₂,hL₂,hsmall⟩ := ρ.logDerivative_shift_small_uniform
    (E := E) m hm β τStar (1/24) hβ hτStar (by norm_num)
  refine ⟨max L₁ L₂,hL₁.trans (le_max_left _ _),?_⟩
  intro g s w h L τ hLpos hL hτ p q M μ B hv hd
  let R := q.val.2.2 - M p.val.2.2
  let F := M (b.evolution g s μ p)
  have hB : ‖B‖ ≤ (1/24)*‖μ.map (g.pathL2 q.val.1)‖ :=
    hsmall g w h L τ hLpos ((le_max_right _ _).trans hL) hτ _
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
  have hp := hpow L ((le_max_left _ _).trans hL)
  have hratio : (2*m : ℝ)*β/L^(2*m) ≤ 1/2 := by
    apply (div_le_iff₀ (pow_pos hLpos _)).mpr
    linarith
  have hg0 := b.shifted_periodic_graph_sq g s h hm hLpos zero_lt_one w.lower q
  simp only [one_pow,mul_one] at hg0
  have hr : ‖q.val.2.1‖^2+‖q.val.2.2‖^2+‖μ.map (g.pathL2 q.val.1)‖^2 ≤
      2*‖b.evolution g s μ q‖^2 := by
    change ‖q.val.2.1‖^2+‖q.val.2.2‖^2+(1-(2*m:ℝ)*β/L^(2*m))*‖μ.map (g.pathL2 q.val.1)‖^2 ≤ _ at hg0
    nlinarith [mul_le_mul_of_nonneg_right hratio (sq_nonneg ‖μ.map (g.pathL2 q.val.1)‖),
      sq_nonneg ‖q.val.2.1‖,sq_nonneg ‖q.val.2.2‖]
  have hG : ‖q.val.2.1‖ + ‖q.val.2.2‖ + ‖μ.map (g.pathL2 q.val.1)‖ ≤
      12*‖b.evolution g s μ q‖ := by
    have h1 : ‖q.val.2.1‖ ≤ 4*‖b.evolution g s μ q‖ := by
      nlinarith [hr,sq_nonneg ‖q.val.2.2‖,sq_nonneg ‖μ.map (g.pathL2 q.val.1)‖,norm_nonneg (b.evolution g s μ q)]
    have h2 : ‖q.val.2.2‖ ≤ 4*‖b.evolution g s μ q‖ := by
      nlinarith [hr,sq_nonneg ‖q.val.2.1‖,sq_nonneg ‖μ.map (g.pathL2 q.val.1)‖,norm_nonneg (b.evolution g s μ q)]
    have h3 : ‖μ.map (g.pathL2 q.val.1)‖ ≤ 4*‖b.evolution g s μ q‖ := by
      nlinarith [hr,sq_nonneg ‖q.val.2.1‖,sq_nonneg ‖q.val.2.2‖,norm_nonneg (b.evolution g s μ q)]
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

end CoerciveForm
end Carleman
