module

public import Carleman.Continuous.ShiftedContinuousGraph
public import Carleman.Weights.CellBounds

/-! Frozen coefficients are only measurable. Their actual graph bound follows
by relative perturbation of the smooth shift, with a uniform mesh threshold. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
namespace BoundedMultiplier
variable {ν : Measure ℝ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem map_sub_norm_le (μ ξ : BoundedMultiplier ν) (θ : ℝ)
    (h : ∀ᵐ t ∂ν, |μ.value t - ξ.value t| ≤ θ * |μ.value t|) (v : Lp H 2 ν) :
    ‖μ.map v - ξ.map v‖ ≤ θ * ‖μ.map v‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [μ.map_ae v, ξ.map_ae v, Lp.coeFn_sub (μ.map v) (ξ.map v), h]
    with t hm hx hs ht
  simp only [Pi.sub_apply] at hs
  rw [hs, hm, hx, ← sub_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right ht (norm_nonneg (v t))
end BoundedMultiplier

namespace TimeWeightRegularity
variable {g : TimeGrid} {w : TimeWeight} {β : ℝ} (h : TimeWeightRegularity w g β)

/-- The original cell estimate as a relative bound on the actual two coefficients. -/
theorem shift_frozen_relative (s : Orientation) {m : ℕ} (hm : 0 < m) {L : ℝ} (hL : 0 < L)
    (hcell : β*g.dt*w.max^2 ≤ 1/2) :
    ∀ᵐ t ∂g.timeMeasure,
      |(h.shiftMultiplier m L hL).value t -
        (s.frozenMultiplier g (fun i => (L*w.nodes g i)^(2*m))).value t| ≤
      ((2*(2*m : ℝ)*2^(2*m-1)*β)*g.dt*w.max^2) * |(h.shiftMultiplier m L hL).value t| := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have he := h.shift_extension s L hL.le (2*m) (by omega) ⟨ht.1.le, ht.2.le⟩ hcell
  change |(L*w.q t)^(2*m) - s.extension g (fun i => (L*w.nodes g i)^(2*m)) t| ≤ _
  apply he.trans
  change (2*(↑(2*m):ℝ)*2^(2*m-1)*β)*L^(2*m)*g.dt*w.q t^(2*m+1) ≤
    ((2*(2*m : ℝ)*2^(2*m-1)*β)*g.dt*w.max^2)*|(L*w.q t)^(2*m)|
  rw [abs_of_nonneg (pow_nonneg (mul_nonneg hL.le (w.nonneg t)) _), mul_pow, pow_succ]
  have hq : w.q t ≤ w.max^2 := (w.upper t).trans (by nlinarith [w.max_ge_one])
  have hc : 0 ≤ (2*(2*m : ℝ)*2^(2*m-1)*β)*g.dt*(L^(2*m)*w.q t^(2*m)) := by
    positivity [h.beta_pos, g.dt_pos, w.pos t]
  convert mul_le_mul_of_nonneg_left hq hc using 1 <;> push_cast <;> ring
end TimeWeightRegularity

namespace CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V) (g : TimeGrid) (s : Orientation)

omit [CompleteSpace H] in
/-- Relative perturbation on the actual L² graph; no final discrete estimate is assumed. -/
theorem periodic_graph_perturbation (μ ξ : BoundedMultiplier g.timeMeasure)
    (hrel : ∀ᵐ t ∂g.timeMeasure, |μ.value t - ξ.value t| ≤ (1/4:ℝ)*|μ.value t|)
    (p : b.PeriodicGraph g)
    (hgraph : ‖p.val.2.1‖^2 + ‖p.val.2.2‖^2 + ‖μ.map (g.pathL2 p.val.1)‖^2 ≤
      2*‖b.evolution g s μ p‖^2) :
    ‖p.val.2.1‖^2 + ‖p.val.2.2‖^2 + ‖ξ.map (g.pathL2 p.val.1)‖^2 ≤
      16*‖b.evolution g s ξ p‖^2 := by
  let v := g.pathL2 p.val.1
  have hd := μ.map_sub_norm_le ξ (1/4) hrel v
  have he : b.evolution g s μ p = b.evolution g s ξ p + (μ.map v - ξ.map v) := by
    change s.sign • p.val.2.1 + p.val.2.2 + μ.map v =
      (s.sign • p.val.2.1 + p.val.2.2 + ξ.map v) + (μ.map v - ξ.map v)
    abel
  have hnorm : ‖b.evolution g s μ p‖ ≤ ‖b.evolution g s ξ p‖ + (1/4)*‖μ.map v‖ := by
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add le_rfl hd)
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnorm
  have hyoung := sq_nonneg (‖b.evolution g s ξ p‖ - (1/4)*‖μ.map v‖)
  have htotal : ‖p.val.2.1‖^2 + ‖p.val.2.2‖^2 + ‖μ.map v‖^2 ≤
      8*‖b.evolution g s ξ p‖^2 := by
    change ‖p.val.2.1‖^2 + ‖p.val.2.2‖^2 + ‖μ.map v‖^2 ≤ _ at hgraph
    nlinarith [sq_nonneg ‖p.val.2.1‖, sq_nonneg ‖p.val.2.2‖]
  have hx : ‖ξ.map v‖ ≤ (5/4)*‖μ.map v‖ := by
    have hh := norm_sub_le (μ.map v) (μ.map v - ξ.map v)
    rw [sub_sub_cancel] at hh
    linarith
  have hxsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hx
  nlinarith [sq_nonneg ‖p.val.2.1‖, sq_nonneg ‖p.val.2.2‖, sq_nonneg ‖μ.map v‖]

/-- Both directions, full weak space, original nodal shift, constant independent of T/L/qmax. -/
theorem frozen_periodic_graph_sq (extension : Orientation) {w : TimeWeight} {β : ℝ} (h : TimeWeightRegularity w g β)
    {m : ℕ} (hm : 0 < m) {L qc : ℝ} (hL : 0 < L) (hqc : 0 < qc)
    (hlower : ∀ t, qc ≤ w.q t)
    (hsmall : (2*m : ℝ)*β/(L^(2*m)*qc^(2*m-1)) ≤ 1/2)
    (hcell : β*g.dt*w.max^2 ≤ 1/2)
    (hmesh : (2*(2*m : ℝ)*2^(2*m-1)*β)*g.dt*w.max^2 ≤ 1/4)
    (p : b.PeriodicGraph g) :
    ‖p.val.2.1‖^2 + ‖p.val.2.2‖^2 +
      ‖(extension.frozenMultiplier g (fun i => (L*w.nodes g i)^(2*m))).map (g.pathL2 p.val.1)‖^2 ≤
      16*‖b.evolution g s (extension.frozenMultiplier g (fun i => (L*w.nodes g i)^(2*m))) p‖^2 := by
  apply b.periodic_graph_perturbation g s (h.shiftMultiplier m L hL)
  · filter_upwards [h.shift_frozen_relative extension hm hL hcell] with t ht
    exact ht.trans (mul_le_mul_of_nonneg_right hmesh (abs_nonneg _))
  · have he := b.shifted_periodic_graph_sq g s h hm hL hqc hlower p
    have hh := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖(h.shiftMultiplier m L hL).map (g.pathL2 p.val.1)‖)
    nlinarith [sq_nonneg ‖p.val.2.1‖, sq_nonneg ‖p.val.2.2‖]

/-- Every L² load, with the time sign and the cell extension chosen independently. -/
theorem frozen_periodic_wellposed (extension : Orientation)
    {w : TimeWeight} {β : ℝ} (h : TimeWeightRegularity w g β)
    {m : ℕ} (hm : 0 < m) {L qc : ℝ} (hL : 0 < L) (hqc : 0 < qc)
    (hlower : ∀ t, qc ≤ w.q t)
    (hsmall : (2*m : ℝ)*β/(L^(2*m)*qc^(2*m-1)) ≤ 1/2)
    (hcell : β*g.dt*w.max^2 ≤ 1/2)
    (hmesh : (2*(2*m : ℝ)*2^(2*m-1)*β)*g.dt*w.max^2 ≤ 1/4)
    (f : Lp H 2 g.timeMeasure) :
    ∃! p : b.PeriodicGraph g,
      b.evolution g s (extension.frozenMultiplier g (fun i => (L*w.nodes g i)^(2*m))) p = f ∧
      ‖p.val.2.1‖^2 + ‖p.val.2.2‖^2 +
        ‖(extension.frozenMultiplier g (fun i => (L*w.nodes g i)^(2*m))).map (g.pathL2 p.val.1)‖^2 ≤
        16*‖f‖^2 := by
  have hn : ∀ᵐ t ∂g.timeMeasure,
      0 ≤ (extension.frozenMultiplier g (fun i => (L*w.nodes g i)^(2*m))).value t := by
    apply Filter.Eventually.of_forall
    intro t
    cases extension <;> exact pow_nonneg (mul_nonneg hL.le (w.nonneg _)) _
  obtain ⟨p, hp, huniq⟩ := b.existsUnique_variable_periodic g s _ hn f
  refine ⟨p, ⟨hp, ?_⟩, fun q hq => huniq q hq.1⟩
  have hb := b.frozen_periodic_graph_sq g s extension h hm hL hqc hlower hsmall hcell hmesh p
  rwa [hp] at hb

omit g s in
/-- Thresholds are chosen before the period, grid, weight, either orientation and load. -/
theorem frozen_periodic_uniform (m : ℕ) (hm : 0 < m) (β : ℝ) (hβ : 0 < β) :
    ∃ L₀ δ : ℝ, 1 ≤ L₀ ∧ 0 < δ ∧
      ∀ (g : TimeGrid) (s extension : Orientation) (w : TimeWeight)
        (_h : TimeWeightRegularity w g β) (L : ℝ), L₀ ≤ L → g.dt*w.max^2 ≤ δ →
        ∀ f : Lp H 2 g.timeMeasure, ∃! p : b.PeriodicGraph g,
          b.evolution g s (extension.frozenMultiplier g (fun i => (L*w.nodes g i)^(2*m))) p = f ∧
          ‖p.val.2.1‖^2 + ‖p.val.2.2‖^2 +
            ‖(extension.frozenMultiplier g (fun i => (L*w.nodes g i)^(2*m))).map (g.pathL2 p.val.1)‖^2 ≤
            16*‖f‖^2 := by
  let C : ℝ := 2*(2*m : ℝ)*2^(2*m-1)*β
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let δ : ℝ := 1/(1+2*β+4*C)
  have hden : 0 < 1+2*β+4*C := by positivity
  refine ⟨max 1 (4*m*β), δ, le_max_left _ _, by dsimp [δ]; positivity, ?_⟩
  intro g s extension w h L hL hmesh f
  have hLone : 1 ≤ L := (le_max_left _ _).trans hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hLone
  have hLlarge : 4*m*β ≤ L := (le_max_right _ _).trans hL
  have hpow : L ≤ L^(2*m) := by
    simpa only [pow_one] using pow_le_pow_right₀ hLone (show 1 ≤ 2*m by omega)
  have hsmall : (2*m : ℝ)*β/(L^(2*m)*1^(2*m-1)) ≤ 1/2 := by
    rw [one_pow, mul_one, div_le_iff₀ (pow_pos hLpos _)]
    nlinarith
  have hM : 0 ≤ g.dt*w.max^2 := mul_nonneg g.dt_pos.le (sq_nonneg _)
  have hh := (le_div_iff₀ hden).mp hmesh
  have hcell : β*g.dt*w.max^2 ≤ 1/2 := by
    nlinarith [mul_nonneg hC hM]
  have hsmallmesh : C*g.dt*w.max^2 ≤ 1/4 := by
    nlinarith [mul_nonneg hβ.le hM]
  exact b.frozen_periodic_wellposed g s extension h hm hLpos zero_lt_one w.lower
    hsmall hcell hsmallmesh f

end CoerciveForm
end Carleman
