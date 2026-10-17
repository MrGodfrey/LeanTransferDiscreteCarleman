module

public import Carleman.Spatial.AllowedWeight
public import Carleman.Weights.CellBounds

/-! Genuine node / continuous-extension comparisons for the allowed spatial L² norms.
All finite grid states and both half-open orientations are included. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman.SpatialProfile
variable {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] {ν : Measure Ω} [SFinite ν] (ρ : SpatialProfile ν)
  {w : TimeWeight} {g : TimeGrid} {β : ℝ} (h : TimeWeightRegularity w g β)
include h

/-- Actual varying-weight density of the existing periodic extension is measurable. -/
theorem aestronglyMeasurable_extended_sq (s : Orientation) (τ : ℝ) (u : g.Sequence (Lp H 2 ν)) :
    AEStronglyMeasurable (fun t => ((ρ.multiplier w τ t).seminorm (s.extension g u t))^2)
      g.timeMeasure := by
  have hh := s.aestronglyMeasurable_cell_select g
    (fun i t => ((ρ.multiplier w τ t).seminorm (u i))^2)
    (fun i => ρ.aestronglyMeasurable_seminorm_sq w τ (u i) h.aestronglyMeasurable)
  convert hh using 1
  cases s <;> rfl

omit [SFinite ν] in
/-- The pointwise square comparisons use the endpoint trace when the plus cell wraps. -/
theorem extended_sq_comparable (s : Orientation) (τ τStar : ℝ) (hτ : |τ| ≤ τStar)
    (hm : β * g.dt * w.max ^ 2 ≤ 1/2)
    (hmw : (4*β*(τStar+ρ.bound)) * g.dt * w.max ^ 2 ≤ 1)
    (u : g.Sequence (Lp H 2 ν)) {t : ℝ} (ht : t ∈ Icc 0 g.period) :
    let d := ((ρ.multiplier w τ t).seminorm (s.extension g u t))^2
    let e := s.extension g (fun i => ((ρ.multiplier w τ (g.nodeTime i)).seminorm (u i))^2) t
    d ≤ 9*e ∧ e ≤ 9*d := by
  let p : ℝ → Seminorm ℝ (Lp H 2 ν) := fun t => (ρ.multiplier w τ t).seminorm
  have hp : p 0 = p g.period := by simp only [p, multiplier, h.endpoint]
  have ha := s.anchor_value_eq_extension g p hp ht
  have hc := ρ.seminorm_cell_le h τ τStar hτ (s.anchor_mem g ht) ht
    (s.anchor_distance g t) hm hmw (s.extension g u t)
  have hr := ρ.seminorm_cell_le h τ τStar hτ ht (s.anchor_mem g ht)
    (by simpa only [abs_sub_comm] using s.anchor_distance g t) hm hmw (s.extension g u t)
  change p t (s.extension g u t) ≤ 3 * p (s.anchor g t) (s.extension g u t) at hc
  change p (s.anchor g t) (s.extension g u t) ≤ 3 * p t (s.extension g u t) at hr
  have he : s.extension g (fun i => (p (g.nodeTime i) (u i))^2) t =
      ((s.extension g (fun i => p (g.nodeTime i)) t) (s.extension g u t))^2 := by cases s <;> rfl
  change (p t (s.extension g u t))^2 ≤ _ ∧ _ ≤ 9*(p t (s.extension g u t))^2
  rw [he, ← ha]
  constructor
  · nlinarith [mul_self_le_mul_self (apply_nonneg (p t) (s.extension g u t)) hc]
  · nlinarith [mul_self_le_mul_self (apply_nonneg (p (s.anchor g t)) (s.extension g u t)) hr]

/-- Both directions of the real space-time norm comparison, with finiteness derived. -/
theorem extended_sq_integral_comparison (s : Orientation) (τ τStar : ℝ) (hτ : |τ| ≤ τStar)
    (hm : β * g.dt * w.max ^ 2 ≤ 1/2)
    (hmw : (4*β*(τStar+ρ.bound)) * g.dt * w.max ^ 2 ≤ 1)
    (u : g.Sequence (Lp H 2 ν)) :
    let d := fun t => ((ρ.multiplier w τ t).seminorm (s.extension g u t))^2
    let n := g.weightedSq (fun i => (ρ.multiplier w τ (g.nodeTime i)).seminorm) u
    Integrable d g.timeMeasure ∧ (∫ t, d t ∂g.timeMeasure) ≤ 9*n ∧
      n ≤ 9*(∫ t, d t ∂g.timeMeasure) := by
  let d := fun t => ((ρ.multiplier w τ t).seminorm (s.extension g u t))^2
  let e := s.extension g (fun i => ((ρ.multiplier w τ (g.nodeTime i)).seminorm (u i))^2)
  have hi := s.integrable_extension g (fun i => ((ρ.multiplier w τ (g.nodeTime i)).seminorm (u i))^2)
  have hc : ∀ᵐ t ∂g.timeMeasure, d t ≤ 9*e t ∧ e t ≤ 9*d t := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    exact ρ.extended_sq_comparable h s τ τStar hτ hm hmw u ⟨ht.1.le, ht.2.le⟩
  have hd : Integrable d g.timeMeasure := (hi.const_mul 9).mono'
    (ρ.aestronglyMeasurable_extended_sq h s τ u) (by
      filter_upwards [hc] with t ht
      simpa only [d, Real.norm_eq_abs, abs_sq] using ht.1)
  have hn : (∫ t, e t ∂g.timeMeasure) =
      g.weightedSq (fun i => (ρ.multiplier w τ (g.nodeTime i)).seminorm) u :=
    s.integral_extension g _
  refine ⟨hd, ?_, ?_⟩
  · have hb := integral_mono_ae hd (hi.const_mul 9) (hc.mono fun _ ht => ht.1)
    rwa [integral_const_mul, hn] at hb
  · have hb := integral_mono_ae hi (hd.const_mul 9) (hc.mono fun _ ht => ht.2)
    rwa [integral_const_mul, hn] at hb

/-- B3's temporal bridge for the manuscript's state, derivative, load and observation
powers. The admissible exponent is tau+a/2, exactly as in the squared norms. -/
theorem powerSq_timeSq_comparison (s : Orientation) (τ a τStar : ℝ)
    (hτ : |τ+a/2| ≤ τStar) (hm : β * g.dt * w.max ^ 2 ≤ 1/2)
    (hmw : (4*β*(τStar+ρ.bound)) * g.dt * w.max ^ 2 ≤ 1)
    (u : g.Sequence (Lp H 2 ν)) :
    let p := fun t => (ρ.multiplier w τ t).seminorm
    TimeSquareIntegrable g w.q a p (s.extension g u) ∧
      timeSq g w.q a p (s.extension g u) ≤ 9 * g.powerSq (w.nodes g) a (fun i => p (g.nodeTime i)) u ∧
      g.powerSq (w.nodes g) a (fun i => p (g.nodeTime i)) u ≤ 9 * timeSq g w.q a p (s.extension g u) := by
  have hc := ρ.extended_sq_integral_comparison h s (τ+a/2) τStar hτ hm hmw u
  have hd : timeDensity w.q a (fun t => (ρ.multiplier w τ t).seminorm) (s.extension g u) =
      fun t => ((ρ.multiplier w (τ+a/2) t).seminorm (s.extension g u t))^2 := by
    funext t
    exact ρ.density_eq_shifted_seminorm_sq w τ a t _
  have hn : g.powerSq (w.nodes g) a (fun i => (ρ.multiplier w τ (g.nodeTime i)).seminorm) u =
      g.weightedSq (fun i => (ρ.multiplier w (τ+a/2) (g.nodeTime i)).seminorm) u := by
    unfold TimeGrid.powerSq TimeGrid.weightedSq
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact ρ.density_eq_shifted_seminorm_sq w τ a (g.nodeTime i) (u i)
  change Integrable _ _ ∧ _ ∧ _
  simp only [timeSq, hd, hn]
  exact hc

/-- Pullback along a real spatial field map. This includes derivative collections,
reconstructions, lifted loads and restriction/observation maps on their full domains. -/
theorem powerSq_timeSq_comparison_comp {V : Type*} [AddCommGroup V] [Module ℝ V]
    (J : V →ₗ[ℝ] Lp H 2 ν) (s : Orientation) (τ a τStar : ℝ)
    (hτ : |τ+a/2| ≤ τStar) (hm : β * g.dt * w.max ^ 2 ≤ 1/2)
    (hmw : (4*β*(τStar+ρ.bound)) * g.dt * w.max ^ 2 ≤ 1)
    (u : g.Sequence V) :
    let p := fun t => (ρ.multiplier w τ t).seminorm.comp J
    TimeSquareIntegrable g w.q a p (s.extension g u) ∧
      timeSq g w.q a p (s.extension g u) ≤ 9 * g.powerSq (w.nodes g) a (fun i => p (g.nodeTime i)) u ∧
      g.powerSq (w.nodes g) a (fun i => p (g.nodeTime i)) u ≤ 9 * timeSq g w.q a p (s.extension g u) := by
  have hc := ρ.powerSq_timeSq_comparison h s τ a τStar hτ hm hmw (fun i => J (u i))
  cases s <;> exact hc


/-- Original load maps may be ordinary functions: only the nodewise load bound is used. -/
theorem lifted_timeSq_le {F : Type*} [AddCommGroup F] [Module ℝ F]
    (lift : F → Lp H 2 ν) (s : Orientation) (τ a τStar : ℝ)
    (hτ : |τ+a/2| ≤ τStar) (hm : β * g.dt * w.max ^ 2 ≤ 1/2)
    (hmw : (4*β*(τStar+ρ.bound)) * g.dt * w.max ^ 2 ≤ 1)
    (p : g.Index → Seminorm ℝ F) (f : g.Sequence F) (K : ℝ)
    (hnode : ∀ i, ((ρ.multiplier w τ (g.nodeTime i)).seminorm (lift (f i)))^2 ≤ K*(p i (f i))^2) :
    timeSq g w.q a (fun t => (ρ.multiplier w τ t).seminorm) (s.extension g (fun i => lift (f i))) ≤
      (9*K)*g.powerSq (w.nodes g) a p f := by
  have hc := (ρ.powerSq_timeSq_comparison h s τ a τStar hτ hm hmw (fun i => lift (f i))).2.1
  have hn := g.powerSq_le (w.nodes g) (fun i => w.nonneg (g.nodeTime i)) a
    (fun i => (ρ.multiplier w τ (g.nodeTime i)).seminorm) p (fun i => lift (f i)) f hnode
  exact hc.trans ((mul_le_mul_of_nonneg_left hn (by norm_num)).trans_eq (by ring))

/-- A numerical spatial reconstruction lower bound followed by the proved temporal comparison. -/
theorem node_powerSq_le_reconstruction {X : Type*} [AddCommGroup X] [Module ℝ X]
    (R : X → Lp H 2 ν) (s : Orientation) (τ a τStar : ℝ)
    (hτ : |τ+a/2| ≤ τStar) (hm : β * g.dt * w.max ^ 2 ≤ 1/2)
    (hmw : (4*β*(τStar+ρ.bound)) * g.dt * w.max ^ 2 ≤ 1)
    (p : g.Index → Seminorm ℝ X) (z : g.Sequence X) (K : ℝ) (hK : 0 ≤ K)
    (hnode : ∀ i, (p i (z i))^2 ≤ K*((ρ.multiplier w τ (g.nodeTime i)).seminorm (R (z i)))^2) :
    g.powerSq (w.nodes g) a p z ≤ (9*K)*
      timeSq g w.q a (fun t => (ρ.multiplier w τ t).seminorm) (s.extension g (fun i => R (z i))) := by
  have hc := (ρ.powerSq_timeSq_comparison h s τ a τStar hτ hm hmw (fun i => R (z i))).2.2
  have hn := g.powerSq_le (w.nodes g) (fun i => w.nonneg (g.nodeTime i)) a p
    (fun i => (ρ.multiplier w τ (g.nodeTime i)).seminorm) z (fun i => R (z i)) hnode
  exact hn.trans ((mul_le_mul_of_nonneg_left hc hK).trans_eq (by ring))

omit h in
/-- The threshold is chosen before the time period, weight, grid, state and orientation. -/
theorem powerSq_timeSq_uniform (β τStar : ℝ) (hβ : 0 < β) (hτStar : 0 ≤ τStar) :
    ∃ δ > 0, ∀ (w : TimeWeight) (g : TimeGrid) (_h : TimeWeightRegularity w g β),
      g.dt*w.max^2 ≤ δ → ∀ (s : Orientation) (τ a : ℝ), |τ+a/2| ≤ τStar →
      ∀ u : g.Sequence (Lp H 2 ν),
      let p := fun t => (ρ.multiplier w τ t).seminorm
      TimeSquareIntegrable g w.q a p (s.extension g u) ∧
        timeSq g w.q a p (s.extension g u) ≤ 9*g.powerSq (w.nodes g) a (fun i => p (g.nodeTime i)) u ∧
        g.powerSq (w.nodes g) a (fun i => p (g.nodeTime i)) u ≤ 9*timeSq g w.q a p (s.extension g u) := by
  refine ⟨cellThreshold β τStar ρ.bound, cellThreshold_pos hβ hτStar ρ.bound_nonneg, ?_⟩
  intro w g hw hm s τ a hτ u
  have hb := hw.mesh_bounds τStar ρ.bound hτStar ρ.bound_nonneg hm
  exact ρ.powerSq_timeSq_comparison hw s τ a τStar hτ hb.1 hb.2 u


omit h in
/-- A fixed bound on all norm exponents avoids imposing a larger original allowed-weight
family. The analytic cell threshold may use tauStar+A/2 without requiring numerical
assumptions for any additional weight. -/
theorem powerSq_timeSq_uniform_bounded_exponents (β τStar A : ℝ)
    (hβ : 0 < β) (hτStar : 0 ≤ τStar) (hA : 0 ≤ A) :
    ∃ δ > 0, ∀ (w : TimeWeight) (g : TimeGrid) (_h : TimeWeightRegularity w g β),
      g.dt*w.max^2 ≤ δ → ∀ (s : Orientation) (τ a : ℝ), |τ| ≤ τStar → |a| ≤ A →
      ∀ u : g.Sequence (Lp H 2 ν),
      let p := fun t => (ρ.multiplier w τ t).seminorm
      TimeSquareIntegrable g w.q a p (s.extension g u) ∧
        timeSq g w.q a p (s.extension g u) ≤ 9*g.powerSq (w.nodes g) a (fun i => p (g.nodeTime i)) u ∧
        g.powerSq (w.nodes g) a (fun i => p (g.nodeTime i)) u ≤ 9*timeSq g w.q a p (s.extension g u) := by
  obtain ⟨δ, hδ, hc⟩ := ρ.powerSq_timeSq_uniform (H := H) β (τStar+A/2) hβ (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro w g hw hm s τ a hτ ha u
  apply hc w g hw hm s τ a _ u
  have hh := abs_add_le τ (a/2)
  rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
  linarith

end Carleman.SpatialProfile
