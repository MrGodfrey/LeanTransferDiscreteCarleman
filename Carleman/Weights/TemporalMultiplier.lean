module

public import Carleman.Spatial.ExponentialDerivative
public import Carleman.Continuous.WeakTimeProduct

/-! Actual allowed-weight operators: genuine operator-norm time derivatives,
absolute continuity, periodic endpoints and the original logarithmic action. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SpatialProfile
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ν : Measure Ω} (ρ : SpatialProfile ν)

def weightCLM (w : TimeWeight) (τ t : ℝ) : Lp E 2 ν →L[ℝ] Lp E 2 ν :=
  Real.exp (τ*Real.log (w.q t)) • ρ.expCLM (w.q t)

theorem weightCLM_apply (w : TimeWeight) (τ t : ℝ) (u : Lp E 2 ν) :
    ρ.weightCLM w τ t u = (ρ.multiplier w τ t).map u := by
  rw [ρ.multiplier_map_eq_expCLM]
  change Real.exp (τ*Real.log (w.q t)) • ρ.expCLM (w.q t) u = _
  rw [Real.rpow_def_of_pos (w.pos t), mul_comm τ]

variable {w : TimeWeight} {g : TimeGrid} {β : ℝ} (h : TimeWeightRegularity w g β)

def weightDerivativeCLM (τ t : ℝ) : Lp E 2 ν →L[ℝ] Lp E 2 ν :=
  (τ*(h.derivative t/w.q t)) • ρ.weightCLM w τ t +
    h.derivative t • (ρ.valueMultiplier.continuousLinearMap.comp (ρ.weightCLM w τ t))

theorem weightDerivativeCLM_apply (τ t : ℝ) (u : Lp E 2 ν) :
    ρ.weightDerivativeCLM h τ t u =
      ρ.logDerivativeAction h τ t ((ρ.multiplier w τ t).map u) := by
  change (τ*(h.derivative t/w.q t)) • ρ.weightCLM w τ t u +
    h.derivative t • ρ.valueMultiplier.map (ρ.weightCLM w τ t u) = _
  rw [ρ.weightCLM_apply]
  rfl

/-- This derivative is in operator norm, not merely pointwise in the spatial variable. -/
theorem hasDerivWithinAt_weightCLM (τ : ℝ) {t : ℝ} (ht : t ∈ Icc 0 g.period) :
    HasDerivWithinAt (ρ.weightCLM (E := E) w τ) (ρ.weightDerivativeCLM h τ t)
      (Icc 0 g.period) t := by
  have hs := (((h.hasDeriv t ht).log (ne_of_gt (w.pos t))).const_mul τ).exp
  have he := (ρ.hasDerivAt_expCLM (E := E) (w.q t)).scomp_hasDerivWithinAt t (h.hasDeriv t ht)
  convert hs.smul he using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro u
    simp only [weightDerivativeCLM, weightCLM, expDerivativeCLM, ContinuousLinearMap.comp_apply,
      add_apply, smul_apply, map_smul, smul_smul, Function.comp_apply]
    module

theorem weightDerivativeCLM_norm_le (τ : ℝ) {t : ℝ} (ht : t ∈ Icc 0 g.period) :
    ‖ρ.weightDerivativeCLM (E := E) h τ t‖ ≤
      β*(|τ|+ρ.bound)*w.max^2 * (max 1 (w.max^τ)*Real.exp (ρ.bound*w.max)) := by
  have hβ := h.beta_pos
  have hρ := ρ.bound_nonneg
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  rw [ρ.weightDerivativeCLM_apply, ρ.logDerivativeAction_eq h τ ht]
  calc
    _ ≤ β*(|τ|+ρ.bound)*w.q t^2 * ‖(ρ.multiplier w τ t).map u‖ :=
      ρ.logDerivative_seminorm_le h τ ht _
    _ ≤ β*(|τ|+ρ.bound)*w.max^2 *
        ((max 1 (w.max^τ)*Real.exp (ρ.bound*w.max))*‖u‖) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (w.nonneg t) (w.upper t) 2) (by positivity)
      · exact ρ.seminorm_global_le w τ t u
      · exact norm_nonneg _
      · positivity
    _ = _ := by ring

include h in
/-- Only the coefficient is Lipschitz; the evolution trajectory remains weak H¹. -/
theorem weightCLM_absolutelyContinuous (τ : ℝ) :
    AbsolutelyContinuousOnInterval (ρ.weightCLM (E := E) w τ) 0 g.period := by
  let C : ℝ := β*(|τ|+ρ.bound)*w.max^2 * (max 1 (w.max^τ)*Real.exp (ρ.bound*w.max))
  have hC : 0 ≤ C := by dsimp [C]; positivity [h.beta_pos, ρ.bound_nonneg]
  have hl : LipschitzOnWith ⟨C,hC⟩ (ρ.weightCLM (E := E) w τ) (Icc 0 g.period) := by
    apply (convex_Icc (0 : ℝ) g.period).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (f' := ρ.weightDerivativeCLM (E := E) h τ)
    · exact fun t ht => ρ.hasDerivWithinAt_weightCLM h τ ht
    · intro t ht
      exact ρ.weightDerivativeCLM_norm_le h τ ht
  rw [← uIcc_of_le g.period_pos.le] at hl
  exact hl.absolutelyContinuousOnInterval

theorem ae_hasDerivAt_weightCLM (τ : ℝ) :
    ∀ᵐ t ∂g.timeMeasure, HasDerivAt (ρ.weightCLM (E := E) w τ)
      (ρ.weightDerivativeCLM h τ t) t := by
  filter_upwards [g.ae_mem_period] with t ht
  exact (ρ.hasDerivWithinAt_weightCLM (E := E) h τ (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

include h in
theorem weightCLM_continuousOn (τ : ℝ) :
    ContinuousOn (ρ.weightCLM (E := E) w τ) (Icc 0 g.period) := by
  simpa only [uIcc_of_le g.period_pos.le] using
    (ρ.weightCLM_absolutelyContinuous (E := E) h τ).continuousOn

include h in
theorem weightCLM_periodic_trace (τ : ℝ) :
    ρ.weightCLM (E := E) w τ 0 = ρ.weightCLM w τ g.period := by
  simp only [weightCLM, h.endpoint]
end Carleman.SpatialProfile
