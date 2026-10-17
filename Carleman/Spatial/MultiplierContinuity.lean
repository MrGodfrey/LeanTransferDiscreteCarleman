module

public import Carleman.Spatial.AllowedWeight
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-! Operator-norm continuity of the actual exponential spatial multiplier.
This supplies Bochner measurability for time-dependent L² states, without
choosing a pointwise jointly measurable representative of those states. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
namespace BoundedMultiplier
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ν : Measure Ω}

def continuousLinearMap (w : BoundedMultiplier ν) : Lp E 2 ν →L[ℝ] Lp E 2 ν :=
  w.linearMap.mkContinuous w.bound w.seminorm_le

theorem continuousLinearMap_apply (w : BoundedMultiplier ν) (u : Lp E 2 ν) :
    w.continuousLinearMap u = w.map u := rfl

end BoundedMultiplier
namespace SpatialProfile
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ν : Measure Ω} (ρ : SpatialProfile ν)

def expMultiplier (r : ℝ) : BoundedMultiplier ν where
  value x := Real.exp (ρ.value x * r)
  measurable := Real.continuous_exp.comp_aestronglyMeasurable (ρ.measurable.mul_const r)
  bound := Real.exp (ρ.bound * |r|)
  bound_nonneg := (Real.exp_pos _).le
  bounded := by
    filter_upwards [ρ.bounded] with x hx
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    apply (le_abs_self _).trans
    simpa only [abs_mul] using mul_le_mul_of_nonneg_right hx (abs_nonneg r)

def expCLM (r : ℝ) : Lp E 2 ν →L[ℝ] Lp E 2 ν :=
  (ρ.expMultiplier r).continuousLinearMap

theorem expCLM_ae (r : ℝ) (u : Lp E 2 ν) :
    ρ.expCLM r u =ᵐ[ν] (fun x => Real.exp (ρ.value x * r) • u x) :=
  (ρ.expMultiplier r).map_ae u

theorem exp_profile_difference {a r s M : ℝ}
    (ha : |a| ≤ ρ.bound) (hr : |r| ≤ M) (hs : |s| ≤ M) :
    |Real.exp (a*r) - Real.exp (a*s)| ≤
      (ρ.bound * Real.exp (ρ.bound*M)) * |r-s| := by
  have hd : ∀ t ∈ Icc (-M) M,
      HasDerivWithinAt (fun z => Real.exp (a*z)) (Real.exp (a*t)*a) (Icc (-M) M) t :=
    fun t _ => by simpa using ((hasDerivAt_id t).const_mul a).exp.hasDerivWithinAt
  have hb : ∀ t ∈ Icc (-M) M, ‖Real.exp (a*t)*a‖ ≤ ρ.bound * Real.exp (ρ.bound*M) := by
    intro t ht
    have ht' : |t| ≤ M := abs_le.mpr ht
    have hat : a*t ≤ ρ.bound*M := (le_abs_self _).trans (by
      rw [abs_mul]
      exact mul_le_mul ha ht' (abs_nonneg _) ρ.bound_nonneg)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    simpa only [mul_comm] using mul_le_mul ha (Real.exp_le_exp.mpr hat)
      (Real.exp_pos _).le ρ.bound_nonneg
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
      (convex_Icc (-M) M) (abs_le.mp hs) (abs_le.mp hr)

theorem expCLM_sub_norm_le {r s M : ℝ}
    (hr : |r| ≤ M) (hs : |s| ≤ M) :
    ‖ρ.expCLM (E := E) r - ρ.expCLM s‖ ≤
      (ρ.bound * Real.exp (ρ.bound*M)) * |r-s| := by
  apply (ρ.expCLM (E := E) r - ρ.expCLM s).opNorm_le_bound
    (M := (ρ.bound * Real.exp (ρ.bound*M)) * |r-s|)
    (by positivity [ρ.bound_nonneg])
  intro u
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [ρ.expCLM_ae r u, ρ.expCLM_ae s u,
    Lp.coeFn_sub (ρ.expCLM r u) (ρ.expCLM s u), ρ.bounded] with x h1 h2 h3 hx
  change ‖(ρ.expCLM r u - ρ.expCLM s u) x‖ ≤ _
  rw [h3]
  simp only [Pi.sub_apply, h1, h2, ← sub_smul, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (ρ.exp_profile_difference hx hr hs) (norm_nonneg _)

/-- Continuity in operator norm, with no separability assumption on the L² space. -/
theorem continuous_expCLM : Continuous (ρ.expCLM (E := E)) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  apply continuousAt_of_locally_lipschitz zero_lt_one
    (ρ.bound * Real.exp (ρ.bound*(|r|+1)))
  intro s hs
  rw [dist_eq_norm, Real.norm_eq_abs] at hs
  have hb : |s| ≤ |r|+1 := by
    have hh := abs_add_le (s-r) r
    rw [sub_add_cancel] at hh
    linarith
  simpa only [dist_eq_norm, Real.norm_eq_abs] using
    ρ.expCLM_sub_norm_le hb (by linarith [abs_nonneg r])

theorem multiplier_map_eq_expCLM (w : TimeWeight) (τ t : ℝ) (u : Lp E 2 ν) :
    (ρ.multiplier w τ t).map u = w.q t^τ • ρ.expCLM (w.q t) u := by
  apply Lp.ext
  filter_upwards [(ρ.multiplier w τ t).map_ae u, ρ.expCLM_ae (w.q t) u,
    Lp.coeFn_smul (w.q t^τ) (ρ.expCLM (w.q t) u)] with x h1 h2 h3
  simp only [Pi.smul_apply] at h3
  rw [h1, h3, h2]
  simp only [multiplier, smul_smul]

/-- Actual weighted L² trajectories are strongly measurable in time. -/
theorem aestronglyMeasurable_map (w : TimeWeight) (τ : ℝ) {μ : Measure ℝ}
    (hq : AEStronglyMeasurable w.q μ) {u : ℝ → Lp E 2 ν}
    (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun t => (ρ.multiplier w τ t).map (u t)) μ := by
  simp_rw [ρ.multiplier_map_eq_expCLM]
  have hc : Continuous (fun p : (Lp E 2 ν →L[ℝ] Lp E 2 ν) × Lp E 2 ν => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hw : AEStronglyMeasurable (fun t => ρ.expCLM (E := E) (w.q t)) μ :=
    ρ.continuous_expCLM.comp_aestronglyMeasurable hq
  exact (hq.aemeasurable.pow_const τ).aestronglyMeasurable.smul
    (hc.comp_aestronglyMeasurable (hw.prodMk hu))

/-- Bounded q and rho give finite weighted L² in time; qmax enters only this
finiteness argument, never the uniform perturbation/comparison constants. -/
theorem memLp_map (w : TimeWeight) (τ : ℝ) {μ : Measure ℝ}
    (hq : AEStronglyMeasurable w.q μ) {u : ℝ → Lp E 2 ν} (hu : MemLp u 2 μ) :
    MemLp (fun t => (ρ.multiplier w τ t).map (u t)) 2 μ := by
  apply hu.of_le_mul (c := max 1 (w.max^τ) * Real.exp (ρ.bound*w.max))
    (ρ.aestronglyMeasurable_map w τ hq hu.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun t => ρ.seminorm_global_le w τ t (u t)

end SpatialProfile
end Carleman
