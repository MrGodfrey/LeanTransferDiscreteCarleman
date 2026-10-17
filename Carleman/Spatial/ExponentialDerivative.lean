module

public import Carleman.Weights.TemporalPerturbation
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! Differentiability of the actual exponential multiplier in operator norm.
Uniform Taylor remainders on the bounded spatial profile justify the passage
from scalar differentiation to the L² operator. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman.SpatialProfile
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ν : Measure Ω} (ρ : SpatialProfile ν)

def expDerivativeCLM (r : ℝ) : Lp E 2 ν →L[ℝ] Lp E 2 ν :=
  ρ.valueMultiplier.continuousLinearMap.comp (ρ.expCLM r)

theorem expDerivativeCLM_ae (r : ℝ) (u : Lp E 2 ν) :
    ρ.expDerivativeCLM r u =ᵐ[ν] (fun x => (ρ.value x*Real.exp (ρ.value x*r)) • u x) := by
  filter_upwards [ρ.valueMultiplier.map_ae (ρ.expCLM r u), ρ.expCLM_ae r u] with x h1 h2
  change ρ.valueMultiplier.map (ρ.expCLM r u) x = _
  rw [h1, h2, ← mul_smul]
  rfl

theorem exp_scalar_remainder {a r s : ℝ} (ha : |a| ≤ ρ.bound)
    (hs : ρ.bound*|s-r| ≤ 1) :
    |Real.exp (a*s)-Real.exp (a*r)-(s-r)*(a*Real.exp (a*r))| ≤
      (Real.exp (ρ.bound*|r|)*ρ.bound^2)*|s-r|^2 := by
  have hz : |a*(s-r)| ≤ 1 := (by rw [abs_mul]; gcongr : |a*(s-r)| ≤ ρ.bound*|s-r|).trans hs
  have he := Real.norm_exp_sub_one_sub_id_le (by simpa only [Real.norm_eq_abs] using hz)
  have hfac : Real.exp (a*s)-Real.exp (a*r)-(s-r)*(a*Real.exp (a*r)) =
      Real.exp (a*r)*(Real.exp (a*(s-r))-1-a*(s-r)) := by
    have h := Real.exp_add (a*r) (a*(s-r))
    rw [show a*r+a*(s-r)=a*s by ring] at h
    rw [h]
    ring
  rw [hfac, abs_mul, abs_of_pos (Real.exp_pos _)]
  have har : a*r ≤ ρ.bound*|r| := (le_abs_self _).trans (by rw [abs_mul]; gcongr)
  calc
    _ ≤ Real.exp (a*r)*|a*(s-r)|^2 := by simpa only [Real.norm_eq_abs] using mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
    _ ≤ Real.exp (ρ.bound*|r|)*(ρ.bound*|s-r|)^2 := by gcongr; rw [abs_mul]; gcongr
    _ = _ := by ring

theorem expCLM_remainder {r s : ℝ} (hs : ρ.bound*|s-r| ≤ 1) :
    ‖ρ.expCLM (E := E) s - ρ.expCLM r - (s-r) • ρ.expDerivativeCLM r‖ ≤
      (Real.exp (ρ.bound*|r|)*ρ.bound^2)*|s-r|^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [ρ.expCLM_ae s u, ρ.expCLM_ae r u, ρ.expDerivativeCLM_ae r u, ρ.bounded,
    Lp.coeFn_sub (ρ.expCLM s u) (ρ.expCLM r u),
    Lp.coeFn_smul (s-r) (ρ.expDerivativeCLM r u),
    Lp.coeFn_sub (ρ.expCLM s u - ρ.expCLM r u) ((s-r) • ρ.expDerivativeCLM r u)]
    with x h1 h2 h3 hx h4 h5 h6
  change ‖((ρ.expCLM s u - ρ.expCLM r u) - (s-r) • ρ.expDerivativeCLM r u) x‖ ≤ _
  simp only [Pi.sub_apply, Pi.smul_apply] at h4 h5 h6
  rw [h6, h4, h5]
  simp only [h1, h2, h3, smul_smul, ← sub_smul, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (ρ.exp_scalar_remainder hx hs) (norm_nonneg _)

/-- Operator-norm derivative of the actual exponential L² multiplier. -/
theorem hasDerivAt_expCLM (r : ℝ) : HasDerivAt (ρ.expCLM (E := E)) (ρ.expDerivativeCLM r) r := by
  rw [hasDerivAt_iff_tendsto]
  have hsmall : ∀ᶠ s in nhds r, ρ.bound*|s-r| ≤ 1 := by
    have hc : ContinuousAt (fun s : ℝ => ρ.bound*|s-r|) r := by fun_prop
    have he := hc.tendsto.eventually (eventually_lt_nhds (show (fun s : ℝ => ρ.bound*|s-r|) r < 1 by simp))
    exact he.mono fun _ h => h.le
  have hc : ContinuousAt (fun s : ℝ => (Real.exp (ρ.bound*|r|)*ρ.bound^2)*|s-r|) r := by fun_prop
  have ht : Tendsto (fun s : ℝ => (Real.exp (ρ.bound*|r|)*ρ.bound^2)*|s-r|) (nhds r) (nhds 0) := by
    simpa using hc.tendsto
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)) ?_ ht
  filter_upwards [hsmall] with s hs
  have hh := mul_le_mul_of_nonneg_left (ρ.expCLM_remainder (E := E) hs) (inv_nonneg.mpr (norm_nonneg (s-r)))
  apply hh.trans_eq
  rw [Real.norm_eq_abs]
  by_cases hn : |s-r| = 0
  · rw [hn]; simp
  · field_simp
end Carleman.SpatialProfile
