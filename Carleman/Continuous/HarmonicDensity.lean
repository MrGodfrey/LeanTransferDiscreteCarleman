module

public import Carleman.Continuous.FiniteHarmonic
public import Carleman.Continuous.WeakPeriodicUnique
public import Mathlib.Analysis.Fourier.AddCircle

/-! Density of actual H-valued finite time harmonics in the Bochner L²
load space. No separability assumption is added to H. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
namespace TimeGrid
variable (g : TimeGrid)

theorem fourier_coe_trig (n : ℤ) (t : ℝ) :
    fourier n (t : AddCircle g.period) =
      (Real.cos (g.angularFrequency n * t) : ℂ) + Real.sin (g.angularFrequency n * t) * Complex.I := by
  rw [fourier_coe_apply]
  have he : 2 * (Real.pi : ℂ) * Complex.I * n * t / g.period =
      ((g.angularFrequency n * t : ℝ) : ℂ) * Complex.I := by
    simp only [angularFrequency, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_intCast,
      Complex.ofReal_ofNat]
    ring
  rw [he, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- Scalar real Fourier completeness on the original unnormalized time interval. -/
theorem scalar_eq_zero_of_harmonics {f : ℝ → ℝ} (hf : MemLp f 2 g.timeMeasure)
    (hc : ∀ n : ℤ, (∫ t, Real.cos (g.angularFrequency n * t) * f t ∂g.timeMeasure) = 0)
    (hs : ∀ n : ℤ, (∫ t, Real.sin (g.angularFrequency n * t) * f t ∂g.timeMeasure) = 0) :
    f =ᵐ[g.timeMeasure] (fun _ => 0) := by
  let F : ℝ → ℂ := fun t => (f t : ℂ)
  have hF : MemLp F 2 g.timeMeasure := hf.continuousLinearMap_comp Complex.ofRealCLM
  have hFIoc : MemLp F 2 (volume.restrict (Ioc 0 g.period)) := by
    simpa only [TimeGrid.timeMeasure, restrict_Ioo_eq_restrict_Ioc] using hF
  have hz (n : ℤ) : fourierCoeffOn g.period_pos F n = 0 := by
    rw [fourierCoeffOn_eq_integral, sub_zero, ← g.timeIntegral_eq_intervalIntegral]
    suffices (∫ t, fourier (-n) (t : AddCircle g.period) • F t ∂g.timeMeasure) = 0 by
      rw [this, smul_zero]
    have hci : Integrable (fun t => Real.cos (g.angularFrequency (-n) * t) * f t) g.timeMeasure :=
      memLp_one_iff_integrable.mp
        ((g.memLp_of_continuousOn (by fun_prop)).mul hf)
    have hsi : Integrable (fun t => Real.sin (g.angularFrequency (-n) * t) * f t) g.timeMeasure :=
      memLp_one_iff_integrable.mp
        ((g.memLp_of_continuousOn (by fun_prop)).mul hf)
    have heq : (fun t : ℝ => fourier (-n) (t : AddCircle g.period) • F t) =
        (fun t => ((Real.cos (g.angularFrequency (-n) * t) * f t : ℝ) : ℂ) +
          ((Real.sin (g.angularFrequency (-n) * t) * f t : ℝ) : ℂ) * Complex.I) := by
      funext t
      rw [g.fourier_coe_trig]
      simp only [F, smul_eq_mul, Complex.ofReal_mul]
      ring
    have hci' : Integrable (fun t => ((Real.cos (g.angularFrequency (-n) * t) * f t : ℝ) : ℂ))
        g.timeMeasure := by
      simpa only [Complex.ofRealCLM_apply] using Complex.ofRealCLM.integrable_comp hci
    have hsi' : Integrable (fun t => ((Real.sin (g.angularFrequency (-n) * t) * f t : ℝ) : ℂ))
        g.timeMeasure := by
      simpa only [Complex.ofRealCLM_apply] using Complex.ofRealCLM.integrable_comp hsi
    rw [heq, integral_add hci' (hsi'.mul_const Complex.I),
      integral_mul_const, integral_complex_ofReal, integral_complex_ofReal, hc, hs]
    simp
  have hp := (hasSum_sq_fourierCoeffOn g.period_pos hFIoc).tsum_eq
  simp only [hz, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    tsum_zero, sub_zero, smul_eq_mul] at hp
  have hint : (∫ t, ‖F t‖^2 ∂g.timeMeasure) = 0 := by
    rw [g.timeIntegral_eq_intervalIntegral]
    exact (mul_eq_zero.mp hp.symm).resolve_left (inv_ne_zero g.period_pos.ne')
  have hi : Integrable (fun t => ‖F t‖^2) g.timeMeasure :=
    (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have ha := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun t => sq_nonneg ‖F t‖) hi).mp hint
  filter_upwards [ha] with t ht
  have hzero : F t = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp ht)
  exact Complex.ofReal_eq_zero.mp hzero

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def harmonicSpan : Submodule ℝ (Lp H 2 g.timeMeasure) :=
  Submodule.span ℝ {v | ∃ (n : ℤ) (f k : H), v = g.harmonicLp n f k}

/-- All finite harmonic loads are dense, even for nonseparable H. -/
theorem harmonicSpan_dense : Dense (g.harmonicSpan (H := H) : Set (Lp H 2 g.timeMeasure)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  apply le_antisymm ?_ bot_le
  intro v hv
  change v = 0
  have hh (n : ℤ) (f k : H) : inner ℝ v (g.harmonicLp n f k) = 0 := by
    rw [real_inner_comm]
    apply (g.harmonicSpan.mem_orthogonal v).mp hv
    change g.harmonicLp n f k ∈ Submodule.span ℝ _
    exact Submodule.subset_span ⟨n, f, k, rfl⟩
  have hc (h : H) (n : ℤ) :
      (∫ t, Real.cos (g.angularFrequency n * t) * inner ℝ (v t) h ∂g.timeMeasure) = 0 := by
    have he := hh n h 0
    rw [L2.inner_def] at he
    convert he using 1
    apply integral_congr_ae
    filter_upwards [g.harmonicLp_ae n h 0] with t ht
    rw [ht]
    simp [harmonicValue, real_inner_smul_right]
  have hs (h : H) (n : ℤ) :
      (∫ t, Real.sin (g.angularFrequency n * t) * inner ℝ (v t) h ∂g.timeMeasure) = 0 := by
    have he := hh n 0 h
    rw [L2.inner_def] at he
    convert he using 1
    apply integral_congr_ae
    filter_upwards [g.harmonicLp_ae n 0 h] with t ht
    rw [ht]
    simp [harmonicValue, real_inner_smul_right]
  have hscalar (h : H) : (fun t => inner ℝ (v t) h) =ᵐ[g.timeMeasure] (fun _ => 0) :=
    g.scalar_eq_zero_of_harmonics ((Lp.memLp v).inner_const h) (hc h) (hs h)
  apply IsWeakTimeClass.eq_zero_of_tests
  intro φ h
  rw [inner_scalarTensor]
  calc
    _ = ∫ _ : ℝ, (0 : ℝ) ∂g.timeMeasure := by
      apply integral_congr_ae
      filter_upwards [hscalar h] with t ht
      rw [ht, mul_zero]
    _ = 0 := integral_zero _ _

end TimeGrid
end Carleman
