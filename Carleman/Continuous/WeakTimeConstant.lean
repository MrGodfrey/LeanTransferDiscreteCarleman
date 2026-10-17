module

public import Carleman.Continuous.TimeTestPrimitive

/-! A distributionally constant time function is genuinely constant a.e.;
continuous representatives agree at every point of the closed period. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Carleman
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem TimeGrid.timeIntegral_of_test_support (g : TimeGrid) {f : ℝ → H}
    (hs : Function.support f ⊆ Ioo 0 g.period) :
    (∫ t, f t ∂g.timeMeasure) = ∫ t, f t := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  by_contra hn
  exact ht (hs hn)

theorem HasWeakTimeDerivative.ae_const_of_zero {g : TimeGrid} {u : ℝ → H}
    (hu : MemLp u 2 g.timeMeasure) (hw : HasWeakTimeDerivative g u (fun _ => 0)) :
    ∃ c : H, u =ᵐ[g.timeMeasure] (fun _ => c) := by
  obtain ⟨ψ, hψ, hcψ, hsψ, hiψ⟩ := exists_time_test_integral_one g
  let c : H := ∫ t, ψ t • u t ∂g.timeMeasure
  have hint (φ : ℝ → ℝ) (hφ : Continuous φ) :
      Integrable (fun t => φ t • u t) g.timeMeasure :=
    memLp_one_iff_integrable.mp ((g.memLp_of_continuousOn hφ.continuousOn).smul hu)
  have htest (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
      (hsφ : tsupport φ ⊆ Ioo 0 g.period) :
      (∫ t, φ t • u t ∂g.timeMeasure) = (∫ t, φ t) • c := by
    let k : ℝ := ∫ t, φ t
    let f : ℝ → ℝ := fun t => φ t - k * ψ t
    have hf : ContDiff ℝ ∞ f := hφ.sub (contDiff_const.mul hψ)
    have hcf : HasCompactSupport f := hcφ.sub (hcψ.mul_left (f := fun _ => k))
    have hsf : tsupport f ⊆ Ioo 0 g.period :=
      (tsupport_sub _ _).trans (union_subset hsφ ((tsupport_mul_subset_right (f := fun _ => k) (g := ψ)).trans hsψ))
    have hif : ∫ t, f t = 0 := by
      change (∫ t, φ t - k * ψ t) = 0
      rw [integral_sub (hφ.continuous.integrable_of_hasCompactSupport hcφ)
        ((hψ.continuous.integrable_of_hasCompactSupport hcψ).const_mul k), integral_const_mul, hiψ]
      dsimp [k]
      ring
    obtain ⟨F, hF, hcF, hsF, hdF⟩ := exists_time_test_primitive hf hcf hsf hif
    have hz := hw F hF hcF hsF
    rw [hdF] at hz
    simp only [smul_zero, integral_zero, neg_zero] at hz
    change (∫ t, (φ t - k * ψ t) • u t ∂g.timeMeasure) = 0 at hz
    simp_rw [sub_smul, mul_smul] at hz
    have hik : Integrable (fun t => k • (ψ t • u t)) g.timeMeasure := by
      change Integrable (k • (fun t => ψ t • u t)) g.timeMeasure
      exact (hint ψ hψ.continuous).smul k
    change (∫ t, φ t • u t - k • (ψ t • u t) ∂g.timeMeasure) = 0 at hz
    rw [integral_sub (hint φ hφ.continuous) hik, integral_smul] at hz
    exact sub_eq_zero.mp hz
  have huc : MemLp (fun t => u t - c) 2 g.timeMeasure := hu.sub (memLp_const c)
  have hz := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((huc.locallyIntegrable (by norm_num)).locallyIntegrableOn (Ioo 0 g.period))
    (fun φ hφ hcφ hsφ => by
      have hcint : Integrable (fun t => φ t • c) g.timeMeasure :=
        (MemLp.integrable (by norm_num) (g.memLp_of_continuousOn hφ.continuous.continuousOn)).smul_const c
      simp_rw [smul_sub]
      rw [integral_sub (hint φ hφ.continuous) hcint, integral_smul_const, htest φ hφ hcφ hsφ]
      rw [g.timeIntegral_of_test_support (H := ℝ) ((subset_tsupport φ).trans hsφ)]
      exact sub_self _)
  refine ⟨c, ?_⟩
  filter_upwards [hz, ae_restrict_mem measurableSet_Ioo] with t ht hmem
  exact sub_eq_zero.mp (ht hmem)

/-- The a.e. constant extends to both endpoint traces by H continuity. -/
theorem HasWeakTimeDerivative.const_of_zero {g : TimeGrid} {u : ℝ → H}
    (hu : ContinuousOn u (Icc 0 g.period))
    (hw : HasWeakTimeDerivative g u (fun _ => 0)) :
    ∀ t ∈ Icc 0 g.period, u t = u 0 := by
  obtain ⟨c, hc⟩ := hw.ae_const_of_zero (g.memLp_of_continuousOn hu)
  have ha : u =ᵐ[volume.restrict (Icc 0 g.period)] (fun _ => c) := by
    simpa only [TimeGrid.timeMeasure, restrict_Ioo_eq_restrict_Icc] using hc
  have he := Measure.eqOn_Icc_of_ae_eq volume g.period_pos.ne ha hu continuousOn_const
  intro t ht
  exact (he ht).trans (he ⟨le_rfl, g.period_pos.le⟩).symm

end Carleman
