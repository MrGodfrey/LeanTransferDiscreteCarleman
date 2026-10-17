module

public import Carleman.Continuous.ConstantPeriodicExistence

/-! Actual time-dependent coefficient energy. Absolute continuity is a
coefficient regularity condition, not a regularity assumption on D(A) values. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem PeriodicWeakTrajectory.coefficient_energy {g : TimeGrid} {D : Submodule ℝ H}
    {A : D →ₗ[ℝ] H} (u : PeriodicWeakTrajectory g D A)
    (μ : BoundedMultiplier g.timeMeasure)
    (hμ : AbsolutelyContinuousOnInterval μ.value 0 g.period)
    (hper : μ.value 0 = μ.value g.period) :
    2 * (∫ t, μ.value t * inner ℝ (u.value t) (u.derivative t) ∂g.timeMeasure) =
      -(∫ t, deriv μ.value t * ‖u.value t‖^2 ∂g.timeMeasure) := by
  have huAC := u.weak_derivative.absolutelyContinuous u.continuous u.derivative_L2
  have hnAC : AbsolutelyContinuousOnInterval (fun t => ‖u.value t‖) 0 g.period :=
    lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval huAC
  have hsAC : AbsolutelyContinuousOnInterval (fun t => ‖u.value t‖^2) 0 g.period := by
    simpa only [pow_two] using hnAC.fun_mul hnAC
  have hc : ContinuousOn (fun t => ‖u.value t‖^2) (uIcc 0 g.period) := hsAC.continuousOn
  have hfirst : Integrable (fun t => deriv μ.value t * ‖u.value t‖^2) g.timeMeasure := by
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le g.period_pos.le).mp
      (hμ.intervalIntegrable_deriv.mul_continuousOn hc)
  have hsecond : Integrable (fun t => μ.value t * inner ℝ (u.value t) (u.derivative t))
      g.timeMeasure :=
    (integrable_inner_of_memLp u.value_L2 u.derivative_L2).bdd_mul μ.measurable
      (by simpa only [Real.norm_eq_abs] using μ.bounded)
  have he := (hμ.fun_mul hsAC).integral_deriv_eq_sub
  rw [← g.timeIntegral_eq_intervalIntegral, ← hper, ← u.periodic_trace, sub_self] at he
  have hder : (fun t => deriv (fun t => μ.value t * ‖u.value t‖^2) t) =ᵐ[g.timeMeasure]
      (fun t => deriv μ.value t * ‖u.value t‖^2 +
        2 * (μ.value t * inner ℝ (u.value t) (u.derivative t))) := by
    filter_upwards [ae_restrict_of_ae hμ.ae_differentiableAt,
      u.weak_derivative.ae_hasDerivAt u.continuous u.derivative_L2,
      ae_restrict_mem measurableSet_Ioo] with t hμt hut ht
    have hm : t ∈ uIcc 0 g.period := by
      simpa only [uIcc_of_le g.period_pos.le] using (show t ∈ Icc 0 g.period from ⟨ht.1.le, ht.2.le⟩)
    rw [((hμt hm).hasDerivAt.fun_mul hut.norm_sq).deriv]
    ring
  rw [integral_congr_ae hder, integral_add hfirst (hsecond.const_mul 2), integral_const_mul] at he
  linarith

namespace CoerciveForm
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V) (g : TimeGrid)

theorem periodic_coefficient_inner (p : b.PeriodicGraph g) (μ : BoundedMultiplier g.timeMeasure) :
    inner ℝ p.val.2.1 (μ.map (g.pathL2 p.val.1)) =
      ∫ t, μ.value t * inner ℝ (p.toTrajectory.value t) (p.toTrajectory.derivative t) ∂g.timeMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [μ.map_ae (g.pathL2 p.val.1), g.pathL2_ae p.val.1] with t hm hv
  rw [hm, hv, real_inner_smul_right, real_inner_comm]
  rfl

theorem periodic_coefficient_sq (p : b.PeriodicGraph g) (μ : BoundedMultiplier g.timeMeasure) :
    ‖μ.map (g.pathL2 p.val.1)‖^2 =
      ∫ t, (μ.value t)^2 * ‖p.toTrajectory.value t‖^2 ∂g.timeMeasure := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [μ.map_ae (g.pathL2 p.val.1), g.pathL2_ae p.val.1] with t hm hv
  rw [real_inner_self_eq_norm_sq, hm, hv, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rfl

omit [CompleteSpace H] in
theorem periodic_coefficient_nonneg (p : b.PeriodicGraph g) (μ : BoundedMultiplier g.timeMeasure)
    (hμ : ∀ᵐ t ∂g.timeMeasure, 0 ≤ μ.value t) :
    0 ≤ inner ℝ p.val.2.2 (μ.map (g.pathL2 p.val.1)) := by
  rw [L2.inner_def]
  apply integral_nonneg_of_ae
  have hg := (b.timeOperatorGraph_ae g.timeMeasure _ _).mp
    ((b.periodicGraph_mem g p.val).mp p.property).2.1
  filter_upwards [hg, μ.map_ae (g.pathL2 p.val.1), hμ] with t ht hm hμt
  obtain ⟨x, hx, ha⟩ := (b.operatorGraph_mem _ _).mp ht
  rw [hm, ← hx, ← ha, real_inner_smul_right]
  exact mul_nonneg hμt (b.operator_nonneg x)

/-- A true coefficient derivative bound yields the original unweighted
shift graph estimate, uniformly in T and in the size of μ. -/
theorem variable_periodic_graph_sq (s : Orientation) (μ : BoundedMultiplier g.timeMeasure)
    (hμ : ∀ᵐ t ∂g.timeMeasure, 0 ≤ μ.value t)
    (hAC : AbsolutelyContinuousOnInterval μ.value 0 g.period)
    (hper : μ.value 0 = μ.value g.period) (δ : ℝ)
    (hd : ∀ᵐ t ∂g.timeMeasure, |deriv μ.value t| ≤ δ * (μ.value t)^2)
    (p : b.PeriodicGraph g) :
    ‖p.val.2.1‖^2 + ‖p.val.2.2‖^2 + (1-δ)*‖μ.map (g.pathL2 p.val.1)‖^2 ≤
      ‖b.evolution g s μ p‖^2 := by
  have hcoeff := p.toTrajectory.coefficient_energy μ hAC hper
  rw [← b.periodic_coefficient_inner g p μ] at hcoeff
  have hi : Integrable (fun t => deriv μ.value t * ‖p.toTrajectory.value t‖^2) g.timeMeasure :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le g.period_pos.le).mp
      (hAC.intervalIntegrable_deriv.mul_continuousOn (by
        simpa only [uIcc_of_le g.period_pos.le] using p.toTrajectory.continuous.norm.fun_pow 2))
  have hsq : Integrable (fun t => (μ.value t)^2 * ‖p.toTrajectory.value t‖^2) g.timeMeasure := by
    have hm := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable
      (μ.map (g.pathL2 p.val.1)))).mp (Lp.memLp _)
    apply hm.congr
    filter_upwards [μ.map_ae (g.pathL2 p.val.1), g.pathL2_ae p.val.1] with t h1 h2
    rw [h1, h2, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rfl
  have hs : |s.sign| = 1 := by cases s <;> norm_num [Orientation.sign]
  have hs2 : s.sign^2 = 1 := by cases s <;> norm_num [Orientation.sign]
  have hbound : s.sign * (∫ t, deriv μ.value t * ‖p.toTrajectory.value t‖^2 ∂g.timeMeasure) ≤
      δ * ‖μ.map (g.pathL2 p.val.1)‖^2 := by
    rw [b.periodic_coefficient_sq, ← integral_const_mul, ← integral_const_mul]
    apply integral_mono_ae (hi.const_mul s.sign) (hsq.const_mul δ)
    filter_upwards [hd] with t ht
    have hh : s.sign * deriv μ.value t ≤ δ*(μ.value t)^2 := by
      calc
        _ ≤ |s.sign * deriv μ.value t| := le_abs_self _
        _ = |deriv μ.value t| := by rw [abs_mul, hs, one_mul]
        _ ≤ _ := ht
    nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg ‖p.toTrajectory.value t‖)]
  have hnon := b.periodic_coefficient_nonneg g p μ hμ
  have hcoeffSign := congrArg (fun x : ℝ => s.sign*x) hcoeff
  have he : b.evolution g s μ p = s.sign • p.val.2.1 + p.val.2.2 + μ.map (g.pathL2 p.val.1) := rfl
  rw [he]
  simp only [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hs2, one_mul,
    inner_add_left, real_inner_smul_left, b.periodic_graph_cross_zero g p]
  nlinarith [hcoeffSign]

end CoerciveForm
end Carleman
