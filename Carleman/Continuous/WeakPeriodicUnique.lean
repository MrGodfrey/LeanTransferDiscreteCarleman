module

public import Carleman.Continuous.WeakTimeEnergy
public import Carleman.Continuous.PeriodicEvolution

/-! Uniqueness for arbitrary genuine weak periodic solutions. The operator
domain is used only a.e., and both time orientations are covered. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem integrable_inner_of_memLp {f k : ℝ → H} {μ : Measure ℝ}
    (hf : MemLp f 2 μ) (hk : MemLp k 2 μ) : Integrable (fun t => inner ℝ (f t) (k t)) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hk.toLp k)).congr
  filter_upwards [hf.coeFn_toLp, hk.coeFn_toLp] with t ht hk
  rw [ht, hk]

namespace CoerciveForm
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (b : CoerciveForm H V)

omit [CompleteSpace H] in
theorem operator_energy_zero {v : b.domain} (hv : inner ℝ (v : H) (b.operator v) = 0) : v = 0 := by
  obtain ⟨c, hc, hbound⟩ := b.coercive
  have he : b.form (b.energy v) (b.energy v) = 0 := by
    rw [← b.operator_test, b.embed_energy, real_inner_comm]
    exact hv
  have hn := hbound (b.energy v)
  rw [he] at hn
  have hs : c * ‖b.energy v‖^2 ≤ 0 := by nlinarith [hn]
  have hs' := nonpos_of_mul_nonpos_right hs hc
  have hnorm : ‖b.energy v‖ = 0 := by nlinarith [norm_nonneg (b.energy v)]
  apply Subtype.ext
  rw [← b.embed_energy v, norm_eq_zero.mp hnorm, map_zero, Submodule.coe_zero]

/-- Homogeneous uniqueness for all weak trajectories and every a.e. nonnegative coefficient. -/
theorem weak_periodic_kernel {g : TimeGrid} (s : Orientation) (μ : ℝ → ℝ)
    (hμ : ∀ᵐ t ∂g.timeMeasure, 0 ≤ μ t)
    (u : PeriodicWeakTrajectory g b.domain b.operator)
    (he : ∀ᵐ t ∂g.timeMeasure, s.sign • u.derivative t +
      b.operator (u.domainValue t) + μ t • u.value t = 0) :
    ∀ t ∈ Icc 0 g.period, u.value t = 0 := by
  let a : ℝ → ℝ := fun t => inner ℝ (u.value t) (b.operator (u.domainValue t))
  let d : ℝ → ℝ := fun t => inner ℝ (u.value t) (u.derivative t)
  have hai : Integrable a g.timeMeasure := integrable_inner_of_memLp u.value_L2 u.operator_L2
  have hdi : Integrable d g.timeMeasure := integrable_inner_of_memLp u.value_L2 u.derivative_L2
  have hnon : 0 ≤ᵐ[g.timeMeasure] a := by
    filter_upwards [u.domainValue_ae] with t ht
    change 0 ≤ inner ℝ (u.value t) (b.operator (u.domainValue t))
    rw [← ht, real_inner_comm]
    exact b.operator_nonneg _
  have hle : a ≤ᵐ[g.timeMeasure] (fun t => -s.sign * d t) := by
    filter_upwards [he, hμ] with t ht hμt
    have hi := congrArg (fun z => inner ℝ (u.value t) z) ht
    simp only [inner_add_right, real_inner_smul_right, inner_zero_right,
      real_inner_self_eq_norm_sq] at hi
    change inner ℝ (u.value t) (b.operator (u.domainValue t)) ≤
      -s.sign * inner ℝ (u.value t) (u.derivative t)
    nlinarith [mul_nonneg hμt (sq_nonneg ‖u.value t‖)]
  have hint := integral_mono_ae hai (hdi.const_mul (-s.sign)) hle
  rw [integral_const_mul, u.time_energy_zero, mul_zero] at hint
  have hzero : (∫ t, a t ∂g.timeMeasure) = 0 := le_antisymm hint (integral_nonneg_of_ae hnon)
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnon hai).mp hzero
  have huv : u.value =ᵐ[g.timeMeasure] (fun _ => 0) := by
    filter_upwards [hae, u.domainValue_ae] with t ht hd
    change inner ℝ (u.value t) (b.operator (u.domainValue t)) = 0 at ht
    rw [← hd] at ht
    have hz := b.operator_energy_zero ht
    rw [← hd, hz, Submodule.coe_zero]
  have ha : u.value =ᵐ[volume.restrict (Icc 0 g.period)] (fun _ => 0) := by
    simpa only [TimeGrid.timeMeasure, restrict_Ioo_eq_restrict_Icc] using huv
  exact fun t ht => Measure.eqOn_Icc_of_ae_eq volume g.period_pos.ne ha u.continuous continuousOn_const ht

variable [CompleteSpace V]

theorem evolution_injective (g : TimeGrid) (s : Orientation) (μ : BoundedMultiplier g.timeMeasure)
    (hμ : ∀ᵐ t ∂g.timeMeasure, 0 ≤ μ.value t) :
    Function.Injective (b.evolution g s μ) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro p hp
  change p = 0
  have he : b.evolution g s μ p = 0 := hp
  have hae := (b.evolution_eq_iff g s μ p 0).mp he
  have hz := b.weak_periodic_kernel s μ.value hμ p.toTrajectory (by
    filter_upwards [hae, Lp.coeFn_zero (E := H) (p := 2) (μ := g.timeMeasure)] with t ht h0
    exact ht.trans h0)
  apply PeriodicGraph.trace_injective
  apply ContinuousMap.ext
  intro t
  have ht := hz t t.property
  change g.clampPath p.val.1 t = 0 at ht
  rw [g.clampPath_on _ _ t.property] at ht
  exact ht

/-- Two arbitrary original weak trajectories with the same load have identical closed-period values. -/
theorem weak_periodic_unique (g : TimeGrid) (s : Orientation) (μ : BoundedMultiplier g.timeMeasure)
    (hμ : ∀ᵐ t ∂g.timeMeasure, 0 ≤ μ.value t) (f : Lp H 2 g.timeMeasure)
    (u v : PeriodicWeakTrajectory g b.domain b.operator)
    (hu : ∀ᵐ t ∂g.timeMeasure, s.sign • u.derivative t + b.operator (u.domainValue t) +
      μ.value t • u.value t = f t)
    (hv : ∀ᵐ t ∂g.timeMeasure, s.sign • v.derivative t + b.operator (v.domainValue t) +
      μ.value t • v.value t = f t) :
    ∀ t ∈ Icc 0 g.period, u.value t = v.value t := by
  have lift_eq (w : PeriodicWeakTrajectory g b.domain b.operator)
      (hw : ∀ᵐ t ∂g.timeMeasure, s.sign • w.derivative t + b.operator (w.domainValue t) +
        μ.value t • w.value t = f t) : b.evolution g s μ w.toPeriodicGraph = f := by
    apply (b.evolution_eq_iff g s μ w.toPeriodicGraph f).mpr
    filter_upwards [hw, w.toPeriodicGraph_derivative_ae, w.toPeriodicGraph_operator_ae,
      ae_restrict_mem measurableSet_Ioo] with t ht hd ha hm
    rw [hd, ha, w.toPeriodicGraph_value_on t ⟨hm.1.le, hm.2.le⟩]
    exact ht
  have he := b.evolution_injective g s μ hμ ((lift_eq u hu).trans (lift_eq v hv).symm)
  intro t ht
  rw [← u.toPeriodicGraph_value_on t ht, he, v.toPeriodicGraph_value_on t ht]

end CoerciveForm
end Carleman
