module

public import Carleman.Continuous.PeriodicSolutionOperator
public import Mathlib.Topology.MetricSpace.Contracting

/-! Arbitrary nonnegative bounded measurable coefficients, including
frozen nodal coefficients: existence follows from the constructed constant
solver and a strict L² contraction. The coefficient is not assumed smooth. -/
@[expose] public noncomputable section
open MeasureTheory
open scoped NNReal
namespace Carleman
namespace BoundedMultiplier
variable {ν : Measure ℝ} (μ : BoundedMultiplier ν)

def positiveComplement (hμ : ∀ᵐ t ∂ν, 0 ≤ μ.value t) : BoundedMultiplier ν where
  value t := μ.bound - μ.value t
  measurable := aestronglyMeasurable_const.sub μ.measurable
  bound := μ.bound
  bound_nonneg := μ.bound_nonneg
  bounded := by
    filter_upwards [hμ, μ.bounded] with t ht hb
    have hupper := (le_abs_self (μ.value t)).trans hb
    rw [abs_of_nonneg (sub_nonneg.mpr hupper)]
    linarith
end BoundedMultiplier

namespace CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V) (g : TimeGrid) (s : Orientation)

theorem evolution_positiveComplement (μ : BoundedMultiplier g.timeMeasure)
    (hμ : ∀ᵐ t ∂g.timeMeasure, 0 ≤ μ.value t) (p : b.PeriodicGraph g) :
    b.evolution g s μ p = b.evolution g s (g.constantMultiplier μ.bound) p -
      (μ.positiveComplement hμ).map (g.pathL2 p.val.1) := by
  apply Lp.ext
  filter_upwards [b.evolution_ae g s μ p,
    b.evolution_ae g s (g.constantMultiplier μ.bound) p,
    Lp.coeFn_sub (b.evolution g s (g.constantMultiplier μ.bound) p)
      ((μ.positiveComplement hμ).map (g.pathL2 p.val.1)),
    (μ.positiveComplement hμ).map_ae (g.pathL2 p.val.1), g.pathL2_ae p.val.1]
    with t h1 h2 h3 h4 hv
  simp only [Pi.sub_apply] at h3
  rw [h1, h3, h2, h4, hv]
  change s.sign • p.toTrajectory.derivative t + b.operator (p.toTrajectory.domainValue t) +
    μ.value t • p.toTrajectory.value t =
    (s.sign • p.toTrajectory.derivative t + b.operator (p.toTrajectory.domainValue t) +
      μ.bound • p.toTrajectory.value t) - (μ.bound - μ.value t) • p.toTrajectory.value t
  rw [sub_smul]
  abel

/-- Surjectivity for arbitrary L² loads and every bounded measurable nonnegative coefficient. -/
theorem evolution_surjective (μ : BoundedMultiplier g.timeMeasure)
    (hμ : ∀ᵐ t ∂g.timeMeasure, 0 ≤ μ.value t) : Function.Surjective (b.evolution g s μ) := by
  intro f
  obtain ⟨α, hαpos, hα⟩ := b.exists_operator_positive_constant
  let R := μ.bound
  have hR : 0 ≤ R := μ.bound_nonneg
  have hsum : 0 < α+R := add_pos_of_pos_of_nonneg hαpos hR
  let ν := μ.positiveComplement hμ
  let S := b.constantStateSolve g s R hR
  let F : Lp H 2 g.timeMeasure → Lp H 2 g.timeMeasure := fun v => S (f + ν.continuousLinearMap v)
  let K : ℝ≥0 := ⟨R/(α+R), div_nonneg hR hsum.le⟩
  have hc : ContractingWith K F := by
    constructor
    · change R/(α+R) < 1
      rw [div_lt_one hsum]
      linarith
    · apply LipschitzWith.of_dist_le_mul
      intro v w
      have he : F v - F w = S (ν.continuousLinearMap (v-w)) := by
        simp only [F, map_add, map_sub, add_sub_add_left_eq_sub]
      rw [dist_eq_norm, dist_eq_norm, he]
      have hb := b.constantStateSolve_bound g s R hR α hα (ν.continuousLinearMap (v-w))
      have hn := ν.seminorm_le (v-w)
      change ‖ν.continuousLinearMap (v-w)‖ ≤ R * ‖v-w‖ at hn
      change ‖S (ν.continuousLinearMap (v-w))‖ ≤ (R/(α+R))*‖v-w‖
      apply (mul_le_mul_iff_right₀ hsum).mp
      have heq : (α+R) * (R/(α+R)*‖v-w‖) = R * ‖v-w‖ := by field_simp
      rw [heq]
      exact hb.trans hn
  let v := hc.fixedPoint F
  have hv : F v = v := hc.fixedPoint_isFixedPt
  let p := b.constantSolve g s R hR (f + ν.continuousLinearMap v)
  have hvalue : g.pathL2 p.val.1 = v := hv
  refine ⟨p, ?_⟩
  rw [b.evolution_positiveComplement g s μ hμ p]
  have he : b.evolution g s (g.constantMultiplier μ.bound) p = f + ν.continuousLinearMap v :=
    b.constantSolve_equation g s R hR _
  rw [he, hvalue]
  exact add_sub_cancel_right _ _

theorem existsUnique_variable_periodic (μ : BoundedMultiplier g.timeMeasure)
    (hμ : ∀ᵐ t ∂g.timeMeasure, 0 ≤ μ.value t) (f : Lp H 2 g.timeMeasure) :
    ∃! p : b.PeriodicGraph g, b.evolution g s μ p = f := by
  obtain ⟨p, hp⟩ := b.evolution_surjective g s μ hμ f
  exact ⟨p, hp, fun q hq => b.evolution_injective g s μ hμ (hq.trans hp.symm)⟩

theorem exists_variable_weak_periodic (μ : BoundedMultiplier g.timeMeasure)
    (hμ : ∀ᵐ t ∂g.timeMeasure, 0 ≤ μ.value t) (f : Lp H 2 g.timeMeasure) :
    ∃ u : PeriodicWeakTrajectory g b.domain b.operator, ∀ᵐ t ∂g.timeMeasure,
      s.sign • u.derivative t + b.operator (u.domainValue t) + μ.value t • u.value t = f t := by
  obtain ⟨p, hp⟩ := b.evolution_surjective g s μ hμ f
  exact ⟨p.toTrajectory, (b.evolution_eq_iff g s μ p f).mp hp⟩

theorem exists_frozen_weak_periodic (μ : g.Sequence ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (f : Lp H 2 g.timeMeasure) :
    ∃ u : PeriodicWeakTrajectory g b.domain b.operator, ∀ᵐ t ∂g.timeMeasure,
      s.sign • u.derivative t + b.operator (u.domainValue t) + s.extension g μ t • u.value t = f t := by
  apply b.exists_variable_weak_periodic g s (s.frozenMultiplier g μ) _ f
  apply Filter.Eventually.of_forall
  intro t
  change 0 ≤ s.extension g μ t
  cases s <;> exact hμ _

theorem IsAssociated.exists_variable_weak_periodic {D : Submodule ℝ H} {A : D →ₗ[ℝ] H}
    (h : b.IsAssociated A) (μ : BoundedMultiplier g.timeMeasure)
    (hμ : ∀ᵐ t ∂g.timeMeasure, 0 ≤ μ.value t) (f : Lp H 2 g.timeMeasure) :
    ∃ u : PeriodicWeakTrajectory g D A, ∀ᵐ t ∂g.timeMeasure,
      s.sign • u.derivative t + A (u.domainValue t) + μ.value t • u.value t = f t := by
  have hd := h.domain_eq b
  subst D
  have ha := h.operator_eq b
  subst A
  exact b.exists_variable_weak_periodic g s μ hμ f

/-- Uniqueness transfers to the full original associated domain and operator. -/
theorem IsAssociated.weak_periodic_unique {D : Submodule ℝ H} {A : D →ₗ[ℝ] H}
    (h : b.IsAssociated A) (μ : BoundedMultiplier g.timeMeasure)
    (hμ : ∀ᵐ t ∂g.timeMeasure, 0 ≤ μ.value t) (f : Lp H 2 g.timeMeasure)
    (u v : PeriodicWeakTrajectory g D A)
    (hu : ∀ᵐ t ∂g.timeMeasure, s.sign • u.derivative t + A (u.domainValue t) +
      μ.value t • u.value t = f t)
    (hv : ∀ᵐ t ∂g.timeMeasure, s.sign • v.derivative t + A (v.domainValue t) +
      μ.value t • v.value t = f t) :
    ∀ t ∈ Set.Icc 0 g.period, u.value t = v.value t := by
  have hd := h.domain_eq b
  subst D
  have ha := h.operator_eq b
  subst A
  exact b.weak_periodic_unique g s μ hμ f u v hu hv

end CoerciveForm
end Carleman
