module

public import Carleman.Weights.PeriodicPrimitive
public import Mathlib.Analysis.Calculus.TangentCone.Real

/-! A genuine C² periodic extension from closed-interval data with matching derivatives. -/
@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace Carleman

theorem exists_periodic_C2_extension {T : ℝ} (hT : 0 < T) {q : ℝ → ℝ}
    (hq : ContDiffOn ℝ 2 q (Icc 0 T))
    (he0 : q 0=q T)
    (he1 : derivWithin q (Icc 0 T) 0=derivWithin q (Icc 0 T) T)
    (he2 : derivWithin (derivWithin q (Icc 0 T)) (Icc 0 T) 0=
      derivWithin (derivWithin q (Icc 0 T)) (Icc 0 T) T) :
    ∃ Q : ℝ → ℝ, ContDiff ℝ 2 Q ∧ Function.Periodic Q T ∧
      ∀ t ∈ Icc 0 T, Q t=q t ∧ deriv Q t=derivWithin q (Icc 0 T) t ∧
        deriv (deriv Q) t=derivWithin (derivWithin q (Icc 0 T)) (Icc 0 T) t := by
  let dq := derivWithin q (Icc 0 T)
  let ddq := derivWithin dq (Icc 0 T)
  have hdq : ContDiffOn ℝ 1 dq (Icc 0 T) := hq.derivWithin (uniqueDiffOn_Icc hT) (by norm_num)
  have hddq : ContinuousOn ddq (Icc 0 T) := hdq.continuousOn_derivWithin (uniqueDiffOn_Icc hT) le_rfl
  obtain ⟨R,hR,hRp,hRe⟩ := exists_continuous_periodic_extension hT hddq he2
  have hderiv1 : ∀ t ∈ Icc 0 T, HasDerivWithinAt dq (R t) (Icc 0 T) t := by
    intro t ht
    rw [hRe ht]
    exact (hdq.differentiableOn (by norm_num) t ht).hasDerivWithinAt
  obtain ⟨P,hP,hPp,hPe⟩ := periodic_primitive_of_interval hT hdq.continuousOn hR hRp hderiv1 he1
  have hderiv0 : ∀ t ∈ Icc 0 T, HasDerivWithinAt q (P t) (Icc 0 T) t := by
    intro t ht
    rw [hPe ht]
    exact (hq.differentiableOn (by norm_num) t ht).hasDerivWithinAt
  have hPc : Continuous P := continuous_iff_continuousAt.mpr fun t => (hP t).continuousAt
  obtain ⟨Q,hQ,hQp,hQe⟩ := periodic_primitive_of_interval hT hq.continuousOn hPc hPp hderiv0 he0
  have hdQ : deriv Q=P := funext fun t => (hQ t).deriv
  have hdP : deriv P=R := funext fun t => (hP t).deriv
  have hP1 : ContDiff ℝ 1 P := contDiff_one_iff_deriv.mpr
    ⟨fun t => (hP t).differentiableAt,by rwa [hdP]⟩
  have hQ2 : ContDiff ℝ 2 Q := by
    rw [show (2 : ℕ∞ω)=1+1 by norm_num,contDiff_succ_iff_deriv]
    refine ⟨fun t => (hQ t).differentiableAt,by norm_num,?_⟩
    rwa [hdQ]
  refine ⟨Q,hQ2,hQp,?_⟩
  intro t ht
  exact ⟨hQe ht,by rw [hdQ]; exact hPe ht,by rw [hdQ,hdP]; exact hRe ht⟩

end Carleman
