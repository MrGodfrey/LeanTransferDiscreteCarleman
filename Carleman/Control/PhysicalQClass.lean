module

public import Carleman.Control.PhysicalBaseAmplitude
public import Carleman.Control.PhysicalParameterChoice

/-! Full original two-derivative weight conditions and a uniform base choice. -/
@[expose] public noncomputable section
namespace Carleman.Physical

theorem physicalWeightSecondDerivative_periodic (qb δ T : ℝ) (hT : T ≠ 0) :
    Function.Periodic (physicalWeightSecondDerivative qb δ T) T := by
  intro t
  have he : Real.pi*(t+T)/T = Real.pi*t/T+Real.pi := by field_simp
  simp [physicalWeightSecondDerivative,physicalWeightDenom,he,Real.sin_add_pi,Real.cos_add_pi]

/-- Actual derivatives of a globally smooth periodic representative; in particular
all original C² traces on the closed physical interval match. -/
structure PhysicalQClass (w : TimeWeight) (T β qc : ℝ) : Prop where
  beta_pos : 0 < β
  qc_ge_one : 1 ≤ qc
  smooth : ContDiff ℝ ⊤ w.q
  lower : ∀ t, qc ≤ w.q t
  first_bound : ∀ t, |deriv w.q t| ≤ β*w.q t^2
  second_bound : ∀ t, |deriv (deriv w.q) t| ≤ β^2*w.q t^3
  endpoint : w.q 0 = w.q T
  first_endpoint : deriv w.q 0 = deriv w.q T
  second_endpoint : deriv (deriv w.q) 0 = deriv (deriv w.q) T

def PhysicalQClass.toRegularity {w : TimeWeight} {g : TimeGrid} {β qc : ℝ}
    (h : PhysicalQClass w g.period β qc) : TimeWeightRegularity w g β where
  beta_pos := h.beta_pos
  derivative := deriv w.q
  hasDeriv t _ := (h.smooth.differentiable (by norm_num) t).hasDerivAt.hasDerivWithinAt
  derivative_bound t _ := h.first_bound t
  endpoint := h.endpoint

theorem physicalWeight_lower_qc (qb δ T qc t : ℝ) (hqc : 1 ≤ qc)
    (hqb : 2*qc ≤ qb) (hδ : 0 < δ) (hδsmall : δ ≤ 1/16) :
    qc ≤ physicalWeight qb δ T t := by
  have hq : 0 ≤ qc := by linarith
  have hd : 0 < Real.sqrt (1+δ^2) := Real.sqrt_pos.mpr (by positivity)
  have hd2 : Real.sqrt (1+δ^2) ≤ 2 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 2)).mp
    rw [Real.sq_sqrt (by positivity)]
    nlinarith only [hδ,hδsmall]
  have hb := mul_le_mul_of_nonneg_left hd2 hq
  have hl : qc ≤ qb/Real.sqrt (1+δ^2) := (le_div_iff₀ hd).mpr (by linarith only [hb,hqb])
  exact hl.trans (physicalWeight_bounds qb δ T t (by linarith) hδ).1

theorem physicalTimeWeight_qclass (qb δ T β qc : ℝ)
    (hqc : 1 ≤ qc) (hqb : 2*qc ≤ qb) (hδ : 0 < δ) (hδsmall : δ ≤ 1/16)
    (hT : 0 < T) (hβ : 0 < β) (hroot : Real.sqrt (1+δ^2) ≤ qb)
    (hfirst : Real.pi/(qb*T) ≤ β) (hsecond : 4*Real.pi^2/(qb^2*T^2) ≤ β^2) :
    PhysicalQClass (physicalTimeWeight qb δ T hroot hδ) T β qc := by
  have hq : 0 < qb := by linarith
  refine ⟨hβ,hqc,physicalWeight_smooth qb δ T hδ,
    (fun t => physicalWeight_lower_qc qb δ T qc t hqc hqb hδ hδsmall),?_,?_,?_,?_,?_⟩
  · intro t
    change |deriv (physicalWeight qb δ T) t| ≤ β*physicalWeight qb δ T t^2
    rw [physicalWeight_deriv qb δ T hδ]
    exact (physicalWeight_derivative_bound qb δ T t hq hδ hT).trans
      (mul_le_mul_of_nonneg_right hfirst (sq_nonneg _))
  · intro t
    change |deriv (deriv (physicalWeight qb δ T)) t| ≤ β^2*physicalWeight qb δ T t^3
    rw [physicalWeight_second_deriv qb δ T hδ]
    exact (physicalWeight_second_derivative_bound qb δ T t hq hδ hT).trans
      (mul_le_mul_of_nonneg_right hsecond (pow_nonneg
        (div_nonneg hq.le (physicalWeightDenom_pos δ T t hδ).le) 3))
  · simpa only [physicalTimeWeight,zero_add] using
      (physicalWeight_periodic qb δ T (ne_of_gt hT) 0).symm
  · change deriv (physicalWeight qb δ T) 0 = deriv (physicalWeight qb δ T) T
    rw [physicalWeight_deriv qb δ T hδ]
    simpa only [zero_add] using (physicalWeightDerivative_periodic qb δ T (ne_of_gt hT) 0).symm
  · change deriv (deriv (physicalWeight qb δ T)) 0 = deriv (deriv (physicalWeight qb δ T)) T
    rw [physicalWeight_second_deriv qb δ T hδ]
    simpa only [zero_add] using (physicalWeightSecondDerivative_periodic qb δ T (ne_of_gt hT) 0).symm

/-- Cb may exceed any fixed requested lower bound, and is chosen before T, M,
the physical grid and S. The returned weight has exactly the original qmax=S. -/
theorem physical_qclass_uniform (β qc Cmin : ℝ) (hβ : 0 < β) (hqc : 1 ≤ qc) :
    ∃ Cb : ℝ, 0 < Cb ∧ Cmin ≤ Cb ∧ ∀ (g : TimeGrid) (M S : ℝ), 0 ≤ M →
      16*physicalBaseAmplitude Cb qc g.period M ≤ S →
      S ≤ physicalBaseAmplitude Cb qc g.period M*g.period/(4*g.dt) →
      ∃ w : TimeWeight,
        w.q = physicalWeight (physicalBaseAmplitude Cb qc g.period M)
          (physicalBaseAmplitude Cb qc g.period M/S) g.period ∧
        w.max = S ∧ PhysicalQClass w g.period β qc ∧
        Nonempty (TimeWeightRegularity w g β) := by
  let Cb := max 2 (max (2*Real.pi/β) Cmin)
  have hc2 : 2 ≤ Cb := le_max_left _ _
  have hcb : 2*Real.pi/β ≤ Cb := (le_max_left _ _).trans (le_max_right _ _)
  have hcm : Cmin ≤ Cb := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨Cb,by linarith only [hc2],hcm,?_⟩
  intro g M S hM hS hmesh
  let qb := physicalBaseAmplitude Cb qc g.period M
  obtain ⟨hq2,hqc2⟩ := physicalBaseAmplitude_ge_two Cb qc g.period M hc2 hqc g.period_pos hM
  obtain ⟨hδ,hδs,hmax,hroot,_⟩ := physical_delta_conditions g qb S hq2 hS hmesh
  obtain ⟨hb1,hb2⟩ := physicalBaseAmplitude_derivative_budgets Cb qc g.period M β
    (by linarith only [hc2]) hqc g.period_pos hM hβ hcb
  let w := physicalTimeWeight qb (qb/S) g.period hroot hδ
  have hw : PhysicalQClass w g.period β qc := physicalTimeWeight_qclass qb (qb/S) g.period β qc
    hqc hqc2 hδ hδs g.period_pos hβ hroot hb1 hb2
  exact ⟨w,rfl,hmax,hw,⟨hw.toRegularity⟩⟩

end Carleman.Physical
