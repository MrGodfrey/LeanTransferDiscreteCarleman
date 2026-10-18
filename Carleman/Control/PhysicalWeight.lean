module

public import Carleman.Weights.CellRegularity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The original regularized sine weight used in physical observability. -/
@[expose] public noncomputable section
namespace Carleman.Physical

def physicalWeightDenom (δ T t : ℝ) : ℝ :=
  Real.sqrt (Real.sin (Real.pi*t/T)^2+δ^2)

def physicalWeight (qb δ T t : ℝ) : ℝ := qb/physicalWeightDenom δ T t

theorem physicalWeightDenom_pos (δ T t : ℝ) (hδ : 0 < δ) :
    0 < physicalWeightDenom δ T t := by
  apply Real.sqrt_pos.mpr
  exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hδ)

theorem physicalWeightDenom_sq (δ T t : ℝ) :
    physicalWeightDenom δ T t ^ 2 = Real.sin (Real.pi*t/T)^2+δ^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem physicalWeightDenom_bounds (δ T t : ℝ) (hδ : 0 ≤ δ) :
    δ ≤ physicalWeightDenom δ T t ∧ physicalWeightDenom δ T t ≤ Real.sqrt (1+δ^2) := by
  constructor
  · apply (sq_le_sq₀ hδ (Real.sqrt_nonneg _)).mp
    change δ^2 ≤ physicalWeightDenom δ T t ^ 2
    rw [physicalWeightDenom_sq]
    linarith [sq_nonneg (Real.sin (Real.pi*t/T))]
  · apply Real.sqrt_le_sqrt
    linarith [Real.sin_sq_le_one (Real.pi*t/T)]

theorem physicalWeight_bounds (qb δ T t : ℝ) (hqb : 0 ≤ qb) (hδ : 0 < δ) :
    qb/Real.sqrt (1+δ^2) ≤ physicalWeight qb δ T t ∧ physicalWeight qb δ T t ≤ qb/δ := by
  obtain ⟨hl,hu⟩ := physicalWeightDenom_bounds δ T t hδ.le
  exact ⟨div_le_div_of_nonneg_left hqb (physicalWeightDenom_pos δ T t hδ) hu,
    div_le_div_of_nonneg_left hqb hδ hl⟩

theorem physicalWeight_zero (qb δ T : ℝ) (hδ : 0 ≤ δ) :
    physicalWeight qb δ T 0 = qb/δ := by
  simp [physicalWeight,physicalWeightDenom,Real.sqrt_sq hδ]

theorem physicalWeight_periodic (qb δ T : ℝ) (hT : T ≠ 0) :
    Function.Periodic (physicalWeight qb δ T) T := by
  intro t
  have he : Real.pi*(t+T)/T = Real.pi*t/T+Real.pi := by field_simp
  simp only [physicalWeight,physicalWeightDenom,he,Real.sin_add_pi,neg_sq]

theorem physicalWeightDenom_hasDerivAt (δ T t : ℝ) (hδ : 0 < δ) :
    HasDerivAt (physicalWeightDenom δ T)
      ((2*Real.sin (Real.pi*t/T)*(Real.cos (Real.pi*t/T)*(Real.pi/T)))/
        (2*physicalWeightDenom δ T t)) t := by
  have ha : HasDerivAt (fun s : ℝ => Real.pi*s/T) (Real.pi/T) t := by
    simpa only [id_eq,mul_one] using ((hasDerivAt_id t).const_mul Real.pi).div_const T
  have hs := ((ha.sin).pow 2).add_const (δ^2)
  have hp : 0 < Real.sin (Real.pi*t/T)^2+δ^2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hδ)
  change HasDerivAt (fun s => Real.sqrt (Real.sin (Real.pi*s/T)^2+δ^2)) _ _
  simpa only [physicalWeightDenom,Nat.cast_ofNat,Nat.reduceSub,pow_one,Pi.pow_apply] using hs.sqrt (ne_of_gt hp)

def physicalWeightDerivative (qb δ T t : ℝ) : ℝ :=
  -(qb*(Real.sin (Real.pi*t/T)*Real.cos (Real.pi*t/T)*(Real.pi/T)))/physicalWeightDenom δ T t^3

theorem physicalWeight_hasDerivAt (qb δ T t : ℝ) (hδ : 0 < δ) :
    HasDerivAt (physicalWeight qb δ T) (physicalWeightDerivative qb δ T t) t := by
  have hd := (hasDerivAt_const t qb).div (physicalWeightDenom_hasDerivAt δ T t hδ)
    (ne_of_gt (physicalWeightDenom_pos δ T t hδ))
  convert hd using 1
  · rfl
  · dsimp only [physicalWeightDerivative]
    field_simp
    ring

theorem physicalWeight_smooth (qb δ T : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ ⊤ (physicalWeight qb δ T) := by
  have ha : ContDiff ℝ ⊤ (fun t : ℝ => Real.pi*t/T) :=
    (contDiff_const.mul contDiff_id).div_const T
  have hs : ContDiff ℝ ⊤ (fun t => Real.sin (Real.pi*t/T)^2+δ^2) :=
    (ha.sin.pow 2).add contDiff_const
  have hp (t : ℝ) : Real.sin (Real.pi*t/T)^2+δ^2 ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hδ))
  exact contDiff_const.div (hs.sqrt hp) (fun t => ne_of_gt (physicalWeightDenom_pos δ T t hδ))

theorem physicalWeight_derivative_bound (qb δ T t : ℝ) (hqb : 0 < qb) (hδ : 0 < δ) (hT : 0 < T) :
    |physicalWeightDerivative qb δ T t| ≤ (Real.pi/(qb*T))*physicalWeight qb δ T t^2 := by
  have hD := physicalWeightDenom_pos δ T t hδ
  have hsin : |Real.sin (Real.pi*t/T)| ≤ physicalWeightDenom δ T t := by
    apply (sq_le_sq₀ (abs_nonneg _) hD.le).mp
    rw [sq_abs,physicalWeightDenom_sq]
    linarith [sq_nonneg δ]
  have hc : |Real.sin (Real.pi*t/T)*Real.cos (Real.pi*t/T)| ≤ physicalWeightDenom δ T t := by
    rw [abs_mul]
    calc
      _ ≤ |Real.sin (Real.pi*t/T)| * 1 := mul_le_mul_of_nonneg_left
        (Real.abs_cos_le_one _) (abs_nonneg _)
      _ ≤ physicalWeightDenom δ T t := by simpa only [mul_one] using hsin
  have hratio : 0 < Real.pi/T := div_pos Real.pi_pos hT
  have he : |physicalWeightDerivative qb δ T t| =
      qb*(Real.pi/T)*|Real.sin (Real.pi*t/T)*Real.cos (Real.pi*t/T)|/physicalWeightDenom δ T t^3 := by
    simp only [physicalWeightDerivative,abs_div,abs_neg,abs_mul,abs_pow,
      abs_of_pos hqb,abs_of_pos hratio,abs_of_pos hD]
    ring
  rw [he]
  calc
    _ ≤ qb*(Real.pi/T)*physicalWeightDenom δ T t/physicalWeightDenom δ T t^3 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc (mul_pos hqb hratio).le)
        (pow_pos hD 3).le
    _ = (Real.pi/(qb*T))*physicalWeight qb δ T t^2 := by
      dsimp only [physicalWeight]
      field_simp

def physicalTimeWeight (qb δ T : ℝ) (hqb : Real.sqrt (1+δ^2) ≤ qb) (hδ : 0 < δ) : TimeWeight where
  q := physicalWeight qb δ T
  max := qb/δ
  lower t := by
    have hd : 0 < Real.sqrt (1+δ^2) := Real.sqrt_pos.mpr (by positivity)
    have hb := (physicalWeight_bounds qb δ T t (hd.le.trans hqb) hδ).1
    exact ((le_div_iff₀ hd).mpr (by simpa only [one_mul] using hqb)).trans hb
  upper t := (physicalWeight_bounds qb δ T t ((Real.sqrt_nonneg _).trans hqb) hδ).2

def physicalTimeWeightRegularity (g : TimeGrid) (qb δ β : ℝ)
    (hqb : Real.sqrt (1+δ^2) ≤ qb) (hδ : 0 < δ) (hβ : 0 < β)
    (hbudget : Real.pi/(qb*g.period) ≤ β) :
    TimeWeightRegularity (physicalTimeWeight qb δ g.period hqb hδ) g β where
  beta_pos := hβ
  derivative := physicalWeightDerivative qb δ g.period
  hasDeriv t _ := (physicalWeight_hasDerivAt qb δ g.period t hδ).hasDerivWithinAt
  derivative_bound t _ := by
    have hq : 0 < qb := (Real.sqrt_pos.mpr (show 0 < 1+δ^2 by positivity)).trans_le hqb
    exact (physicalWeight_derivative_bound qb δ g.period t hq hδ g.period_pos).trans
      (mul_le_mul_of_nonneg_right hbudget (sq_nonneg _))
  endpoint := by
    change physicalWeight qb δ g.period 0 = physicalWeight qb δ g.period g.period
    simpa only [zero_add] using (physicalWeight_periodic qb δ g.period (ne_of_gt g.period_pos) 0).symm

end Carleman.Physical
