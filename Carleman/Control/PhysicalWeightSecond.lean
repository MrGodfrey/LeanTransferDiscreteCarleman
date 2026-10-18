module

public import Carleman.Control.PhysicalWeight

/-! The original weight's second derivative with a T-uniform ratio bound. -/
@[expose] public noncomputable section
namespace Carleman.Physical

def physicalWeightSecondDerivative (qb δ T t : ℝ) : ℝ :=
  qb*(Real.pi/T)^2*(3*(Real.sin (Real.pi*t/T)*Real.cos (Real.pi*t/T))^2-
    (Real.cos (Real.pi*t/T)^2-Real.sin (Real.pi*t/T)^2)*physicalWeightDenom δ T t^2)/
    physicalWeightDenom δ T t^5

theorem physicalWeightDerivative_hasDerivAt (qb δ T t : ℝ) (hδ : 0 < δ) :
    HasDerivAt (physicalWeightDerivative qb δ T) (physicalWeightSecondDerivative qb δ T t) t := by
  have ha : HasDerivAt (fun s : ℝ => Real.pi*s/T) (Real.pi/T) t := by
    simpa only [id_eq,mul_one] using ((hasDerivAt_id t).const_mul Real.pi).div_const T
  have hb := ha.sin.mul ha.cos
  have hn := ((hb.mul_const (Real.pi/T)).const_mul qb).neg
  have hd := (physicalWeightDenom_hasDerivAt δ T t hδ).pow 3
  have he := hn.div hd (pow_ne_zero 3 (ne_of_gt (physicalWeightDenom_pos δ T t hδ)))
  have hDne := ne_of_gt (physicalWeightDenom_pos δ T t hδ)
  convert he using 1
  · rfl
  · dsimp only [physicalWeightSecondDerivative,Pi.pow_apply,Pi.neg_apply,Pi.mul_apply]
    field_simp [hDne]
    ring

theorem physicalWeight_second_derivative_bound (qb δ T t : ℝ)
    (hqb : 0 < qb) (hδ : 0 < δ) (hT : 0 < T) :
    |physicalWeightSecondDerivative qb δ T t| ≤
      (4*Real.pi^2/(qb^2*T^2))*physicalWeight qb δ T t^3 := by
  let s := Real.sin (Real.pi*t/T)
  let c := Real.cos (Real.pi*t/T)
  let D := physicalWeightDenom δ T t
  have hD : 0 < D := physicalWeightDenom_pos δ T t hδ
  have hs : s^2 ≤ D^2 := by
    dsimp only [D,s]
    rw [physicalWeightDenom_sq]
    linarith [sq_nonneg δ]
  have hc : c^2 ≤ 1 := Real.cos_sq_le_one _
  have hsc : (s*c)^2 ≤ D^2 := by
    rw [mul_pow]
    exact (mul_le_mul_of_nonneg_left hc (sq_nonneg s)).trans (by simpa only [mul_one] using hs)
  have hdiff : |c^2-s^2| ≤ 1 := by
    apply abs_le.mpr
    have he : s^2+c^2 = 1 := Real.sin_sq_add_cos_sq _
    constructor <;> nlinarith [sq_nonneg s,sq_nonneg c]
  have hn : |3*(s*c)^2-(c^2-s^2)*D^2| ≤ 4*D^2 := by
    calc
      _ ≤ |3*(s*c)^2| + |(c^2-s^2)*D^2| := abs_sub _ _
      _ = 3*(s*c)^2+|c^2-s^2| * D^2 := by
        rw [abs_mul,abs_of_nonneg (show (0:ℝ) ≤ 3 by norm_num),abs_of_nonneg (sq_nonneg (s*c)),
          abs_mul,abs_of_nonneg (sq_nonneg D)]
      _ ≤ 4*D^2 := by
        have hh := mul_le_mul_of_nonneg_right hdiff (sq_nonneg D)
        nlinarith only [hh,hsc]
  have ha : 0 < Real.pi/T := div_pos Real.pi_pos hT
  have habs : |physicalWeightSecondDerivative qb δ T t| =
      qb*(Real.pi/T)^2*|3*(s*c)^2-(c^2-s^2)*D^2| / D^5 := by
    change |qb*(Real.pi/T)^2*(3*(s*c)^2-(c^2-s^2)*D^2)/D^5| = _
    rw [abs_div,abs_mul,abs_mul,abs_of_pos hqb,abs_of_nonneg (sq_nonneg _),
      abs_of_pos (pow_pos hD 5)]
  rw [habs]
  calc
    _ ≤ qb*(Real.pi/T)^2*(4*D^2)/D^5 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn (mul_pos hqb (sq_pos_of_pos ha)).le)
        (pow_pos hD 5).le
    _ = (4*Real.pi^2/(qb^2*T^2))*physicalWeight qb δ T t^3 := by
      change qb*(Real.pi/T)^2*(4*D^2)/D^5 = (4*Real.pi^2/(qb^2*T^2))*(qb/D)^3
      field_simp

theorem physicalWeight_deriv (qb δ T : ℝ) (hδ : 0 < δ) :
    deriv (physicalWeight qb δ T) = physicalWeightDerivative qb δ T :=
  funext fun t => (physicalWeight_hasDerivAt qb δ T t hδ).deriv

theorem physicalWeight_second_deriv (qb δ T : ℝ) (hδ : 0 < δ) :
    deriv (deriv (physicalWeight qb δ T)) = physicalWeightSecondDerivative qb δ T := by
  rw [physicalWeight_deriv qb δ T hδ]
  exact funext fun t => (physicalWeightDerivative_hasDerivAt qb δ T t hδ).deriv

theorem physicalWeightDerivative_zero (qb δ T : ℝ) : physicalWeightDerivative qb δ T 0 = 0 := by
  simp [physicalWeightDerivative]

theorem physicalWeightDerivative_periodic (qb δ T : ℝ) (hT : T ≠ 0) :
    Function.Periodic (physicalWeightDerivative qb δ T) T := by
  intro t
  have he : Real.pi*(t+T)/T = Real.pi*t/T+Real.pi := by field_simp
  simp [physicalWeightDerivative,physicalWeightDenom,he,Real.sin_add_pi,Real.cos_add_pi]

end Carleman.Physical
