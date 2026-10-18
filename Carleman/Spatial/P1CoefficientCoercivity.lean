module

public import Carleman.Spatial.UniformNeighborGrading

/-! Sharp finite coefficient algebra for the weighted P1 mass form.
Identification with actual simplex integrals is a separate obligation. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman

def p1MassMargin (d : ℕ) (γ : ℝ) : ℝ := 1-((d+1:ℝ)*(γ-1)^2)/(4*γ)

theorem p1MassMargin_pos {d : ℕ} {γ : ℝ} (hγ : 1 ≤ γ) (hg : γ < p1GradingLimit d) :
    0 < p1MassMargin d γ := by
  have hγ0 : 0 < γ := zero_lt_one.trans_le hγ
  have hs : 1 < Real.sqrt (d+2) := (Real.lt_sqrt (by norm_num)).mpr
    (by nlinarith [show (0:ℝ) ≤ (d:ℝ) from Nat.cast_nonneg d])
  have hg' : γ*(Real.sqrt (d+2)-1) < Real.sqrt (d+2)+1 :=
    (lt_div_iff₀ (sub_pos.mpr hs)).mp hg
  have hl : (γ-1)*Real.sqrt (d+2) < γ+1 := by nlinarith
  have hsq := (sq_lt_sq₀ (mul_nonneg (sub_nonneg.mpr hγ) (Real.sqrt_nonneg _))
    (by positivity : 0 ≤ γ+1)).mpr hl
  rw [mul_pow,Real.sq_sqrt (by positivity)] at hsq
  have hm : (d+1:ℝ)*(γ-1)^2 < 4*γ := by nlinarith
  unfold p1MassMargin
  have hd : ((d+1:ℝ)*(γ-1)^2)/(4*γ) < 1 :=
    (div_lt_iff₀ (by positivity : 0 < 4*γ)).mpr (by simpa only [one_mul] using hm)
  linarith

theorem weight_deviation_bound {a γ : ℝ} (ha : 1 ≤ a) (hag : a ≤ γ) :
    |a-γ/a| ≤ γ-1 := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hg0 : 0 < γ := ha0.trans_le hag
  have he : a*(a-γ/a)=a^2-γ := by field_simp
  have hleft := mul_nonneg (sub_nonneg.mpr ha) (by positivity : 0 ≤ a+γ)
  have hright := mul_nonneg (sub_nonneg.mpr hag) (by positivity : 0 ≤ a+1)
  apply abs_le.mpr
  constructor <;> nlinarith

variable {ι : Type*} [Fintype ι]

def p1CoefficientForm (c e : ι → ℝ) : ℝ :=
  (∑ i, c i*e i)+(∑ i, c i)*(∑ i, e i)

theorem p1CoefficientForm_smul_right (c e : ι → ℝ) (a : ℝ) :
    p1CoefficientForm c (fun i => a*e i) = a*p1CoefficientForm c e := by
  unfold p1CoefficientForm
  simp only [mul_add,Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

theorem weighted_coefficient_deviation (c ω : ι → ℝ) {γ : ℝ}
    (hω : ∀ i, 1 ≤ ω i) (hωγ : ∀ i, ω i ≤ γ) :
    (∑ i, ((ω i)^2-γ)*c i)^2 ≤
      (Fintype.card ι:ℝ)*(γ-1)^2*(∑ i, (ω i*c i)^2) := by
  have hid : (∑ i, ((ω i)^2-γ)*c i) =
      ∑ i, (ω i-γ/ω i)*(ω i*c i) := by
    apply Finset.sum_congr rfl
    intro i _
    have hi : ω i ≠ 0 := ne_of_gt (zero_lt_one.trans_le (hω i))
    field_simp
  rw [hid]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => ω i-γ/ω i) (fun i => ω i*c i)
  apply hcs.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  calc
    _ ≤ ∑ _i : ι, (γ-1)^2 := by
      apply Finset.sum_le_sum
      intro i _
      have hi := weight_deviation_bound (hω i) (hωγ i)
      nlinarith [sq_abs (ω i-γ/ω i),abs_nonneg (ω i-γ/ω i)]
    _ = _ := by simp

theorem weighted_p1_coefficient_coercive (d : ℕ) (c ω : Fin (d+1) → ℝ) {γ : ℝ}
    (hγ : 1 ≤ γ) (hω : ∀ i, 1 ≤ ω i) (hωγ : ∀ i, ω i ≤ γ) :
    p1MassMargin d γ*(∑ i, (ω i*c i)^2) ≤
      p1CoefficientForm c (fun i => (ω i)^2*c i) := by
  have hγ0 : 0 < γ := zero_lt_one.trans_le hγ
  have hd := weighted_coefficient_deviation c ω hω hωγ
  have hid : (∑ i, ((ω i)^2-γ)*c i) =
      (∑ i, (ω i)^2*c i)-γ*(∑ i, c i) := by
    simp only [sub_mul,Finset.sum_sub_distrib,← Finset.mul_sum]
  have hs : (∑ i, c i*((ω i)^2*c i)) = ∑ i, (ω i*c i)^2 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hid] at hd
  simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] at hd
  have hp := sq_nonneg ((∑ i, (ω i)^2*c i)+γ*(∑ i, c i))
  unfold p1CoefficientForm
  rw [hs]
  unfold p1MassMargin
  apply (le_of_mul_le_mul_left ?_ (by positivity : 0 < 4*γ))
  field_simp
  simp only [mul_pow] at hd
  nlinarith

theorem weighted_p1_coefficient_coercive_scaled (d : ℕ) (c ω : Fin (d+1) → ℝ)
    {γ a : ℝ} (hγ : 1 ≤ γ) (ha : 0 < a)
    (hω : ∀ i, a ≤ ω i) (hωγ : ∀ i, ω i ≤ γ*a) :
    p1MassMargin d γ*(∑ i, (ω i*c i)^2) ≤
      p1CoefficientForm c (fun i => (ω i)^2*c i) := by
  have hl := weighted_p1_coefficient_coercive d c (fun i => ω i/a) hγ
    (fun i => (le_div_iff₀ ha).mpr (by simpa only [one_mul] using hω i))
    (fun i => (div_le_iff₀ ha).mpr (hωγ i))
  have hs : (∑ i, (ω i*c i)^2) = a^2*(∑ i, ((ω i/a)*c i)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  have hf : p1CoefficientForm c (fun i => (ω i)^2*c i) =
      a^2*p1CoefficientForm c (fun i => (ω i/a)^2*c i) := by
    rw [← p1CoefficientForm_smul_right]
    congr 1
    funext i
    field_simp
  rw [hs,hf]
  simpa only [mul_assoc,mul_left_comm (p1MassMargin d γ) (a^2)] using
    mul_le_mul_of_nonneg_left hl (sq_nonneg a)

theorem weighted_p1_coefficient_form_pos (d : ℕ) (c ω : Fin (d+1) → ℝ)
    {γ a : ℝ} (hγ : 1 ≤ γ) (hg : γ < p1GradingLimit d) (ha : 0 < a)
    (hω : ∀ i, a ≤ ω i) (hωγ : ∀ i, ω i ≤ γ*a) (hc : c ≠ 0) :
    0 < p1CoefficientForm c (fun i => (ω i)^2*c i) := by
  have hn : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (funext h)
  obtain ⟨i,hi⟩ := hn
  have hs : 0 < ∑ j, (ω j*c j)^2 := by
    apply lt_of_lt_of_le (sq_pos_of_ne_zero (mul_ne_zero (ne_of_gt (ha.trans_le (hω i))) hi))
    exact Finset.single_le_sum (fun j _ => sq_nonneg (ω j*c j)) (Finset.mem_univ i)
  exact (mul_pos (p1MassMargin_pos hγ hg) hs).trans_le
    (weighted_p1_coefficient_coercive_scaled d c ω hγ ha hω hωγ)

end Carleman
