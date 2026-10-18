module

public import Carleman.Spatial.SimplexPermutationIntegral
public import Carleman.Spatial.P1CoefficientCoercivity

/-! The exact consistent P1 mass integral on every genuine simplex. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} (T : Affine.Simplex ℝ (SpatialCoordinates d) d)

theorem integral_simplexBarycentric_mul_offdiag (i j : Fin (d+1)) (hij : i ≠ j) :
    (∫ x in simplicialCell T.points, simplexBarycentric T i x * simplexBarycentric T j x) =
      volume.real (simplicialCell T.points)/((d+1:ℝ)*(d+2)) := by
  let I (k : Fin (d+1)) := ∫ x in simplicialCell T.points,
    simplexBarycentric T i x * simplexBarycentric T k x
  have hsym (k : Fin (d+1)) (hk : k ≠ i) : I k = I j := by
    have h := integral_simplexBarycentric_mul_permutation T (Equiv.swap j k) i j
    simpa only [Equiv.swap_apply_of_ne_of_ne hij hk.symm,Equiv.swap_apply_left] using h
  have hs : ∑ k, I k = volume.real (simplicialCell T.points)/(d+1:ℝ) := by
    rw [← integral_finsetSum]
    · simp only [← Finset.mul_sum,simplexBarycentric_sum,mul_one,integral_simplexBarycentric]
    · intro k _
      exact ((simplexBarycentric T i).continuous_of_finiteDimensional.mul
        (simplexBarycentric T k).continuous_of_finiteDimensional).continuousOn.integrableOn_compact
          (simplicialCell_compact _)
  have hd : (0:ℝ) < d := by
    cases d with
    | zero => exact (hij (Fin.ext (by omega))).elim
    | succ n => exact_mod_cast Nat.succ_pos n
  have he (k : Fin (d+1)) : I k = I j + if k=i then I i-I j else 0 := by
    by_cases hk : k=i
    · subst k
      simp
    · rw [ite_eq_right hk,add_zero,hsym k hk]
  have hs' : ∑ k, I k = (d:ℝ)*I j+I i := by
    calc
      ∑ k, I k = ∑ k, (I j + if k=i then I i-I j else 0) :=
        Finset.sum_congr rfl (fun k _ => he k)
      _ = (d:ℝ)*I j+I i := by
        simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
          nsmul_eq_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
        push_cast
        ring
  have hii : I i = 2*volume.real (simplicialCell T.points)/((d+1:ℝ)*(d+2)) := by
    simpa only [I,← sq] using integral_simplexBarycentric_sq T i
  rw [hs',hii] at hs
  change I j = _
  have hd1 : (d:ℝ)+1 ≠ 0 := by positivity
  have hd2 : (d:ℝ)+2 ≠ 0 := by positivity
  field_simp at hs ⊢
  nlinarith

theorem integral_simplexBarycentric_mul (i j : Fin (d+1)) :
    (∫ x in simplicialCell T.points, simplexBarycentric T i x * simplexBarycentric T j x) =
      (1+(if i=j then 1 else 0))*volume.real (simplicialCell T.points)/((d+1:ℝ)*(d+2)) := by
  by_cases h : i=j
  · subst j
    convert integral_simplexBarycentric_sq T i using 1 <;> norm_num [← sq]
  · simpa only [ite_eq_right h,add_zero,one_mul] using integral_simplexBarycentric_mul_offdiag T i j h


omit T in
theorem p1CoefficientForm_sum (c e : Fin (d+1) → ℝ) :
    (∑ i, ∑ j, c i*e j*(1+(if i=j then 1 else 0))) = p1CoefficientForm c e := by
  simp only [mul_add,mul_one,mul_ite,mul_zero,Finset.sum_add_distrib,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true,← Finset.mul_sum,← Finset.sum_mul,
    p1CoefficientForm]
  ring

theorem integral_simplexNodalInterpolant_mul (c e : Fin (d+1) → ℝ) :
    (∫ x in simplicialCell T.points, simplexNodalInterpolant T c x * simplexNodalInterpolant T e x) =
      volume.real (simplicialCell T.points)/((d+1:ℝ)*(d+2)) * p1CoefficientForm c e := by
  have hm (i j : Fin (d+1)) : Integrable
      (fun x => (c i*e j)*(simplexBarycentric T i x*simplexBarycentric T j x))
      (volume.restrict (simplicialCell T.points)) :=
    (continuous_const.mul ((simplexBarycentric T i).continuous_of_finiteDimensional.mul
      (simplexBarycentric T j).continuous_of_finiteDimensional)).continuousOn.integrableOn_compact
        (simplicialCell_compact _)
  have he : (fun x => simplexNodalInterpolant T c x*simplexNodalInterpolant T e x) =
      (fun x => ∑ i, ∑ j, (c i*e j)*(simplexBarycentric T i x*simplexBarycentric T j x)) := by
    funext x
    simp only [simplexNodalInterpolant_apply]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hm i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hm _ j),integral_const_mul,
    integral_simplexBarycentric_mul]
  rw [← p1CoefficientForm_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring


theorem simplex_mass_factor_pos :
    0 < volume.real (simplicialCell T.points)/((d+1:ℝ)*(d+2)) := by
  have hv : 0 < volume.real (simplicialCell T.points) :=
    ENNReal.toReal_pos (Measure.measure_pos_of_nonempty_interior volume
      (simplicialCell_interior_nonempty T)).ne' (simplicialCell_compact _).measure_ne_top
  exact div_pos hv (by positivity)

theorem integral_simplexNodalInterpolant_sq_bounds (c : Fin (d+1) → ℝ) :
    volume.real (simplicialCell T.points)/((d+1:ℝ)*(d+2))*(∑ i, (c i)^2) ≤
        (∫ x in simplicialCell T.points, (simplexNodalInterpolant T c x)^2) ∧
    (∫ x in simplicialCell T.points, (simplexNodalInterpolant T c x)^2) ≤
      volume.real (simplicialCell T.points)/((d+1:ℝ)*(d+2))*(d+2)*(∑ i, (c i)^2) := by
  have he : (∫ x in simplicialCell T.points, (simplexNodalInterpolant T c x)^2) =
      volume.real (simplicialCell T.points)/((d+1:ℝ)*(d+2))*
        ((∑ i, (c i)^2)+(∑ i, c i)^2) := by
    simpa only [p1CoefficientForm,← sq] using integral_simplexNodalInterpolant_mul T c c
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin (d+1) => (1:ℝ)) c
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,Nat.cast_add,Nat.cast_one] at hc
  rw [he]
  have hv := (simplex_mass_factor_pos T).le
  constructor
  · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _)) hv
  · have hh : (∑ i, (c i)^2)+(∑ i, c i)^2 ≤ (d+2:ℝ)*(∑ i, (c i)^2) := by
      nlinarith
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh hv

theorem weighted_simplex_mass_coercive (c ω : Fin (d+1) → ℝ)
    {γ a : ℝ} (hγ : 1 ≤ γ) (ha : 0 < a)
    (hω : ∀ i, a ≤ ω i) (hωγ : ∀ i, ω i ≤ γ*a) :
    volume.real (simplicialCell T.points)/((d+1:ℝ)*(d+2))*
      p1MassMargin d γ*(∑ i, (ω i*c i)^2) ≤
    ∫ x in simplicialCell T.points, simplexNodalInterpolant T c x *
      simplexNodalInterpolant T (fun i => (ω i)^2*c i) x := by
  rw [integral_simplexNodalInterpolant_mul]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (weighted_p1_coefficient_coercive_scaled d c ω hγ ha hω hωγ) (simplex_mass_factor_pos T).le

theorem weighted_simplex_mass_pos (c ω : Fin (d+1) → ℝ)
    {γ a : ℝ} (hγ : 1 ≤ γ) (hg : γ < p1GradingLimit d) (ha : 0 < a)
    (hω : ∀ i, a ≤ ω i) (hωγ : ∀ i, ω i ≤ γ*a) (hc : c ≠ 0) :
    0 < ∫ x in simplicialCell T.points, simplexNodalInterpolant T c x *
      simplexNodalInterpolant T (fun i => (ω i)^2*c i) x := by
  rw [integral_simplexNodalInterpolant_mul]
  exact mul_pos (simplex_mass_factor_pos T)
    (weighted_p1_coefficient_form_pos d c ω hγ hg ha hω hωγ hc)

end Carleman
