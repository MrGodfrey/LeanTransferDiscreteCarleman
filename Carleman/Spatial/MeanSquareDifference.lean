module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod

/-! Exact mean-square and pairwise-difference identities on a finite
measure space, for actual L² functions. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]

theorem integral_sq_sub_const {f : Ω → ℝ} (hf : MemLp f 2 ν) (a : ℝ) :
    (∫ x, (f x-a)^2 ∂ν)=(∫ x, (f x)^2 ∂ν)-2*a*(∫ x, f x ∂ν)+ν.real univ*a^2 := by
  have hi : Integrable f ν := hf.integrable (by norm_num)
  have he : (fun x => (f x-a)^2)=(fun x => ((f x)^2-2*a*f x)+a^2) := by
    funext x
    ring
  have hs : Integrable (fun x => (f x)^2-2*a*f x) ν :=
    hf.integrable_sq.sub (hi.const_mul (2*a))
  rw [he,integral_add hs (integrable_const _),
    integral_sub hf.integrable_sq (hi.const_mul (2*a)),integral_const_mul,integral_const,smul_eq_mul]

theorem integral_pairwise_sq {f : Ω → ℝ} (hf : MemLp f 2 ν) :
    (∫ x, ∫ y, (f x-f y)^2 ∂ν ∂ν)=
      2*ν.real univ*(∫ x, (f x)^2 ∂ν)-2*(∫ x, f x ∂ν)^2 := by
  have hi : Integrable f ν := hf.integrable (by norm_num)
  have hinner (x : Ω) : (∫ y, (f x-f y)^2 ∂ν)=
      (∫ y, (f y)^2 ∂ν)-2*f x*(∫ y, f y ∂ν)+ν.real univ*(f x)^2 := by
    convert integral_sq_sub_const hf (f x) using 1
    congr 1
    funext y
    ring
  simp_rw [hinner]
  have hm : Integrable (fun x => 2*f x*(∫ y, f y ∂ν)) ν := (hi.const_mul 2).mul_const _
  have hs : Integrable (fun x => (∫ y, (f y)^2 ∂ν)-2*f x*(∫ y, f y ∂ν)) ν :=
    (integrable_const _).sub hm
  rw [integral_add hs (hf.integrable_sq.const_mul _),
    integral_sub (integrable_const _) hm,integral_const,integral_const_mul,
    integral_mul_const,integral_const_mul,smul_eq_mul]
  ring

theorem mean_square_pairwise_identity {f : Ω → ℝ} (hf : MemLp f 2 ν)
    (hν : 0 < ν.real univ) :
    2*ν.real univ*(∫ x, (f x-(∫ y, f y ∂ν)/ν.real univ)^2 ∂ν)=
      ∫ x, ∫ y, (f x-f y)^2 ∂ν ∂ν := by
  rw [integral_sq_sub_const hf,integral_pairwise_sq hf]
  field_simp
  ring

end Carleman
