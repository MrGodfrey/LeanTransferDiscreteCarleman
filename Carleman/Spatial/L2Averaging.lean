module

public import Carleman.Spatial.RealL2Integral
public import Mathlib.MeasureTheory.Integral.Prod

/-! L² averaging inequalities on genuine product measures. All integrability
needed for the Bochner norms and Fubini exchanges is established explicitly. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman

theorem bochnerL2Norm_restrict_le {Z E : Type*} [MeasurableSpace Z] [NormedAddCommGroup E]
    {ζ : Measure Z} {f : Z → E} (hf : MemLp f 2 ζ) (A : Set Z) :
    bochnerL2Norm (ζ.restrict A) f ≤ bochnerL2Norm ζ f :=
  ENNReal.toReal_mono hf.eLpNorm_lt_top.ne (eLpNorm_restrict_le f 2 ζ A)

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [IsFiniteMeasure ν]

theorem l2_average_square_le {f : X × Y → ℝ}
    (hf : AEStronglyMeasurable f (μ.prod ν))
    (h2 : Integrable (fun p => f p^2) (μ.prod ν)) :
    MemLp (fun x => ∫ y, f (x,y) ∂ν) 2 μ ∧
      (bochnerL2Norm μ (fun x => ∫ y, f (x,y) ∂ν))^2 ≤
        ν.real univ*(∫ p, f p^2 ∂μ.prod ν) := by
  have hmeas := hf.integral_prod_right'
  have hpoint : ∀ᵐ x ∂μ, (∫ y, f (x,y) ∂ν)^2 ≤ ν.real univ*(∫ y, f (x,y)^2 ∂ν) := by
    filter_upwards [hf.prodMk_left,h2.prod_right_ae] with x hx hx2
    have hs := (memLp_two_iff_integrable_sq hx).mpr hx2
    have he := integral_mul_sq_le (memLp_const (1 : ℝ)) hs
    simpa only [one_mul,one_pow,integral_const,smul_eq_mul,mul_one] using he
  have hmajor : Integrable (fun x => ν.real univ*(∫ y, f (x,y)^2 ∂ν)) μ :=
    h2.integral_prod_left.const_mul _
  have hsq : Integrable (fun x => (∫ y, f (x,y) ∂ν)^2) μ := by
    apply hmajor.mono' (hmeas.pow 2)
    filter_upwards [hpoint] with x hx
    simpa only [Pi.pow_apply,Real.norm_eq_abs,abs_pow,sq_abs] using hx
  have hm := (memLp_two_iff_integrable_sq hmeas).mpr hsq
  refine ⟨hm,?_⟩
  rw [← integral_sq_eq_bochnerL2Norm_sq hm]
  have he := integral_mono_ae hsq hmajor hpoint
  rw [integral_const_mul,← integral_prod _ h2] at he
  exact he

/-- A uniform bound on the actual L² slices proves the product-square
integrability required above; the scalar C is merely this proved norm bound. -/
theorem integrable_square_of_slice_bound {f : X × Y → ℝ}
    (hf : AEStronglyMeasurable f (μ.prod ν))
    (hs : ∀ y, MemLp (fun x => f (x,y)) 2 μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ y, bochnerL2Norm μ (fun x => f (x,y)) ≤ C) :
    Integrable (fun p => f p^2) (μ.prod ν) := by
  apply (integrable_prod_iff' (hf.pow 2)).mpr
  refine ⟨Filter.Eventually.of_forall fun y => (hs y).integrable_sq,?_⟩
  apply (integrable_const (C^2)).mono' ((hf.pow 2).norm.prod_swap.integral_prod_right')
  apply Filter.Eventually.of_forall
  intro y
  have he : (∫ x, ‖f (x,y)^2‖ ∂μ) = (bochnerL2Norm μ (fun x => f (x,y)))^2 := by
    simp only [Real.norm_eq_abs,abs_pow,sq_abs]
    exact integral_sq_eq_bochnerL2Norm_sq (hs y)
  change ‖∫ x, ‖f (x,y)^2‖ ∂μ‖ ≤ C^2
  rw [he,Real.norm_eq_abs,abs_pow,sq_abs]
  exact (sq_le_sq₀ (bochnerL2Norm_nonneg _) hC).mpr (hb y)

theorem l2_average_le_of_slice_bound {f : X × Y → ℝ}
    (hf : AEStronglyMeasurable f (μ.prod ν))
    (hs : ∀ y, MemLp (fun x => f (x,y)) 2 μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ y, bochnerL2Norm μ (fun x => f (x,y)) ≤ C) :
    MemLp (fun x => ∫ y, f (x,y) ∂ν) 2 μ ∧
      bochnerL2Norm μ (fun x => ∫ y, f (x,y) ∂ν) ≤ ν.real univ*C := by
  have h2 := integrable_square_of_slice_bound hf hs hC hb
  obtain ⟨hm,he⟩ := l2_average_square_le hf h2
  refine ⟨hm,?_⟩
  have hprod : (∫ p, f p^2 ∂μ.prod ν) ≤ ν.real univ*C^2 := by
    rw [integral_prod_symm _ h2]
    have hb' : ∀ᵐ y ∂ν, (∫ x, f (x,y)^2 ∂μ) ≤ C^2 := Filter.Eventually.of_forall fun y => by
      rw [integral_sq_eq_bochnerL2Norm_sq (hs y)]
      exact (sq_le_sq₀ (bochnerL2Norm_nonneg _) hC).mpr (hb y)
    simpa only [integral_const,smul_eq_mul] using
      integral_mono_ae h2.integral_prod_right (integrable_const (C^2)) hb'
  apply (sq_le_sq₀ (bochnerL2Norm_nonneg _) (mul_nonneg (measureReal_nonneg) hC)).mp
  calc
    _ ≤ _ := he
    _ ≤ ν.real univ*(ν.real univ*C^2) := mul_le_mul_of_nonneg_left hprod (measureReal_nonneg)
    _ = (ν.real univ*C)^2 := by ring
end Carleman
