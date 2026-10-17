module

public import Carleman.Continuous.BochnerNorm
public import Carleman.Periodic.L2Algebra

/-! Domination by two genuine L² fields, in continuous and discrete time. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman
variable {X E : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup E]

theorem bochnerL2Norm_coe (f : Lp E 2 μ) : bochnerL2Norm μ f = ‖f‖ := by
  rw [bochnerL2Norm_eq _ (Lp.memLp f),Lp.toLp_coeFn]

theorem lp_norm_le_two {F : Type*} [NormedAddCommGroup F]
    (f : Lp E 2 μ) (a b : Lp F 2 μ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ C*(‖a x‖+‖b x‖)) : ‖f‖ ≤ C*(‖a‖+‖b‖) := by
  let v : Fin 2 → X → F := ![(fun x => a x),(fun x => b x)]
  have hv : ∀ i, MemLp (v i) 2 μ := by intro i; fin_cases i <;> exact Lp.memLp _
  have hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ C*∑ i, ‖v i x‖ := by
    simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,v] using h
  have he := bochnerL2Norm_le_sum (Lp.memLp f) v hv hC hb
  simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,v,bochnerL2Norm_coe] using he

theorem TimeGrid.l2Norm_le_two (g : TimeGrid) [InnerProductSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : g.Sequence E) (a b : g.Sequence F) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ‖f i‖ ≤ C*(‖a i‖+‖b i‖)) : g.l2Norm f ≤ C*(g.l2Norm a+g.l2Norm b) := by
  have he := lp_norm_le_two (Orientation.plus.extensionLp g f)
    (Orientation.plus.extensionLp g a) (Orientation.plus.extensionLp g b) hC ?_
  · simpa only [Orientation.plus.extensionLp_norm] using he
  filter_upwards [Orientation.plus.extensionLp_ae g f,
    Orientation.plus.extensionLp_ae g a,Orientation.plus.extensionLp_ae g b] with t hf ha hb
  rw [hf,ha,hb]
  exact h _
end Carleman
