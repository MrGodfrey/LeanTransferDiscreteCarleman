module

public import Carleman.Continuous.BochnerNormAlgebra
public import Carleman.Continuous.NormDomination
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! Finite measurable covers control the actual restricted L² norm. No
partition of unity, boundary regularity, or overlap bound is assumed. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {X E ι : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [Fintype ι]
  {μ : Measure X}

theorem bochnerL2Norm_finite_cover {f : X → E} (hf : MemLp f 2 μ)
    (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hcover : ∀ᵐ x ∂μ, ∃ i, x ∈ A i) :
    bochnerL2Norm μ f ≤ ∑ i, bochnerL2Norm (μ.restrict (A i)) f := by
  classical
  have hmem (i : ι) : MemLp ((A i).indicator f) 2 μ := hf.indicator (hA i).nullMeasurableSet
  have hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ 1*∑ i, ‖(A i).indicator f x‖ := by
    filter_upwards [hcover] with x hx
    obtain ⟨i,hi⟩ := hx
    rw [one_mul]
    calc
      _ = ‖(A i).indicator f x‖ := by rw [indicator_of_mem hi]
      _ ≤ _ := Finset.single_le_sum (fun j _ => norm_nonneg ((A j).indicator f x)) (Finset.mem_univ i)
  have he := bochnerL2Norm_le_sum hf (fun i => (A i).indicator f) hmem zero_le_one hb
  simpa only [one_mul,bochnerL2Norm,eLpNorm_indicator_eq_eLpNorm_restrict (hA _).nullMeasurableSet] using he
end Carleman
