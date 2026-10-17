module

public import Carleman.Continuous.WeakSolution
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! Actual Bochner L² norms and finite Minkowski estimates. Every comparison
requires MemLp, so totalized extended-real conversion cannot hide infinity. -/
@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Carleman
variable {X E : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup E]

def bochnerL2Norm (μ : Measure X) (f : X → E) : ℝ := (eLpNorm f 2 μ).toReal

theorem bochnerL2Norm_eq (f : X → E) (hf : MemLp f 2 μ) :
    bochnerL2Norm μ f = ‖hf.toLp f‖ := (Lp.norm_toLp f hf).symm

theorem bochnerL2Norm_nonneg (f : X → E) : 0 ≤ bochnerL2Norm μ f := ENNReal.toReal_nonneg

theorem bochnerL2Norm_norm (f : X → E) (hf : MemLp f 2 μ) :
    bochnerL2Norm μ (fun t => ‖f t‖) = bochnerL2Norm μ f := by
  unfold bochnerL2Norm
  rw [eLpNorm_norm _ hf.aestronglyMeasurable]

theorem bochnerL2Norm_add {f g : X → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    bochnerL2Norm μ (fun t => f t + g t) ≤ bochnerL2Norm μ f + bochnerL2Norm μ g := by
  change bochnerL2Norm μ (f+g) ≤ _
  rw [bochnerL2Norm_eq _ (hf.add hg), bochnerL2Norm_eq _ hf, bochnerL2Norm_eq _ hg]
  rw [MemLp.toLp_add]
  exact norm_add_le (hf.toLp f) (hg.toLp g)

theorem bochnerL2Norm_finsetSum {ι : Type*} (s : Finset ι) (f : ι → X → E)
    (hf : ∀ i ∈ s, MemLp (f i) 2 μ) :
    bochnerL2Norm μ (fun t => ∑ i ∈ s, f i t) ≤ ∑ i ∈ s, bochnerL2Norm μ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bochnerL2Norm]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (bochnerL2Norm_add (hf i (Finset.mem_insert_self _ _))
      (memLp_finsetSum _ (fun j hj => hf j (Finset.mem_insert_of_mem hj)))).trans
      (add_le_add le_rfl (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))))

theorem memLp_of_le_sum_norm {ι : Type*} [Fintype ι]
    {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)]
    {f : X → E} (hf : AEStronglyMeasurable f μ) (v : ∀ i, X → F i)
    (hv : ∀ i, MemLp (v i) 2 μ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ t ∂μ, ‖f t‖ ≤ C * ∑ i, ‖v i t‖) : MemLp f 2 μ := by
  have hs : MemLp (fun t => C * ∑ i, ‖v i t‖) 2 μ :=
    (memLp_finsetSum _ (fun i _ => (hv i).norm)).const_mul C
  apply hs.of_le hf
  filter_upwards [hb] with t ht
  simpa only [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg hC (Finset.sum_nonneg fun i _ => norm_nonneg (v i t)))] using ht

/-- A pointwise finite sum of norms controls the sum of genuine Bochner norms
by Minkowski. The scalar sum is never identified with that sum of norms. -/
theorem bochnerL2Norm_le_sum {ι : Type*} [Fintype ι]
    {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)]
    {f : X → E} (hf : MemLp f 2 μ) (v : ∀ i, X → F i)
    (hv : ∀ i, MemLp (v i) 2 μ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ t ∂μ, ‖f t‖ ≤ C * ∑ i, ‖v i t‖) :
    bochnerL2Norm μ f ≤ C * ∑ i, bochnerL2Norm μ (v i) := by
  have hs : MemLp (fun t => ∑ i, ‖v i t‖) 2 μ := memLp_finsetSum _ (fun i _ => (hv i).norm)
  have hle : bochnerL2Norm μ f ≤ C * bochnerL2Norm μ (fun t => ∑ i, ‖v i t‖) := by
    rw [bochnerL2Norm_eq _ hf, bochnerL2Norm_eq _ hs]
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hf.coeFn_toLp, hs.coeFn_toLp, hb] with t h1 h2 ht
    rw [h1, h2, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)]
    exact ht
  have he := bochnerL2Norm_finsetSum Finset.univ (fun i t => ‖v i t‖) (fun i _ => (hv i).norm)
  simp_rw [bochnerL2Norm_norm _ (hv _)] at he
  exact hle.trans (mul_le_mul_of_nonneg_left he hC)
end Carleman
