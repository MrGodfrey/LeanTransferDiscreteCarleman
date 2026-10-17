module

public import Carleman.Continuous.BochnerNorm

/-! Representative invariance and elementary algebra for actual Bochner norms. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman
variable {X E : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup E]

theorem bochnerL2Norm_congr_ae {f g : X → E} (h : f =ᵐ[μ] g) :
    bochnerL2Norm μ f = bochnerL2Norm μ g :=
  congrArg ENNReal.toReal (eLpNorm_congr_ae h)

theorem bochnerL2Norm_neg (f : X → E) :
    bochnerL2Norm μ (-f) = bochnerL2Norm μ f := by
  exact congrArg ENNReal.toReal (eLpNorm_neg f 2 μ)

theorem bochnerL2Norm_sub {f g : X → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    bochnerL2Norm μ (fun x => f x - g x) ≤ bochnerL2Norm μ f + bochnerL2Norm μ g := by
  simpa only [sub_eq_add_neg, Pi.neg_apply, bochnerL2Norm_neg] using bochnerL2Norm_add hf hg.neg

theorem bochnerL2Norm_const_smul [NormedSpace ℝ E] (c : ℝ) (f : X → E) :
    bochnerL2Norm μ (c • f) = |c| *bochnerL2Norm μ f := by
  simp only [bochnerL2Norm, eLpNorm_const_smul, ENNReal.toReal_mul,
    toReal_enorm, Real.norm_eq_abs]

end Carleman
