module

public import Carleman.Continuous.TimeInterval
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Vector-valued L² testing uses actual scalar test functions. It is a
continuous Hilbert pairing, so weak derivative identities pass to limits. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman
variable {α H : Type*} [MeasurableSpace α] (μ : Measure α)
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def scalarTensor (φ : Lp ℝ 2 μ) : H →L[ℝ] Lp H 2 μ :=
  ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] H →L[ℝ] H).flip.compLpL₂ 2 μ).flip φ

theorem scalarTensor_ae (φ : Lp ℝ 2 μ) (h : H) :
    scalarTensor μ φ h =ᵐ[μ] (fun t => φ t • h) :=
  ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] H →L[ℝ] H).flip h).coeFn_compLp φ

theorem inner_scalarTensor (f : Lp H 2 μ) (φ : Lp ℝ 2 μ) (h : H) :
    inner ℝ f (scalarTensor μ φ h) = ∫ t, φ t * inner ℝ (f t) h ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [scalarTensor_ae μ φ h] with t ht
  rw [ht, real_inner_smul_right]

theorem integrable_scalar_smul (f : Lp H 2 μ) (φ : Lp ℝ 2 μ) :
    Integrable (fun t => φ t • f t) μ :=
  memLp_one_iff_integrable.mp ((Lp.memLp φ).smul (Lp.memLp f))

variable [CompleteSpace H]

/-- The closed Hilbert pairing is exactly a test of the H-valued Bochner integral. -/
theorem inner_scalarTensor_integral (f : Lp H 2 μ) (φ : Lp ℝ 2 μ) (h : H) :
    inner ℝ f (scalarTensor μ φ h) = inner ℝ (∫ t, φ t • f t ∂μ) h := by
  rw [inner_scalarTensor]
  have he := (innerSL ℝ h).integral_comp_comm (integrable_scalar_smul μ f φ)
  simp only [innerSL_apply_apply, real_inner_smul_right] at he
  calc
    _ = ∫ t, φ t * inner ℝ h (f t) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        dsimp only
        rw [real_inner_comm h (f t)]
    _ = inner ℝ h (∫ t, φ t • f t ∂μ) := he
    _ = _ := real_inner_comm _ _

end Carleman
