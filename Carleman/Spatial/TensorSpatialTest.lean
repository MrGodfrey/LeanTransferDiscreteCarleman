module

public import Carleman.Spatial.WeakDerivative
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Actual compactly supported product tests and their genuine derivative
in the interval coordinate. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SpatialTest
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {S : Set E} {I : Set ℝ}

theorem tensor_tsupport_subset (φ : SpatialTest S) (ψ : SpatialTest I) :
    tsupport (fun p : E × ℝ => φ.value p.1*ψ.value p.2) ⊆ tsupport φ.value ×ˢ tsupport ψ.value := by
  apply closure_minimal ?_ ((isClosed_tsupport φ.value).prod (isClosed_tsupport ψ.value))
  intro p hp
  exact ⟨subset_tsupport _ (fun h => hp (by simp only [h,zero_mul])),
    subset_tsupport _ (fun h => hp (by simp only [h,mul_zero]))⟩

def tensor (φ : SpatialTest S) (ψ : SpatialTest I) : SpatialTest (S ×ˢ I) where
  value p := φ.value p.1*ψ.value p.2
  smooth := (φ.smooth.comp contDiff_fst).mul (ψ.smooth.comp contDiff_snd)
  compact := (φ.compact.prod ψ.compact).of_isClosed_subset (isClosed_tsupport _) (tensor_tsupport_subset φ ψ)
  support := (tensor_tsupport_subset φ ψ).trans (prod_mono φ.support ψ.support)

theorem tensor_interval_derivative (φ : SpatialTest S) (ψ : SpatialTest I) (p : E × ℝ) :
    fderiv ℝ (φ.tensor ψ).value p (0,1)=φ.value p.1*deriv ψ.value p.2 := by
  have hφ := ((φ.smooth.differentiable (by simp)) p.1).hasFDerivAt.comp p hasFDerivAt_fst
  have hψ := ((ψ.smooth.differentiable (by simp)) p.2).hasFDerivAt.comp p hasFDerivAt_snd
  change fderiv ℝ (φ.value ∘ Prod.fst * ψ.value ∘ Prod.snd) p (0,1)= _
  rw [(hφ.mul hψ).fderiv]
  change φ.value p.1*(fderiv ℝ ψ.value p.2) 1+ψ.value p.2*(fderiv ℝ φ.value p.1) 0= _
  rw [map_zero,mul_zero,add_zero]
  rfl

end Carleman.SpatialTest
