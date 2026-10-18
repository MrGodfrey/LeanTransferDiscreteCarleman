module

public import Carleman.Spatial.SimplexReferenceInverse

/-! Uniform coordinate norm comparison for genuine scalar derivatives. -/
@[expose] public noncomputable section
namespace Carleman
variable {d : ℕ}

theorem derivativeOneFiber_injective : Function.Injective (derivativeOneFiber (d := d)) := by
  intro A B h
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.ext
  intro i
  have hh := congrArg (fun v : DerivativeFiber d 1 => v (Sym.oneEquiv i)) h
  change A (EuclideanSpace.basisFun (Fin d) ℝ (Sym.oneEquiv.symm (Sym.oneEquiv i))) =
    B (EuclideanSpace.basisFun (Fin d) ℝ (Sym.oneEquiv.symm (Sym.oneEquiv i))) at hh
  rw [Equiv.symm_apply_apply] at hh
  exact hh

theorem derivativeOneFiber_reverse_bound : ∃ C > (0:ℝ),
    ∀ A : SpatialCoordinates d →L[ℝ] ℝ, ‖A‖ ≤ C*‖derivativeOneFiber A‖ := by
  obtain ⟨C,hC,hanti⟩ := derivativeOneFiber.toLinearMap.injective_iff_antilipschitz.mp
    (derivativeOneFiber_injective (d := d))
  exact ⟨C,hC,fun A => ZeroHomClass.bound_of_antilipschitz derivativeOneFiber hanti A⟩

theorem derivativeOneFiber_comp_bound : ∃ C > (0:ℝ),
    ∀ (A : SpatialCoordinates d →L[ℝ] ℝ) (B : SpatialCoordinates d →L[ℝ] SpatialCoordinates d),
      ‖derivativeOneFiber (A.comp B)‖ ≤ C*‖B‖*‖derivativeOneFiber A‖ := by
  obtain ⟨K,hK,hbound⟩ := derivativeOneFiber_reverse_bound (d := d)
  refine ⟨‖derivativeOneFiber (d := d)‖*K+1,by positivity,?_⟩
  intro A B
  calc
    ‖derivativeOneFiber (A.comp B)‖ ≤ ‖derivativeOneFiber (d := d)‖*‖A.comp B‖ :=
      derivativeOneFiber.le_opNorm _
    _ ≤ ‖derivativeOneFiber (d := d)‖*(‖A‖*‖B‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le A B)
        (norm_nonneg (derivativeOneFiber (d := d)))
    _ ≤ ‖derivativeOneFiber (d := d)‖*((K*‖derivativeOneFiber A‖)*‖B‖) := by
      gcongr
      exact hbound A
    _ ≤ (‖derivativeOneFiber (d := d)‖*K+1)*‖B‖*‖derivativeOneFiber A‖ := by
      nlinarith [norm_nonneg B,norm_nonneg (derivativeOneFiber A)]

end Carleman
