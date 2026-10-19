module

public import Carleman.Spatial.SmoothH2NodalGradient
public import Carleman.Spatial.SimplexH2ValueLimit

/-! Convergence of actual node values determines the true affine nodal
derivative. Full first-order Euclidean fiber norms retain every coordinate. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Carleman
variable {d : ℕ}

theorem simplexNodal_affineDerivative_eq (T : Affine.Simplex ℝ (SpatialCoordinates d) d)
    (c : Fin (d+1) → ℝ) :
    affineScalarDerivative (simplexNodalInterpolant T c)=simplexNodalDerivativeLinear T c :=
  (affineScalar_hasFDerivAt _ 0).unique (simplexNodalInterpolant_hasFDerivAt T c 0)

theorem simplexNodalDerivative_tendsto (T : Affine.Simplex ℝ (SpatialCoordinates d) d)
    {f : SpatialCoordinates d → ℝ} {F : ℕ → SpatialCoordinates d → ℝ}
    (h : ∀ i, Tendsto (fun n => F n (T.points i)) atTop (𝓝 (f (T.points i)))) :
    Tendsto (fun n => affineScalarDerivative (simplexNodalInterpolant T (fun i => F n (T.points i)))) atTop
      (𝓝 (affineScalarDerivative (simplexNodalInterpolant T (fun i => f (T.points i))))) := by
  simp only [simplexNodal_affineDerivative_eq]
  exact (simplexNodalDerivativeLinear T).continuous_of_finiteDimensional.continuousAt.tendsto.comp
    (tendsto_pi_nhds.mpr h)

theorem firstDerivativeFiber_norm_sq (w : DerivativeFiber d 1) :
    ‖w‖^2=∑ i : Fin d, (w (Sym.cons i Sym.nil))^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  exact (Equiv.sum_comp Sym.oneEquiv (fun α : Sym (Fin d) 1 => (w α)^2)).symm

theorem firstDerivativeFiber_sub_norm_sq (w : DerivativeFiber d 1)
    (A : SpatialCoordinates d →L[ℝ] ℝ) :
    ‖w-derivativeOneFiber A‖^2=
      ∑ i : Fin d, (w (Sym.cons i Sym.nil)-A (EuclideanSpace.basisFun (Fin d) ℝ i))^2 := by
  rw [firstDerivativeFiber_norm_sq]
  apply Finset.sum_congr rfl
  intro i _
  rfl

end Carleman
