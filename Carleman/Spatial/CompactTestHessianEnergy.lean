module

public import Carleman.Spatial.SpatialTestDerivative
public import Carleman.Spatial.TestPoincare

/-! Exact Hessian--Laplacian energy for actual compactly supported smooth
tests. This interior identity has no boundary term; extending it to
Dirichlet functions with nonzero normal derivative requires separate work. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman.SpatialTest
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem mixed_derivative_norm_sq (φ : SpatialTest S) (e f : SpatialCoordinates d) :
    ‖(φ.derivativeTest e).derivativeLp (volume.restrict S) f‖^2 =
      inner ℝ ((φ.derivativeTest e).derivativeLp (volume.restrict S) e)
        ((φ.derivativeTest f).derivativeLp (volume.restrict S) f) := by
  have h1 := (φ.derivativeTest e).weakDerivative e ((φ.derivativeTest f).derivativeTest f)
  have h2 := (φ.derivativeTest e).weakDerivative f ((φ.derivativeTest f).derivativeTest e)
  simp only [derivativeTest_toLp] at h1 h2
  rw [(φ.derivativeTest f).derivativeTest_derivativeLp_commute f e (volume.restrict S)] at h1
  rw [φ.derivativeTest_derivativeLp_commute f e (volume.restrict S),real_inner_self_eq_norm_sq] at h2
  linarith

theorem hessian_energy_eq_laplacian (φ : SpatialTest S) :
    (∑ i : Fin d, ∑ j : Fin d,
      ‖(φ.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).derivativeLp
        (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ j)‖^2) =
      ‖∑ i : Fin d, (φ.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).derivativeLp
        (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i)‖^2 := by
  rw [← real_inner_self_eq_norm_sq,sum_inner]
  simp only [inner_sum,φ.mixed_derivative_norm_sq]

theorem hessian_component_norm_le_laplacian (φ : SpatialTest S) (i j : Fin d) :
    ‖(φ.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).derivativeLp
      (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ j)‖ ≤
      ‖∑ k : Fin d, (φ.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ k)).derivativeLp
        (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ k)‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← φ.hessian_energy_eq_laplacian]
  let D := fun k l : Fin d => (φ.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ k)).derivativeLp
    (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ l)
  change ‖D i j‖^2 ≤ ∑ k : Fin d, ∑ l : Fin d, ‖D k l‖^2
  calc
    _ ≤ ∑ l : Fin d, ‖D i l‖^2 :=
      Finset.single_le_sum (fun l _ => sq_nonneg ‖D i l‖) (Finset.mem_univ j)
    _ ≤ _ := Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg ‖D k l‖)
      (Finset.mem_univ i)

end Carleman.SpatialTest
