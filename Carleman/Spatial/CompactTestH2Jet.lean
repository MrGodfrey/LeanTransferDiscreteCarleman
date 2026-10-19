module

public import Carleman.Spatial.CompactTestHessianEnergy
public import Carleman.Spatial.WeakH2BoundedTest
public import Carleman.Spatial.WeakLaplacian

/-! Every original compactly supported smooth test has its actual H² jet.
The Hessian estimate follows from the proved interior energy identity,
and the resulting Laplacian is the sum of its genuine second derivatives. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman.SpatialTest
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

def laplacianLp (φ : SpatialTest S) : Lp ℝ 2 (volume.restrict S) :=
  ∑ i : Fin d, (φ.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).derivativeLp
    (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i)

theorem exists_H2_jet (hS : IsOpen S) (φ : SpatialTest S) :
    ∃ v : WeakSobolevJet d 2 (volume.restrict S) S,
      WeakSobolevJet.truncate (by decide : 1 ≤ 2) v = φ.sobolevJet ∧
      negativeLaplacian v = -φ.laplacianLp ∧
      ‖WeakSobolevJet.field 2 v‖^2 ≤ (Fintype.card (Sym (Fin d) 2) : ℝ)*‖φ.laplacianLp‖^2 := by
  obtain ⟨v,hv,hvn⟩ := exists_weakH2_of_gradient_test_bounds hS φ.sobolevJet
    (C := ‖φ.laplacianLp‖) (norm_nonneg _) (by
      intro i j ψ
      rw [φ.sobolevJet_derivative]
      have hw := (φ.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).weakDerivative
        (EuclideanSpace.basisFun (Fin d) ℝ j) ψ
      rw [φ.derivativeTest_toLp] at hw
      rw [hw,abs_neg]
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
        (φ.hessian_component_norm_le_laplacian i j) (norm_nonneg _)))
  refine ⟨v,hv,?_,hvn⟩
  rw [negativeLaplacian_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hfirst := congrArg (fun w => derivativeComponent (Sym.cons i Sym.nil)
    (WeakSobolevJet.field 1 w)) hv
  change derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 v) = _ at hfirst
  rw [φ.sobolevJet_derivative] at hfirst
  have hw := v.property 1 (Sym.cons i Sym.nil) i
  change IsWeakSpatialDerivative (volume.restrict S) S _
    (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 v)) _ at hw
  rw [hfirst] at hw
  have ht := (φ.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).weakDerivative
    (EuclideanSpace.basisFun (Fin d) ℝ i)
  rw [φ.derivativeTest_toLp] at ht
  exact hw.unique hS (ae_restrict_mem hS.measurableSet) ht

end Carleman.SpatialTest
