module

public import Carleman.Spatial.LipschitzWeakDerivative
public import Carleman.Spatial.FirstOrderSobolevJet

/-! Actual H¹ jets of every smooth compactly supported spatial test. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SpatialTest
variable {d : ℕ} {S : Set (SpatialCoordinates d)} (φ : SpatialTest S)

theorem memLp_fderiv : MemLp (fderiv ℝ φ.value) 2 (volume.restrict S) :=
  (φ.smooth.continuous_fderiv (by simp)).memLp_of_hasCompactSupport (φ.compact.fderiv ℝ)

def fderivLp : Lp (SpatialCoordinates d →L[ℝ] ℝ) 2 (volume.restrict S) :=
  φ.memLp_fderiv.toLp (fderiv ℝ φ.value)

theorem fderivLp_ae : φ.fderivLp =ᵐ[volume.restrict S] fderiv ℝ φ.value := MemLp.coeFn_toLp _

def sobolevJet : WeakSobolevJet d 1 (volume.restrict S) S := by
  apply firstOrderJet (φ.toLp (volume.restrict S)) φ.fderivLp
  intro i
  obtain ⟨C,hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport φ.compact φ.smooth (by simp)
  apply weakSpatialDerivative_of_lipschitz hC _ _ _ (φ.toLp_ae (volume.restrict S))
  filter_upwards [OperatorMultiplier.const_map_ae
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)) φ.fderivLp,φ.fderivLp_ae] with x hx hd
  rw [hd] at hx
  exact hx.trans ((φ.smooth.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv).symm

theorem sobolevJet_value : WeakSobolevJet.value φ.sobolevJet = φ.toLp (volume.restrict S) :=
  firstOrderJet_value _ _ _

end Carleman.SpatialTest
