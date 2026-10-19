module

public import Carleman.Spatial.AffineWeakTransport
public import Carleman.Spatial.SobolevJet
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Reflection across an actual coordinate hyperplane as a volume-preserving
smooth affine isometry, with exact coordinate and derivative formulas. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

def coordinateSignFlip (r : Fin d) : SpatialCoordinates d ≃ₗᵢ[ℝ] SpatialCoordinates d :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun j => if j=r then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

theorem coordinateSignFlip_apply (r : Fin d) (x : SpatialCoordinates d) (j : Fin d) :
    coordinateSignFlip r x j=if j=r then -(x j) else x j := by
  classical
  by_cases hj : j=r <;> simp [coordinateSignFlip,hj]

def coordinateReflection (r : Fin d) (c : ℝ) : SpatialCoordinates d ≃ₜ SpatialCoordinates d :=
  affineSpatialChart (coordinateSignFlip r).toContinuousLinearEquiv
    ((2*c) • EuclideanSpace.basisFun (Fin d) ℝ r)

theorem coordinateReflection_apply (r : Fin d) (c : ℝ) (x : SpatialCoordinates d) (j : Fin d) :
    coordinateReflection r c x j=if j=r then 2*c-x j else x j := by
  classical
  change coordinateSignFlip r x j+((2*c) • EuclideanSpace.basisFun (Fin d) ℝ r) j=_
  rw [coordinateSignFlip_apply]
  by_cases hj : j=r
  · subst j; simp [EuclideanSpace.basisFun_apply,EuclideanSpace.single,sub_eq_add_neg,add_comm]
  · simp [EuclideanSpace.basisFun_apply,EuclideanSpace.single,hj]

theorem coordinateReflection_involutive (r : Fin d) (c : ℝ) :
    Function.Involutive (coordinateReflection r c) := by
  intro x
  ext j
  simp only [coordinateReflection_apply]
  by_cases hj : j=r <;> simp [hj]

theorem coordinateReflection_symm (r : Fin d) (c : ℝ) :
    (coordinateReflection r c).symm=coordinateReflection r c := by
  apply Homeomorph.ext
  intro x
  apply (coordinateReflection r c).injective
  rw [Homeomorph.apply_symm_apply,coordinateReflection_involutive]

theorem coordinateReflection_measurePreserving (r : Fin d) (c : ℝ) :
    MeasurePreserving (coordinateReflection r c) volume volume :=
  (measurePreserving_add_right volume ((2*c) • EuclideanSpace.basisFun (Fin d) ℝ r)).comp
    (coordinateSignFlip r).measurePreserving

def coordinateReflectionSign (r i : Fin d) : ℝ := if i=r then -1 else 1

theorem coordinateReflectionSign_sq (r i : Fin d) : (coordinateReflectionSign r i)^2=1 := by
  unfold coordinateReflectionSign
  split <;> norm_num

theorem coordinateSignFlip_basis (r i : Fin d) :
    coordinateSignFlip r (EuclideanSpace.basisFun (Fin d) ℝ i)=
      coordinateReflectionSign r i • EuclideanSpace.basisFun (Fin d) ℝ i := by
  classical
  ext j
  rw [coordinateSignFlip_apply]
  by_cases hji : j=i
  · subst j
    by_cases hi : i=r <;> simp [EuclideanSpace.basisFun_apply,EuclideanSpace.single,coordinateReflectionSign,hi]
  · simp [EuclideanSpace.basisFun_apply,EuclideanSpace.single,hji]

end Carleman
