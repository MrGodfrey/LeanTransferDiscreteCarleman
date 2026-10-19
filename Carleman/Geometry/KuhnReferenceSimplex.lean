module

public import Carleman.Spatial.AffineSimplex
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.Block

/-! The genuine reference Kuhn simplex, with vertices 0, e₀, e₀+e₁, ... .
An actual unit upper triangular map constructs its affine independence. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

def coordinateStandardSimplex (d : ℕ) : Affine.Simplex ℝ (SpatialCoordinates d) d where
  points := Fin.cons 0 (EuclideanSpace.basisFun (Fin d) ℝ)
  independent := by
    rw [affineIndependent_iff_linearIndependent_vsub ℝ _ 0]
    let f : {i : Fin (d+1) // i ≠ 0} → Fin d := fun i => i.val.pred i.property
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      have he := congrArg Fin.succ hab
      simpa only [f,Fin.succ_pred] using he
    convert (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.linearIndependent.comp f hf using 1
    funext i
    rw [vsub_eq_sub,Fin.cons_zero,sub_zero,← Fin.succ_pred i.val i.property,Fin.cons_succ]
    rfl

def kuhnPrefixMatrix (d : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => if i ≤ j then 1 else 0

theorem kuhnPrefixMatrix_det (d : ℕ) : (kuhnPrefixMatrix d).det=1 := by
  have ht : (kuhnPrefixMatrix d).IsUpperTriangular := by
    intro i j hji
    change j < i at hji
    exact ite_eq_right (not_le.mpr hji)
  rw [Matrix.det_of_isUpperTriangular ht]
  simp [kuhnPrefixMatrix]

def kuhnPrefixEquiv (d : ℕ) : SpatialCoordinates d ≃L[ℝ] SpatialCoordinates d :=
  (Matrix.toLinearEquiv (EuclideanSpace.basisFun (Fin d) ℝ).toBasis (kuhnPrefixMatrix d)
    (by rw [kuhnPrefixMatrix_det]; exact isUnit_one)).toContinuousLinearEquiv

theorem kuhnPrefixEquiv_basis (i j : Fin d) :
    kuhnPrefixEquiv d (EuclideanSpace.basisFun (Fin d) ℝ i) j = if j ≤ i then 1 else 0 := by
  change (Matrix.toLin (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis (kuhnPrefixMatrix d)
      ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis i)) j = _
  rw [Matrix.toLin_self]
  change (EuclideanSpace.proj j) (∑ k, kuhnPrefixMatrix d k i •
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis k) = _
  rw [map_sum]
  change (∑ k, kuhnPrefixMatrix d k i * (EuclideanSpace.basisFun (Fin d) ℝ k j)) = _
  simp [kuhnPrefixMatrix,EuclideanSpace.basisFun_apply]

def kuhnReferenceSimplex (d : ℕ) : Affine.Simplex ℝ (SpatialCoordinates d) d :=
  affineSimplex (coordinateStandardSimplex d) (kuhnPrefixEquiv d) 0

theorem kuhnReferenceSimplex_points (k : Fin (d+1)) (j : Fin d) :
    (kuhnReferenceSimplex d).points k j = if j.val < k.val then 1 else 0 := by
  induction k using Fin.cases with
  | zero =>
    simp [kuhnReferenceSimplex,affineSimplex_points,coordinateStandardSimplex,affineChange_apply]
  | succ k =>
    rw [kuhnReferenceSimplex,affineSimplex_points]
    simp only [coordinateStandardSimplex,Fin.cons_succ,affineChange_apply,add_zero,
      kuhnPrefixEquiv_basis,Fin.val_succ]
    congr 1
    exact propext (show j ≤ k ↔ j.val < k.val+1 from Nat.lt_succ_iff.symm)

end Carleman
