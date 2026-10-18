module

public import Carleman.Control.ConformingTransferData
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Actual consistent-mass Galerkin stiffness on every finite conforming L2
subspace. Symmetry, positivity and the zero stiffness defect are conclusions. -/
@[expose] public noncomputable section
open MeasureTheory Set InnerProductSpace
namespace Carleman.Physical
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} {hS : IsOpen S} {hν : ∀ᵐ x ∂ν, x ∈ S}
  (a : OriginalForm (m := m) hS hν)
  (X : Submodule ℝ (Lp ℝ 2 ν)) [FiniteDimensional ℝ X] (hX : X ≤ a.V)

def conformingEnergyLift : X →L[ℝ] a.Energy :=
  (a.valueEquiv.symm.toLinearMap.comp (X.inclusion hX)).toContinuousLinearMap

@[simp] theorem conformingEnergyLift_value (x : X) :
    a.valueEquiv (conformingEnergyLift a X hX x) = X.inclusion hX x :=
  a.valueEquiv.apply_symm_apply _

def galerkinStiffness : X →L[ℝ] X :=
  (toDual ℝ X).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (a.form.bilinearComp (conformingEnergyLift a X hX) (conformingEnergyLift a X hX))

theorem galerkinStiffness_form (x y : X) :
    inner ℝ (galerkinStiffness a X hX x) y =
      a.scalarForm (X.inclusion hX x) (X.inclusion hX y) := by
  change inner ℝ ((toDual ℝ X).symm
    (a.form.bilinearComp (conformingEnergyLift a X hX) (conformingEnergyLift a X hX) x)) y = _
  rw [toDual_symm_apply]
  rfl

theorem galerkinStiffness_symmetric : (galerkinStiffness a X hX).IsSymmetric := by
  intro x y
  calc
    inner ℝ (galerkinStiffness a X hX x) y =
        a.scalarForm (X.inclusion hX x) (X.inclusion hX y) := galerkinStiffness_form a X hX x y
    _ = a.scalarForm (X.inclusion hX y) (X.inclusion hX x) := a.symmetric _ _
    _ = inner ℝ (galerkinStiffness a X hX y) x := (galerkinStiffness_form a X hX y x).symm
    _ = inner ℝ x (galerkinStiffness a X hX y) := real_inner_comm _ _

theorem galerkinStiffness_nonneg (x : X) : 0 ≤ inner ℝ (galerkinStiffness a X hX x) x := by
  rw [galerkinStiffness_form]
  obtain ⟨c,hc,hcoer⟩ := a.coercive
  exact (mul_nonneg (mul_nonneg hc.le (norm_nonneg _)) (norm_nonneg _)).trans
    (hcoer (a.valueEquiv.symm (X.inclusion hX x)))

theorem galerkinStiffness_unique (A : X →L[ℝ] X)
    (hA : ∀ x y, inner ℝ (A x) y = a.scalarForm (X.inclusion hX x) (X.inclusion hX y)) :
    A = galerkinStiffness a X hX := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [hA,galerkinStiffness_form]

theorem galerkinStiffness_defect_zero (x y : X) :
    inner ℝ (galerkinStiffness a X hX x) y =
      a.scalarForm ((conformingReconstruction a.V X hX).R x)
        ((conformingReconstruction a.V X hX).R y)+(0 : X →ₗ[ℝ] X →ₗ[ℝ] ℝ) x y := by
  simpa only [conformingReconstruction,LinearMap.zero_apply,add_zero] using galerkinStiffness_form a X hX x y

end Carleman.Physical
