module

public import Carleman.Control.GalerkinStiffness
public import Carleman.Control.DirichletTimeWeakCompactness

/-! The actual Galerkin state lifted into the full original Dirichlet energy space. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

def dirichletGalerkinState (hS : IsOpen S) (hd : 0 < d) (hb : Bornology.IsBounded S)
    (X : Submodule ℝ (Lp ℝ 2 (volume.restrict S))) [FiniteDimensional ℝ X]
    (hX : X ≤ dirichletSubspace S) : X →L[ℝ] DirichletEnergyState S :=
  Physical.conformingEnergyLift (boundedDirichletOriginalForm hS hd hb) X hX

theorem dirichletGalerkinState_value (hS : IsOpen S) (hd : 0 < d) (hb : Bornology.IsBounded S)
    (X : Submodule ℝ (Lp ℝ 2 (volume.restrict S))) [FiniteDimensional ℝ X]
    (hX : X ≤ dirichletSubspace S) (x : X) :
    dirichletStateValue S (dirichletGalerkinState hS hd hb X hX x)=(x : Lp ℝ 2 (volume.restrict S)) := by
  have h := Physical.conformingEnergyLift_value (boundedDirichletOriginalForm hS hd hb) X hX x
  exact congrArg (fun z : dirichletSubspace S => (z : Lp ℝ 2 (volume.restrict S))) h

theorem dirichletGalerkinState_stiffness (hS : IsOpen S) (hd : 0 < d) (hb : Bornology.IsBounded S)
    (X : Submodule ℝ (Lp ℝ 2 (volume.restrict S))) [FiniteDimensional ℝ X]
    (hX : X ≤ dirichletSubspace S) (x y : X) :
    inner ℝ (Physical.galerkinStiffness (boundedDirichletOriginalForm hS hd hb) X hX x) y=
      inner ℝ (dirichletStateGradient S (dirichletGalerkinState hS hd hb X hX x))
        (dirichletStateGradient S (dirichletGalerkinState hS hd hb X hX y)) := by
  rw [Physical.galerkinStiffness_form]
  rfl

theorem dirichletGalerkinState_norm_sq (hS : IsOpen S) (hd : 0 < d) (hb : Bornology.IsBounded S)
    (X : Submodule ℝ (Lp ℝ 2 (volume.restrict S))) [FiniteDimensional ℝ X]
    (hX : X ≤ dirichletSubspace S) (x : X) :
    ‖dirichletGalerkinState hS hd hb X hX x‖^2=‖x‖^2+
      inner ℝ (Physical.galerkinStiffness (boundedDirichletOriginalForm hS hd hb) X hX x) x := by
  rw [dirichletEnergyState_norm_sq,dirichletGalerkinState_value,
    dirichletGalerkinState_stiffness,real_inner_self_eq_norm_sq]
  rfl

end Carleman
