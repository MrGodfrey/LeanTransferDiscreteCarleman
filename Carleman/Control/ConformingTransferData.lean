module

public import Carleman.Control.ConformingPhysicalControl
public import Carleman.Control.PhysicalTransferGeometry
public import Carleman.Transfer.HeatScaleUniform

/-! Actual consistent-mass reconstruction and original numerical/continuous
assumptions for a conforming heat family. No discrete CE is stored as data. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Physical
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {ν : Measure Ω}
  (V X : Submodule ℝ (Lp E 2 ν)) [CompleteSpace X] (hX : X ≤ V)

def conformingReconstruction : Reconstruction V X where
  R := X.inclusion hX
  J := X.orthogonalProjectionOnto.toLinearMap
  mass_adjoint v z := by
    change inner ℝ (X.orthogonalProjectionOnto v) z = inner ℝ v (z : Lp E 2 ν)
    rw [X.inner_orthogonalProjectionOnto_eq_of_mem_right]

@[simp] theorem conformingReconstruction_RH (x : X) :
    (conformingReconstruction V X hX).RH x = (x : Lp E 2 ν) := rfl

def conformingLoad : LoadInterface (conformingReconstruction V X hX) (Lp E 2 ν) where
  Γ := X.orthogonalProjectionOnto
  lift := id
  compatible _ := rfl

omit [CompleteSpace X] in
def conformingWeightedState (ρ : SpatialProfile ν) (w : TimeWeight) (t : ℝ) : Seminorm ℝ X :=
  (ρ.multiplier w 0 t).seminorm.comp X.subtype

omit [CompleteSpace X] in
theorem conformingWeightedState_definite (ρ : SpatialProfile ν) (w : TimeWeight)
    (t : ℝ) (x : X) (hx : conformingWeightedState X ρ w t x = 0) : x = 0 := by
  apply Subtype.ext
  exact (ρ.seminorm_definite w 0 t (x : Lp E 2 ν)).mp hx

end Carleman.Physical

@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Physical
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} {hS : IsOpen S} {hν : ∀ᵐ x ∂ν, x ∈ S}
  (a : OriginalForm (m := CarlemanExponents.heat.m) hS hν)
  (hD : a.model.domain ≤ sobolevSubspace d (2*CarlemanExponents.heat.m) ν S)
  (ρ : SpatialProfile ν)
  {Z : Fin CarlemanExponents.heat.m → Type*}
  [∀ j, NormedAddCommGroup (Z j)] [∀ j, InnerProductSpace ℝ (Z j)]
  (P : ∀ j : Fin CarlemanExponents.heat.m, DifferentialExpression ν
    (fun k : Fin (CarlemanExponents.heat.m+1) => DerivativeFiber d k.val) (Z j) (j.val+1))
  (obs : Set (SpatialCoordinates d)) (hobs : MeasurableSet obs)
  (X : Submodule ℝ (Lp ℝ 2 ν)) [CompleteSpace X] (hX : X ≤ a.V)
  (A : X →L[ℝ] X) (defect : X →ₗ[ℝ] X →ₗ[ℝ] ℝ)
  (g : TimeGrid) (w : TimeWeight)

/-- This geometry uses the actual L2 inclusion and indicator observation. -/
def conformingHeatGeometry : TransferGeometry a.V X (Lp ℝ 2 ν) (Lp ℝ 2 ν) CarlemanExponents.heat :=
  sobolevGeometry hS hν a.sobolev w ρ P obs hobs
    (conformingWeightedState X ρ w) (fun t => (ρ.multiplier w 0 t).seminorm)
    (fun t => (ρ.multiplier w 0 t).seminorm)
    (conformingWeightedState_definite X ρ w)
    (fun t f => (ρ.seminorm_definite w 0 t f).mp)
    (fun t f => (ρ.seminorm_definite w 0 t f).mp)

/-- Original A2/A3, N1--N5 and continuous A4, for the actual conforming
reconstruction. Concrete finite-element estimates are still to supply these
fields; neither periodic discrete CE nor physical observability is a field. -/
structure ConformingHeatData (c C Ccomm τStar Ctime Csuper Cnum Cce mesh : ℝ)
    (errors : ErrorScales) where
  allowed : Section3.AllowedFamily hS hν a.sobolev hD a.scalarForm a.model.operator ρ w c C Ccomm τStar
  numerical : Section5.NumericalData a hD (conformingReconstruction a.V X hX)
    A.toLinearMap defect (conformingLoad a.V X hX)
    (conformingAmbientControl X obs hobs).adjoint.toLinearMap g w ρ obs hobs
    (conformingWeightedState X ρ w) (fun t => (ρ.multiplier w 0 t).seminorm)
    (fun t => (ρ.multiplier w 0 t).seminorm) τStar Ctime Csuper Cnum mesh errors
  continuous : ∀ (s : Orientation) (U : PeriodicWeakTrajectory g a.model.domain a.model.operator),
    (conformingHeatGeometry a ρ P obs hobs X w).continuousEnergy g
      ((conformingHeatGeometry a ρ P obs hobs X w).trajectory g a.domain_le U) ≤ Cce *
      (timeSq g w.q 0 (conformingHeatGeometry a ρ P obs hobs X w).space
        (fun t => s.sign • U.derivative t+a.model.operator (U.domainValue t))+
      timeSq g w.q CarlemanExponents.heat.o (conformingHeatGeometry a ρ P obs hobs X w).observation
        (fun t => (U.domainValue t : Lp ℝ 2 ν)))

end Carleman.Physical
