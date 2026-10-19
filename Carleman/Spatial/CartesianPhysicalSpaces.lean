module

public import Carleman.Spatial.PhysicalFiniteSpace
public import Carleman.Spatial.CartesianNodalControl
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The original full state and control Hilbert spaces carry precisely the
physical mass inner products. Their actual Hilbert adjoint is nodal restriction. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

abbrev CartesianPhysicalState (δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ) :=
  PhysicalFiniteSpace (CartesianInteriorIndex N) (∏ j, δ j) (Finset.prod_pos (fun j _ => hδ j))

abbrev CartesianPhysicalControl (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ω : Set (SpatialCoordinates d)) :=
  PhysicalFiniteSpace (CartesianObservationIndex o δ N ω) (∏ j, δ j) (Finset.prod_pos (fun j _ => hδ j))

theorem cartesianPhysicalState_inner (δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (f g : CartesianPhysicalState δ hδ N) :
    inner ℝ f g=cartesianPhysicalInner δ N f g := rfl

theorem cartesianPhysicalControl_inner (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ω : Set (SpatialCoordinates d)) (v z : CartesianPhysicalControl o δ hδ N ω) :
    inner ℝ v z=cartesianControlPhysicalInner o δ N ω v z := by
  classical
  rfl

def cartesianPhysicalControlExtension (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ω : Set (SpatialCoordinates d)) :
    CartesianPhysicalControl o δ hδ N ω →L[ℝ] CartesianPhysicalState δ hδ N := by
  classical
  exact LinearMap.toContinuousLinearMap
    (PhysicalFiniteSpace.valuesEquiv.symm.toLinearMap.comp
      ((cartesianControlExtension o δ N ω).comp PhysicalFiniteSpace.valuesEquiv.toLinearMap))

def cartesianPhysicalControlRestriction (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ω : Set (SpatialCoordinates d)) :
    CartesianPhysicalState δ hδ N →L[ℝ] CartesianPhysicalControl o δ hδ N ω := by
  classical
  exact LinearMap.toContinuousLinearMap
    (PhysicalFiniteSpace.valuesEquiv.symm.toLinearMap.comp
      ((cartesianControlRestriction o δ N ω).comp PhysicalFiniteSpace.valuesEquiv.toLinearMap))

theorem cartesianPhysicalControlExtension_values (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ω : Set (SpatialCoordinates d)) (v : CartesianPhysicalControl o δ hδ N ω) :
    ⇑(cartesianPhysicalControlExtension o δ hδ N ω v)=cartesianControlExtension o δ N ω v := rfl

theorem cartesianPhysicalControlRestriction_values (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ω : Set (SpatialCoordinates d)) (f : CartesianPhysicalState δ hδ N) :
    ⇑(cartesianPhysicalControlRestriction o δ hδ N ω f)=cartesianControlRestriction o δ N ω f := rfl

theorem cartesianPhysicalControl_adjoint (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ω : Set (SpatialCoordinates d)) :
    (cartesianPhysicalControlExtension o δ hδ N ω).adjoint=cartesianPhysicalControlRestriction o δ hδ N ω := by
  classical
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right,cartesianPhysicalState_inner,cartesianPhysicalControl_inner]
  exact cartesianControlExtension_pairing o δ N ω v f

def cartesianPhysicalStateWeight (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (σ : SpatialCoordinates d → ℝ) :
    CartesianPhysicalState δ hδ N →L[ℝ] CartesianPhysicalState δ hδ N :=
  PhysicalFiniteSpace.multiplier (fun a => σ (cartesianInteriorPoint o δ N a))

def cartesianPhysicalControlWeight (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ω : Set (SpatialCoordinates d)) (σ : SpatialCoordinates d → ℝ) :
    CartesianPhysicalControl o δ hδ N ω →L[ℝ] CartesianPhysicalControl o δ hδ N ω := by
  classical
  exact PhysicalFiniteSpace.multiplier (fun a => σ (cartesianInteriorPoint o δ N a.val))

theorem cartesianPhysicalStateWeight_norm_sq (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (σ : SpatialCoordinates d → ℝ) (f : CartesianPhysicalState δ hδ N) :
    ‖cartesianPhysicalStateWeight o δ hδ N σ f‖^2=cartesianWeightedNodeEnergy o δ N σ f :=
  PhysicalFiniteSpace.multiplier_norm_sq _ _

theorem cartesianPhysicalControlWeight_norm_sq (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ω : Set (SpatialCoordinates d)) (σ : SpatialCoordinates d → ℝ)
    (v : CartesianPhysicalControl o δ hδ N ω) :
    ‖cartesianPhysicalControlWeight o δ hδ N ω σ v‖^2=cartesianControlWeightedSq o δ N ω σ v := by
  classical
  exact PhysicalFiniteSpace.multiplier_norm_sq _ _

end Carleman
