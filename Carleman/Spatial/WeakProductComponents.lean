module

public import Carleman.Spatial.FirstWeakProduct
public import Carleman.Spatial.GradientPairing
public import Carleman.Spatial.DirichletDistribution

/-! Actual coordinate product fields and test identities for the
Dirichlet operator product rule. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff BigOperators
namespace Carleman
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
  {S : Set (SpatialCoordinates d)}

theorem weakGradientPairing_coordinates (u v : WeakSobolevJet d 1 ν S) :
    weakGradientPairing u v = ∑ i : Fin d,
      inner ℝ (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))
        (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 v)) :=
  firstDerivativeField_inner (WeakSobolevJet.field 1 u) (WeakSobolevJet.field 1 v)

theorem weakFirstProduct_component (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
    (w : BoundedMultiplier ν) (dw : Fin d → BoundedMultiplier ν)
    (hw : ContDiffOn ℝ ∞ w.value S)
    (hdw : ∀ i, (dw i).value =ᵐ[ν] (fun x => fderiv ℝ w.value x (EuclideanSpace.basisFun (Fin d) ℝ i)))
    (u : WeakSobolevJet d 1 ν S) (i : Fin d) :
    derivativeComponent (Sym.cons i Sym.nil)
      (WeakSobolevJet.field 1 (weakFirstProduct hS hν w dw hw hdw u)) =
      w.map (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))+
        (dw i).map (WeakSobolevJet.value u) := by
  change derivativeComponent (Sym.cons i Sym.nil)
    (w.map (E := DerivativeFiber d 1) (WeakSobolevJet.field (1 : Fin 2) u)+
      firstGradientAssembly (fun j => (dw j).map (WeakSobolevJet.value u))) = _
  rw [map_add,derivativeComponent_multiplier,firstGradientAssembly_component]

theorem weak_product_coordinate_test (hS : IsOpen S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (φ : SpatialTest S)
    (i : Fin d) (w dw : BoundedMultiplier (volume.restrict S))
    (hw : ContDiffOn ℝ ∞ w.value S)
    (hdw : dw.value =ᵐ[volume.restrict S]
      (fun x => fderiv ℝ w.value x (EuclideanSpace.basisFun (Fin d) ℝ i))) :
    inner ℝ (w.map (WeakSobolevJet.value u))
      (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i)) =
      -inner ℝ (w.map (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))+
        dw.map (WeakSobolevJet.value u)) (φ.toLp (volume.restrict S)) :=
  ((WeakSobolevJet.field_weak_derivative u 0 Sym.nil i).mul hS
    (ae_restrict_mem hS.measurableSet) w dw hw hdw) φ

end Carleman
