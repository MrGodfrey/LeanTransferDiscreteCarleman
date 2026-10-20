module
public import Carleman.Spatial.SubdomainWeightedExtension
public import Carleman.Spatial.DirichletHeatContinuity
/-! Actual values, weak time derivatives, operator values and weak spatial gradients in a common L² product. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

abbrev DirichletHeatFields (S : Set (SpatialCoordinates d)) (g : TimeGrid) :=
  Lp (Lp ℝ 2 (volume.restrict S)) 2 g.timeMeasure ×
  Lp (Lp ℝ 2 (volume.restrict S)) 2 g.timeMeasure ×
  Lp (Lp ℝ 2 (volume.restrict S)) 2 g.timeMeasure ×
  Lp (Lp (DerivativeFiber d 1) 2 (volume.restrict S)) 2 g.timeMeasure

def dirichletHeatFields {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hd : 0<d)
    (hb : Bornology.IsBounded S) (g : TimeGrid) :
    (boundedDirichletOriginalForm hS hd hb).model.PeriodicGraph g →L[ℝ] DirichletHeatFields S g :=
  let B := (boundedDirichletOriginalForm hS hd hb).model
  (g.fieldsValue.comp (B.periodicGraphSubmodule g).subtypeL).prod
    ((g.fieldsDerivative.comp (B.periodicGraphSubmodule g).subtypeL).prod
      ((g.fieldsOperator.comp (B.periodicGraphSubmodule g).subtypeL).prod
        (dirichletPeriodicGradient hS hd hb g)))

theorem dirichletHeatFields_apply {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hd : 0<d)
    (hb : Bornology.IsBounded S) (g : TimeGrid)
    (p : (boundedDirichletOriginalForm hS hd hb).model.PeriodicGraph g) :
    dirichletHeatFields hS hd hb g p=
      (g.pathL2 p.val.1,p.val.2.1,p.val.2.2,dirichletPeriodicGradient hS hd hb g p) := rfl

def subdomainHeatFields (S T : Set (SpatialCoordinates d)) (g : TimeGrid) :
    DirichletHeatFields T g →L[ℝ] DirichletHeatFields S g :=
  let e := (subdomainZeroExtendCLM (E := ℝ) S T).compLpL 2 g.timeMeasure
  let eG := (subdomainZeroExtendCLM (E := DerivativeFiber d 1) S T).compLpL 2 g.timeMeasure
  e.prodMap (e.prodMap (e.prodMap eG))

theorem subdomainHeatFields_apply (S T : Set (SpatialCoordinates d)) (g : TimeGrid)
    (p : DirichletHeatFields T g) :
    subdomainHeatFields S T g p=
      ((subdomainZeroExtendCLM S T).compLp p.1,
        (subdomainZeroExtendCLM S T).compLp p.2.1,
        (subdomainZeroExtendCLM S T).compLp p.2.2.1,
        (subdomainZeroExtendCLM S T).compLp p.2.2.2) := rfl

end Carleman
