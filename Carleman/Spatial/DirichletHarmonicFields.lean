module
public import Carleman.Spatial.WeakTrajectoryHeatEnergies
public import Carleman.Continuous.HarmonicGraphFields
/-! The four actual Bochner fields of a harmonic original Dirichlet graph. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hd : 0<d)
  (hb : Bornology.IsBounded S) (g : TimeGrid) (j : ℤ)
  (x y : (boundedDirichletOriginalForm hS hd hb).model.operatorGraph)

theorem dirichlet_harmonic_value_Lp :
    let B := (boundedDirichletOriginalForm hS hd hb).model
    g.pathL2 (B.harmonicGraph g j x y).val.1=g.harmonicLp j (B.graphH x) (B.graphH y) := by
  intro B
  apply Lp.ext
  filter_upwards [g.pathL2_ae (B.harmonicGraph g j x y).val.1,
    g.harmonicLp_ae j (B.graphH x) (B.graphH y),ae_restrict_mem measurableSet_Ioo]
    with t h1 h2 ht
  rw [h1,g.clampPath_on _ t ⟨ht.1.le,ht.2.le⟩,B.harmonicGraph_trace,h2]

theorem dirichlet_harmonic_derivative_Lp :
    let B := (boundedDirichletOriginalForm hS hd hb).model
    (B.harmonicGraph g j x y).val.2.1=
      g.harmonicLp j (g.angularFrequency j • B.graphH y) (-g.angularFrequency j • B.graphH x) := by
  intro B
  apply Lp.ext
  filter_upwards [B.harmonicGraph_derivative_ae g j x y,
    g.harmonicLp_ae j (g.angularFrequency j • B.graphH y) (-g.angularFrequency j • B.graphH x)]
    with t h1 h2
  rw [h1,h2]
  simp only [harmonicDerivative,harmonicValue,smul_smul]
  module

theorem dirichlet_harmonic_operator_Lp :
    let B := (boundedDirichletOriginalForm hS hd hb).model
    (B.harmonicGraph g j x y).val.2.2=g.harmonicLp j (B.graphA x) (B.graphA y) := by
  intro B
  exact Lp.ext ((B.harmonicGraph_operator_ae g j x y).trans (g.harmonicLp_ae j _ _).symm)

theorem dirichlet_harmonic_gradient_Lp :
    let B := (boundedDirichletOriginalForm hS hd hb).model
    dirichletPeriodicGradient hS hd hb g (B.harmonicGraph g j x y)=
      g.harmonicLp j (WeakSobolevJet.field 1 (dirichletDomainJet hS hd hb (B.graphDomain x)))
        (WeakSobolevJet.field 1 (dirichletDomainJet hS hd hb (B.graphDomain y))) := by
  intro B
  let X := dirichletDomainJet hS hd hb (B.graphDomain x)
  let Y := dirichletDomainJet hS hd hb (B.graphDomain y)
  have hg := dirichletTrajectory_gradient_ae hS hd hb g
    (B.harmonicTrajectory g j (B.graphDomain x) (B.graphDomain y))
  apply Lp.ext
  filter_upwards [hg,g.harmonicLp_ae j (WeakSobolevJet.field 1 X) (WeakSobolevJet.field 1 Y)]
    with t hgrad hfield
  let a := Real.cos (g.angularFrequency j*t)
  let b := Real.sin (g.angularFrequency j*t)
  have hj : dirichletDomainJet hS hd hb
      (B.harmonicDomain (g.angularFrequency j) (B.graphDomain x) (B.graphDomain y) t)=a • X+b • Y := by
    apply WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)
    rw [dirichletDomainJet_value]
    change harmonicValue (g.angularFrequency j) (B.graphH x) (B.graphH y) t=
      WeakSobolevJet.valueCLM (a • X+b • Y)
    simp only [map_add,map_smul,WeakSobolevJet.valueCLM_apply,X,Y,dirichletDomainJet_value]
    rfl
  change dirichletPeriodicGradient hS hd hb g
    (B.harmonicTrajectory g j (B.graphDomain x) (B.graphDomain y)).toPeriodicGraph t=
      g.harmonicLp j (WeakSobolevJet.field 1 X) (WeakSobolevJet.field 1 Y) t
  rw [hgrad,hfield]
  change WeakSobolevJet.field 1 (dirichletDomainJet hS hd hb
    (domainRepresentative B.domain (harmonicValue (g.angularFrequency j)
      (B.graphDomain x : Lp ℝ 2 (volume.restrict S)) (B.graphDomain y : Lp ℝ 2 (volume.restrict S))) t))=_
  rw [B.harmonicDomain_representative,hj]
  change (WeakSobolevJet.fieldCLM 1) (a • X+b • Y)=_
  simp only [map_add,map_smul]
  rfl

end Carleman
