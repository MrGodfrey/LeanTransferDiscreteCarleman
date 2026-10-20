module

public import Carleman.Control.TensorAdjointPairing

/-! The pivot mass and bounded control, gradient and original product-potential load in the true energy space. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology BigOperators NNReal ContDiff
namespace Carleman

variable {d : ℕ} {S : Set (SpatialCoordinates d)}

def dirichletTimeMass (S : Set (SpatialCoordinates d)) (hS : IsOpen S) :
    DirichletEnergyState S →L[ℝ] DirichletEnergyState S := by
  letI := dirichletEnergyState_complete hS
  exact (dirichletStateValue S).adjoint.comp (dirichletStateValue S)

def dirichletTimeLoad (T : ℝ) (hS : IsOpen S)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S)))
    (Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T)))
    (U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T))) :
    Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T)) := by
  letI := dirichletEnergyState_complete hS
  let E := (dirichletStateValue S).compLpL 2 (volume.restrict (Ioc 0 T))
  let G := (dirichletStateGradient S).compLpL 2 (volume.restrict (Ioc 0 T))
  let J := (bochnerL2ProductIsometry (μ := volume.restrict (Ioc 0 T)) (ν := volume.restrict S)).toContinuousLinearMap
  exact E.adjoint U-G.adjoint (G Y)-E.adjoint (J.adjoint (b.map (J (E Y))))

attribute [local irreducible] timeTensor bochnerL2ProductIsometry

set_option backward.isDefEq.respectTransparency true in
theorem dirichletTimeMass_pairing (T : ℝ) (hS : IsOpen S)
    (Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T)))
    (w : DirichletEnergyState S) (f : Lp ℝ 2 (volume.restrict (Ioc 0 T))) :
    inner ℝ ((dirichletTimeMass S hS).compLpL 2 (volume.restrict (Ioc 0 T)) Y) (timeTensor T w f)=
      inner ℝ ((dirichletStateValue S).compLpL 2 (volume.restrict (Ioc 0 T)) Y)
        (timeTensor T (dirichletStateValue S w) f) := by
  let := dirichletEnergyState_complete hS
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(dirichletTimeMass S hS).coeFn_compLpL Y,
    (dirichletStateValue S).coeFn_compLpL Y,timeTensor_ae T w f,
    timeTensor_ae T (dirichletStateValue S w) f] with t ht he hw hv
  simp only [ht,he,hw,hv,real_inner_smul_right]
  congr 1
  exact (dirichletStateValue S).adjoint_inner_left w (dirichletStateValue S (Y t))


theorem dirichletTimeLoad_pairing (T : ℝ) (hS : IsOpen S)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S)))
    (Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T)))
    (U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T)))
    (w : DirichletEnergyState S) (f : Lp ℝ 2 (volume.restrict (Ioc 0 T))) :
    let Yv := (dirichletStateValue S).compLpL 2 (volume.restrict (Ioc 0 T)) Y;
    let Yg := (dirichletStateGradient S).compLpL 2 (volume.restrict (Ioc 0 T)) Y;
    inner ℝ (dirichletTimeLoad T hS b Y U) (timeTensor T w f)=
      inner ℝ U (timeTensor T (dirichletStateValue S w) f)-
      inner ℝ Yg (timeTensor T (dirichletStateGradient S w) f)-
      inner ℝ (b.map (bochnerL2ProductIsometry Yv))
        (bochnerL2ProductIsometry (timeTensor T (dirichletStateValue S w) f)) := by
  let := dirichletEnergyState_complete hS
  dsimp only [dirichletTimeLoad]
  simp only [inner_sub_left,ContinuousLinearMap.adjoint_inner_left,timeTensor_map,
    LinearIsometry.coe_toContinuousLinearMap]


end Carleman
