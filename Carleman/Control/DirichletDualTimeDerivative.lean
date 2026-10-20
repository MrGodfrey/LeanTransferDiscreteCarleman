module

public import Carleman.Control.DirichletMassWeakDerivative

/-! The actual strong-dual Bochner right-hand side is the distributional time derivative of the original state. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology BigOperators NNReal ContDiff
namespace Carleman

variable {d : ℕ} {S : Set (SpatialCoordinates d)}

def dirichletPivotDual (S : Set (SpatialCoordinates d)) (hS : IsOpen S) :
    DirichletEnergyState S →L[ℝ] StrongDual ℝ (DirichletEnergyState S) :=
  (innerSL ℝ : DirichletEnergyState S →L[ℝ] StrongDual ℝ (DirichletEnergyState S)).comp
    (dirichletTimeMass S hS)

theorem dirichletPivotDual_apply (hS : IsOpen S) (v w : DirichletEnergyState S) :
    dirichletPivotDual S hS v w=inner ℝ (dirichletStateValue S v) (dirichletStateValue S w) := by
  let := dirichletEnergyState_complete hS
  exact (dirichletStateValue S).adjoint_inner_left w (dirichletStateValue S v)

def dirichletDualTimeLoad (T : ℝ) (hS : IsOpen S)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S)))
    (Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T)))
    (U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T))) :
    Lp (StrongDual ℝ (DirichletEnergyState S)) 2 (volume.restrict (Ioc 0 T)) :=
  (innerSL ℝ : DirichletEnergyState S →L[ℝ] StrongDual ℝ (DirichletEnergyState S)).compLpL 2
    (volume.restrict (Ioc 0 T)) (dirichletTimeLoad T hS b Y U)

theorem dirichletDualTimeLoad_pairing (T : ℝ) (hS : IsOpen S)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S)))
    (Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T)))
    (U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T)))
    (w : DirichletEnergyState S) (f : Lp ℝ 2 (volume.restrict (Ioc 0 T))) :
    let Yv := (dirichletStateValue S).compLpL 2 (volume.restrict (Ioc 0 T)) Y;
    let Yg := (dirichletStateGradient S).compLpL 2 (volume.restrict (Ioc 0 T)) Y;
    (∫ t, f t*(dirichletDualTimeLoad T hS b Y U t) w ∂(volume.restrict (Ioc 0 T)))=
      inner ℝ U (timeTensor T (dirichletStateValue S w) f)-
      inner ℝ Yg (timeTensor T (dirichletStateGradient S w) f)-
      inner ℝ (b.map (bochnerL2ProductIsometry Yv))
        (bochnerL2ProductIsometry (timeTensor T (dirichletStateValue S w) f)) := by
  intro Yv Yg
  calc
    _ = ∫ t, f t*inner ℝ (dirichletTimeLoad T hS b Y U t) w ∂(volume.restrict (Ioc 0 T)) := by
      apply integral_congr_ae
      filter_upwards [(innerSL ℝ : DirichletEnergyState S →L[ℝ] StrongDual ℝ (DirichletEnergyState S)).coeFn_compLpL
        (dirichletTimeLoad T hS b Y U)] with t ht
      change (dirichletDualTimeLoad T hS b Y U) t=innerSL ℝ ((dirichletTimeLoad T hS b Y U) t) at ht
      rw [ht]
      rfl
    _ = inner ℝ (dirichletTimeLoad T hS b Y U) (timeTensor T w f) := by
      rw [timeTensor_eq_scalarTensor,inner_scalarTensor]
    _ = _ := dirichletTimeLoad_pairing T hS b Y U w f


theorem FiniteDirichletControlIdentity.dual_weak_time_derivative
    {T : ℝ} (hTpos : 0 < T) (hS : IsOpen S) [IsFiniteMeasure (volume.restrict S)]
    {b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S))}
    {y0 : Lp ℝ 2 (volume.restrict S)}
    {Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T))}
    {U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T))}
    (hid : FiniteDirichletControlIdentity T S b y0 Y U)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo 0 T) :
    (∫ t, deriv φ t • dirichletPivotDual S hS (Y t) ∂(volume.restrict (Ioc 0 T)))=
      -(∫ t, φ t • dirichletDualTimeLoad T hS b Y U t ∂(volume.restrict (Ioc 0 T))) := by
  let := dirichletEnergyState_complete hS
  let g : TimeGrid := ⟨1,by decide,T,hTpos⟩
  have hT : g.period=T := by simp [g,TimeGrid.period]
  have hμ : g.timeMeasure=volume.restrict (Ioc 0 T) := by
    rw [TimeGrid.timeMeasure,hT,restrict_Ioo_eq_restrict_Ioc]
  let L : DirichletEnergyState S →L[ℝ] StrongDual ℝ (DirichletEnergyState S) := innerSL ℝ
  let mY := (dirichletTimeMass S hS).compLpL 2 (volume.restrict (Ioc 0 T)) Y
  let D := dirichletTimeLoad T hS b Y U
  have hm : MemLp mY 2 g.timeMeasure := by rw [hμ]; exact Lp.memLp mY
  have hd : MemLp D 2 g.timeMeasure := by rw [hμ]; exact Lp.memLp D
  have he := (hid.mass_weak_time_derivative hS g hT).map_integral hm hd L φ hφ hc (by simpa only [hT] using hs)
  rw [hμ] at he
  have he₁ : (∫ t, deriv φ t • L (mY t) ∂(volume.restrict (Ioc 0 T)))=
      ∫ t, deriv φ t • dirichletPivotDual S hS (Y t) ∂(volume.restrict (Ioc 0 T)) := by
    apply integral_congr_ae
    filter_upwards [(dirichletTimeMass S hS).coeFn_compLpL Y] with t ht
    change mY t=dirichletTimeMass S hS (Y t) at ht
    rw [ht]
    rfl
  have he₂ : (∫ t, φ t • L (D t) ∂(volume.restrict (Ioc 0 T)))=
      ∫ t, φ t • dirichletDualTimeLoad T hS b Y U t ∂(volume.restrict (Ioc 0 T)) := by
    apply integral_congr_ae
    filter_upwards [L.coeFn_compLpL D] with t ht
    change dirichletDualTimeLoad T hS b Y U t=L (D t) at ht
    rw [ht]
  exact he₁.symm.trans (he.trans (congrArg Neg.neg he₂))

end Carleman
