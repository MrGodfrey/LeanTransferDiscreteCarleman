module

public import Carleman.Control.PivotTimeContinuity
public import Carleman.Control.DirichletRegularizedPaths

/-! The original weak control state has a true closed-interval H-continuous representative. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman
set_option backward.isDefEq.respectTransparency true in
theorem FiniteDirichletControlIdentity.continuous_H_representative
    {d : ℕ} {S : Set (SpatialCoordinates d)} {T : ℝ}
    (hTpos : 0 < T) (hS : IsOpen S) [IsFiniteMeasure (volume.restrict S)]
    {b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S))}
    {y0 : Lp ℝ 2 (volume.restrict S)}
    {Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T))}
    {U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T))}
    (hid : FiniteDirichletControlIdentity T S b y0 Y U) :
    ∃ q : ℝ → Lp ℝ 2 (volume.restrict S), ContinuousOn q (Icc 0 T) ∧
      q =ᵐ[volume.restrict (Ioc 0 T)] (fun t => dirichletStateValue S (Y t)) := by
  let := dirichletEnergyState_complete hS
  let g : TimeGrid := ⟨1,by decide,T,hTpos⟩
  have hT : g.period=T := by simp [g,TimeGrid.period]
  have hμ : g.timeMeasure=volume.restrict (Ioc 0 T) := by
    rw [TimeGrid.timeMeasure,hT,restrict_Ioo_eq_restrict_Ioc]
  have hE : Function.Injective (dirichletStateValue S) :=
    conformingEmbed_injective (dirichletSubspace S) hS (ae_restrict_mem hS.measurableSet)
  have hex := exists_pivot_time_representative (V := DirichletEnergyState S) hμ
    (dirichletStateValue S) hE Y (dirichletTimeLoad T hS b Y U)
    (hid.mass_weak_time_derivative hS g hT)
  simpa only [hT] using hex

end Carleman
