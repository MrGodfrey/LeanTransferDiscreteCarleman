module

public import Carleman.Control.MassRegularizedPaths
public import Carleman.Control.DirichletMassRegularization
public import Carleman.Control.DirichletMassWeakDerivative

/-! The same original control state and load are strongly approximated by genuine continuous energy paths. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman
set_option backward.isDefEq.respectTransparency true in
theorem FiniteDirichletControlIdentity.regularized_time_paths
    {d : ℕ} {S : Set (SpatialCoordinates d)} {T : ℝ}
    (hS : IsOpen S) [IsFiniteMeasure (volume.restrict S)]
    {b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S))}
    {y0 : Lp ℝ 2 (volume.restrict S)}
    {Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T))}
    {U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T))}
    (hid : FiniteDirichletControlIdentity T S b y0 Y U)
    (g : TimeGrid) (hT : g.period=T)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    ∃ u du : ℕ → ℝ → DirichletEnergyState S,
    ∃ hu : ∀ n, MemLp (u n) 2 (volume.restrict (Ioc 0 T)),
    ∃ hd : ∀ n, MemLp (du n) 2 (volume.restrict (Ioc 0 T)),
      (∀ n, ContinuousOn (u n) (Icc 0 T)) ∧
      (∀ n, HasWeakTimeDerivative g (u n) (du n)) ∧
      (∀ n, u n =ᵐ[volume.restrict (Ioc 0 T)]
        (fun t => dirichletMassRegularizer S hS (ε n) (hε n) (Y t))) ∧
      (∀ n, (fun t => dirichletTimeMass S hS (du n t)) =ᵐ[volume.restrict (Ioc 0 T)]
        (fun t => dirichletMassRegularizer S hS (ε n) (hε n) (dirichletTimeLoad T hS b Y U t))) ∧
      Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 Y) ∧
      Tendsto (fun n => ((hd n).continuousLinearMap_comp (dirichletTimeMass S hS)).toLp
        (fun t => dirichletTimeMass S hS (du n t))) atTop (𝓝 (dirichletTimeLoad T hS b Y U)) := by
  subst T
  let := dirichletEnergyState_complete hS
  have hμ : g.timeMeasure=volume.restrict (Ioc 0 g.period) := by
    rw [TimeGrid.timeMeasure,restrict_Ioo_eq_restrict_Ioc]
  have hex := mass_regularized_time_paths (V := DirichletEnergyState S) (dirichletTimeMass S hS) (dirichletTimeMass_nonneg hS)
    (dirichletTimeMass_dense hS) hμ Y (dirichletTimeLoad g.period hS b Y U)
    (hid.mass_weak_time_derivative hS g rfl) ε hε hlim
  simpa only [dirichletMassRegularizer] using hex

end Carleman
