module

public import Carleman.Control.DirichletDualMassEquivalence
public import Carleman.Control.DirichletEnergyUniqueness
public import Carleman.Control.DirichletNullControlState

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman

/-- The original V'-valued energy equation and initial trace, with no terminal constraint. -/
def DirichletEnergySolution {d : ℕ} (T : ℝ) (S : Set (SpatialCoordinates d))
    (hS : IsOpen S) [IsFiniteMeasure (volume.restrict S)]
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S)))
    (y0 : Lp ℝ 2 (volume.restrict S))
    (Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T)))
    (U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T))) : Prop :=
  ∃ q : ℝ → Lp ℝ 2 (volume.restrict S), ContinuousOn q (Icc 0 T) ∧
    q =ᵐ[volume.restrict (Ioc 0 T)] (fun t => dirichletStateValue S (Y t)) ∧ q 0=y0 ∧
    ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo 0 T →
      (∫ t, deriv φ t • dirichletPivotDual S hS (Y t) ∂(volume.restrict (Ioc 0 T)))=
        -(∫ t, φ t • dirichletDualTimeLoad T hS b Y U t ∂(volume.restrict (Ioc 0 T)))

theorem DirichletNullControlState.energy_solution
    {d : ℕ} {S : Set (SpatialCoordinates d)} {T : ℝ}
    {hS : IsOpen S} [IsFiniteMeasure (volume.restrict S)]
    {b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S))}
    {y0 : Lp ℝ 2 (volume.restrict S)}
    {Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T))}
    {U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T))}
    (hy : DirichletNullControlState T S hS b y0 Y U) :
    DirichletEnergySolution T S hS b y0 Y U := by
  obtain ⟨q,hc,hq,h0,_,hw⟩ := hy
  exact ⟨q,hc,hq,h0,hw⟩

theorem DirichletEnergySolution.mass_weak_time_derivative
    {d : ℕ} {S : Set (SpatialCoordinates d)} {T : ℝ}
    {hS : IsOpen S} [IsFiniteMeasure (volume.restrict S)]
    {b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S))}
    {y0 : Lp ℝ 2 (volume.restrict S)}
    {Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T))}
    {U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T))}
    (hy : DirichletEnergySolution T S hS b y0 Y U) (g : TimeGrid) (hT : g.period=T) :
    HasWeakTimeDerivative g ((dirichletTimeMass S hS).compLpL 2 (volume.restrict (Ioc 0 T)) Y)
      (dirichletTimeLoad T hS b Y U) := by
  obtain ⟨q,_,_,_,hw⟩ := hy
  exact (dirichlet_dual_mass_weak_iff hS b Y U g hT).mp hw

theorem DirichletEnergySolution.unique
    {d : ℕ} {S : Set (SpatialCoordinates d)} {T : ℝ}
    (hTpos : 0 < T) {hS : IsOpen S} [IsFiniteMeasure (volume.restrict S)]
    {b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S))}
    {y0 : Lp ℝ 2 (volume.restrict S)}
    {Y Z : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T))}
    {U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T))}
    (hy : DirichletEnergySolution T S hS b y0 Y U)
    (hz : DirichletEnergySolution T S hS b y0 Z U) : Y=Z := by
  let g : TimeGrid := ⟨1,by decide,T,hTpos⟩
  have hT : g.period=T := by simp [g,TimeGrid.period]
  have hwY := hy.mass_weak_time_derivative g hT
  have hwZ := hz.mass_weak_time_derivative g hT
  obtain ⟨q,hq,hqa,hq0,_⟩ := hy
  obtain ⟨r,hr,hra,hr0,_⟩ := hz
  exact (dirichlet_mass_energy_unique hS b Y Z U g hT hwY hwZ q r hq hr hqa hra
    (hq0.trans hr0.symm)).1

theorem FiniteDirichletControlIdentity.unique_energy_solution
    {d : ℕ} {S : Set (SpatialCoordinates d)} {T : ℝ}
    (hTpos : 0 < T) (hS : IsOpen S) [IsFiniteMeasure (volume.restrict S)]
    {b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S))}
    {y0 : Lp ℝ 2 (volume.restrict S)}
    {Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T))}
    {U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T))}
    (hid : FiniteDirichletControlIdentity T S b y0 Y U) :
    DirichletEnergySolution T S hS b y0 Y U ∧
      ∀ Z, DirichletEnergySolution T S hS b y0 Z U → Y=Z ∧ DirichletNullControlState T S hS b y0 Z U := by
  have hn := hid.null_control_state hTpos hS
  have hy := hn.energy_solution
  refine ⟨hy,fun Z hz => ?_⟩
  have he := hy.unique hTpos hz
  exact ⟨he,he ▸ hn⟩

end Carleman
