module

public import Carleman.Control.PivotWeakEnergyIdentity
public import Carleman.Control.DirichletTimeEndpoints

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

set_option backward.isDefEq.respectTransparency true in
theorem FiniteDirichletControlIdentity.energy_identity
    {d : ℕ} {S : Set (SpatialCoordinates d)} {T : ℝ}
    (hTpos : 0 < T) (hS : IsOpen S) [IsFiniteMeasure (volume.restrict S)]
    {b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S))}
    {y0 : Lp ℝ 2 (volume.restrict S)}
    {Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T))}
    {U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T))}
    (hid : FiniteDirichletControlIdentity T S b y0 Y U)
    (q : ℝ → Lp ℝ 2 (volume.restrict S)) (hc : ContinuousOn q (Icc 0 T))
    (hq : q =ᵐ[volume.restrict (Ioc 0 T)] (fun t => dirichletStateValue S (Y t))) :
    ∀ t ∈ Icc 0 T,
      ‖q t‖^2-‖q 0‖^2=2*(∫ s in 0..t, inner ℝ (Y s) (dirichletTimeLoad T hS b Y U s)) := by
  let := dirichletEnergyState_complete hS
  let g : TimeGrid := ⟨1,by decide,T,hTpos⟩
  have hT : g.period=T := by simp [g,TimeGrid.period]
  have hμ : g.timeMeasure=volume.restrict (Ioc 0 T) := by
    rw [TimeGrid.timeMeasure,hT,restrict_Ioo_eq_restrict_Ioc]
  have hE : Function.Injective (dirichletStateValue S) :=
    conformingEmbed_injective (dirichletSubspace S) hS (ae_restrict_mem hS.measurableSet)
  have he := pivot_time_energy_identity (V := DirichletEnergyState S) hμ
    (dirichletStateValue S) hE Y (dirichletTimeLoad T hS b Y U)
    (hid.mass_weak_time_derivative hS g hT) q (by rwa [hT]) hq
  simpa only [hT] using he

theorem FiniteDirichletControlIdentity.continuous_H_energy_trace
    {d : ℕ} {S : Set (SpatialCoordinates d)} {T : ℝ}
    (hTpos : 0 < T) (hS : IsOpen S) [IsFiniteMeasure (volume.restrict S)]
    {b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S))}
    {y0 : Lp ℝ 2 (volume.restrict S)}
    {Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T))}
    {U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T))}
    (hid : FiniteDirichletControlIdentity T S b y0 Y U) :
    ∃ q : ℝ → Lp ℝ 2 (volume.restrict S), ContinuousOn q (Icc 0 T) ∧
      q =ᵐ[volume.restrict (Ioc 0 T)] (fun t => dirichletStateValue S (Y t)) ∧
      q 0=y0 ∧ q T=0 ∧ ∀ t ∈ Icc 0 T,
        ‖q t‖^2-‖y0‖^2=2*(∫ s in 0..t, inner ℝ (Y s) (dirichletTimeLoad T hS b Y U s)) := by
  obtain ⟨q,hc,hq,hzero,hend⟩ := hid.continuous_H_trace hTpos hS
  refine ⟨q,hc,hq,hzero,hend,?_⟩
  simpa only [hzero] using hid.energy_identity hTpos hS q hc hq


end Carleman
