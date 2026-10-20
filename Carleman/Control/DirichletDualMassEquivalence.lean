module

public import Carleman.Control.WeakDerivativeInjection
public import Carleman.Control.DirichletDualTimeDerivative

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman

theorem dirichlet_dual_mass_weak_iff
    {d : ℕ} {S : Set (SpatialCoordinates d)} {T : ℝ} (hS : IsOpen S)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S)))
    (Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T)))
    (U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T)))
    (g : TimeGrid) (hT : g.period=T) :
    (∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo 0 T →
      (∫ t, deriv φ t • dirichletPivotDual S hS (Y t) ∂(volume.restrict (Ioc 0 T)))=
        -(∫ t, φ t • dirichletDualTimeLoad T hS b Y U t ∂(volume.restrict (Ioc 0 T)))) ↔
    HasWeakTimeDerivative g ((dirichletTimeMass S hS).compLpL 2 (volume.restrict (Ioc 0 T)) Y)
      (dirichletTimeLoad T hS b Y U) := by
  let := dirichletEnergyState_complete hS
  have hμ : g.timeMeasure=volume.restrict (Ioc 0 T) := by
    rw [TimeGrid.timeMeasure,hT,restrict_Ioo_eq_restrict_Ioc]
  let L : DirichletEnergyState S →L[ℝ] StrongDual ℝ (DirichletEnergyState S) := innerSL ℝ
  let mY := (dirichletTimeMass S hS).compLpL 2 (volume.restrict (Ioc 0 T)) Y
  let D := dirichletTimeLoad T hS b Y U
  have hm : MemLp mY 2 g.timeMeasure := by rw [hμ]; exact Lp.memLp mY
  have hd : MemLp D 2 g.timeMeasure := by rw [hμ]; exact Lp.memLp D
  have he₁ (φ : ℝ → ℝ) : (∫ t, deriv φ t • L (mY t) ∂g.timeMeasure)=
      ∫ t, deriv φ t • dirichletPivotDual S hS (Y t) ∂(volume.restrict (Ioc 0 T)) := by
    rw [hμ]
    apply integral_congr_ae
    filter_upwards [(dirichletTimeMass S hS).coeFn_compLpL Y] with t ht
    change mY t=dirichletTimeMass S hS (Y t) at ht
    rw [ht]
    rfl
  have he₂ (φ : ℝ → ℝ) : (∫ t, φ t • L (D t) ∂g.timeMeasure)=
      ∫ t, φ t • dirichletDualTimeLoad T hS b Y U t ∂(volume.restrict (Ioc 0 T)) := by
    rw [hμ]
    apply integral_congr_ae
    filter_upwards [L.coeFn_compLpL D] with t ht
    change dirichletDualTimeLoad T hS b Y U t=L (D t) at ht
    rw [ht]
  constructor
  · intro hw
    apply HasWeakTimeDerivative.of_injective_map_integral hm hd L
      (InnerProductSpace.toDualMap ℝ (DirichletEnergyState S)).injective
    intro φ hφ hc hs
    rw [he₁,he₂]
    exact hw φ hφ hc (by simpa only [hT] using hs)
  · intro hw φ hφ hc hs
    rw [← he₁,← he₂]
    exact hw.map_integral hm hd L φ hφ hc (by simpa only [hT] using hs)

theorem dirichlet_dual_energy_memLp
    {d : ℕ} {S : Set (SpatialCoordinates d)} (T : ℝ) (hS : IsOpen S)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S)))
    (Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T)))
    (U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T))) :
    MemLp (fun t => dirichletPivotDual S hS (Y t)) 2 (volume.restrict (Ioc 0 T)) ∧
    MemLp (dirichletDualTimeLoad T hS b Y U) 2 (volume.restrict (Ioc 0 T)) := by
  exact ⟨(Lp.memLp ((dirichletPivotDual S hS).compLpL 2 (volume.restrict (Ioc 0 T)) Y)).ae_eq
    ((dirichletPivotDual S hS).coeFn_compLpL Y),Lp.memLp _⟩

end Carleman
