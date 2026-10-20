module

public import Carleman.Control.DirichletTimeEndpoints
public import Carleman.Control.DirichletDualTimeDerivative

/-! The same original energy state solves the actual dual equation and has a continuous null-control trace. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Carleman
open scoped ContDiff in
/-- The actual energy state has a closed-interval H trace and solves the original V'-valued null-control equation. -/
def DirichletNullControlState {d : ℕ} (T : ℝ) (S : Set (SpatialCoordinates d))
    (hS : IsOpen S) [IsFiniteMeasure (volume.restrict S)]
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S)))
    (y0 : Lp ℝ 2 (volume.restrict S))
    (Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T)))
    (U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T))) : Prop :=
  ∃ q : ℝ → Lp ℝ 2 (volume.restrict S), ContinuousOn q (Icc 0 T) ∧
    q =ᵐ[volume.restrict (Ioc 0 T)] (fun t => dirichletStateValue S (Y t)) ∧
    q 0=y0 ∧ q T=0 ∧
    ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo 0 T →
      (∫ t, deriv φ t • dirichletPivotDual S hS (Y t) ∂(volume.restrict (Ioc 0 T)))=
        -(∫ t, φ t • dirichletDualTimeLoad T hS b Y U t ∂(volume.restrict (Ioc 0 T)))

theorem FiniteDirichletControlIdentity.null_control_state
    {d : ℕ} {S : Set (SpatialCoordinates d)} {T : ℝ}
    (hTpos : 0 < T) (hS : IsOpen S) [IsFiniteMeasure (volume.restrict S)]
    {b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S))}
    {y0 : Lp ℝ 2 (volume.restrict S)}
    {Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T))}
    {U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T))}
    (hid : FiniteDirichletControlIdentity T S b y0 Y U) :
    DirichletNullControlState T S hS b y0 Y U := by
  obtain ⟨q,hc,hq,h0,hT⟩ := hid.continuous_H_trace hTpos hS
  exact ⟨q,hc,hq,h0,hT,hid.dual_weak_time_derivative hTpos hS⟩

end Carleman
