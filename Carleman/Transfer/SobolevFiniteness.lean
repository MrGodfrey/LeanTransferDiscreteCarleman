module

public import Carleman.Continuous.SobolevError
public import Carleman.Transfer.SobolevGeometry

/-! Finiteness in the actual Section 5 geometry, from the original elliptic
regularity bound and a genuine periodic weak trajectory. -/
@[expose] public noncomputable section
open Set MeasureTheory
namespace Carleman
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {a : CarlemanExponents} {V : Submodule ℝ (Lp ℝ 2 ν)}
  (hV : V ≤ sobolevSubspace d a.m ν S)
  {X F Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [AddCommGroup F] [Module ℝ F] [AddCommGroup Y] [Module ℝ Y]
  {Z : Fin a.m → Type*} [∀ j, NormedAddCommGroup (Z j)]
  [∀ j, InnerProductSpace ℝ (Z j)]
  (w : TimeWeight) (ρ : SpatialProfile ν)
  (P : ∀ j : Fin a.m, DifferentialExpression ν
      (fun k : Fin (a.m+1) => DerivativeFiber d k.val) (Z j) (j.val+1))
  (obs : Set (SpatialCoordinates d)) (hobs : MeasurableSet obs)
  (state : ℝ → Seminorm ℝ X) (load : ℝ → Seminorm ℝ F) (control : ℝ → Seminorm ℝ Y)
  (hstate : ∀ t v, state t v = 0 → v = 0)
  (hload : ∀ t v, load t v = 0 → v = 0)
  (hcontrol : ∀ t v, control t v = 0 → v = 0)

local notation "p" => sobolevGeometry hS hν hV w ρ P obs hobs state load control hstate hload hcontrol

variable {g : TimeGrid} (hq : AEStronglyMeasurable w.q g.timeMeasure)

include hq in
theorem sobolevGeometry_value_finite (b : ℝ) {v : ℝ → Lp ℝ 2 ν}
    (hv : MemLp v 2 g.timeMeasure) : TimeSquareIntegrable g w.q b (p).space v :=
  ρ.timeSquareIntegrable_of_memLp g w 0 b hq hv

include hq in
theorem sobolevGeometry_observation_finite (b : ℝ) {v : ℝ → Lp ℝ 2 ν}
    (hv : MemLp v 2 g.timeMeasure) : TimeSquareIntegrable g w.q b (p).observation v := by
  have hc : MemLp (fun t => (BoundedMultiplier.cutoff obs hobs).map (v t)) 2 g.timeMeasure :=
    hv.continuousLinearMap_comp (BoundedMultiplier.cutoff obs hobs).continuousLinearMap
  change TimeSquareIntegrable g w.q b (fun t => (ρ.multiplier w 0 t).seminorm)
    (fun t => (BoundedMultiplier.cutoff obs hobs).map (v t))
  exact ρ.timeSquareIntegrable_of_memLp g w 0 b hq hc

include hq in
theorem sobolevGeometry_derivative_finite (b : ℝ) {v : ℝ → V}
    (hv : MemLp (fun t => domainSobolevJet hS hν hV (v t)) 2 g.timeMeasure)
    (j : Fin a.m) : TimeSquareIntegrable g w.q b ((p).derivative j) v :=
  (P j).timeSquareIntegrable_apply g w ρ 0 b hq _
    (fun k => WeakSobolevJet.memLp_field hv k)

include hq in
theorem sobolevGeometry_gradient_finite (b : ℝ) {v : ℝ → V}
    (hv : MemLp (fun t => domainSobolevJet hS hν hV (v t)) 2 g.timeMeasure)
    (k : Fin (a.m+1)) : TimeSquareIntegrable g w.q b ((p).gradient k) v :=
  WeakSobolevJet.timeSquareIntegrable_field g w ρ 0 b hq hv k

omit w ρ P obs hobs state load control hstate hload hcontrol hq in
theorem conforming_value_L2 {v : ℝ → V}
    (hv : MemLp (fun t => domainSobolevJet hS hν hV (v t)) 2 g.timeMeasure) :
    MemLp (fun t => (v t : Lp ℝ 2 ν)) 2 g.timeMeasure := by
  have hh := hv.continuousLinearMap_comp WeakSobolevJet.valueCLM
  simpa only [WeakSobolevJet.valueCLM_apply, domainSobolevJet_value] using hh

variable {D : Submodule ℝ (Lp ℝ 2 ν)} {A : D →ₗ[ℝ] Lp ℝ 2 ν}
  (hDV : D ≤ V) (u : PeriodicWeakTrajectory g D A)
  (C : ℝ) (hell : ∀ v : D, ‖domainSobolevJet hS hν (hDV.trans hV) v‖ ≤ C*‖A v‖)
  (r : Reconstruction V X) (s : Orientation) (z : g.Sequence X)

include C hell in
theorem sobolevGeometry_trajectory_graph_L2 :
    MemLp (fun t => domainSobolevJet hS hν hV ((p).trajectory g hDV u t)) 2 g.timeMeasure :=
  u.domainSobolev_L2 hS hν (hDV.trans hV) C hell

theorem sobolevGeometry_reconstruction_graph_L2 :
    MemLp (fun t => domainSobolevJet hS hν hV ((p).reconstruction g r s z t)) 2 g.timeMeasure := by
  have he : (fun t => domainSobolevJet hS hν hV ((p).reconstruction g r s z t)) =
      s.extension g (fun i => domainSobolevJet hS hν hV (r.R (z i))) := by cases s <;> rfl
  rw [he]
  exact s.memLp_extension g _

include C hell in
theorem sobolevGeometry_error_graph_L2 :
    MemLp (fun t => domainSobolevJet hS hν hV ((p).error g hDV u r s z t)) 2 g.timeMeasure := by
  have hu := sobolevGeometry_trajectory_graph_L2 hS hν hV w ρ P obs hobs state load control
    hstate hload hcontrol hDV u C hell
  have hv := sobolevGeometry_reconstruction_graph_L2 hS hν hV w ρ P obs hobs state load control
    hstate hload hcontrol r s z
  have he : (fun t => domainSobolevJet hS hν hV ((p).error g hDV u r s z t)) =
      (fun t => domainSobolevJet hS hν hV ((p).trajectory g hDV u t)) -
      (fun t => domainSobolevJet hS hν hV ((p).reconstruction g r s z t)) := by
    funext t
    exact map_sub _ _ _
  rw [he]
  exact hu.sub hv

end Carleman
