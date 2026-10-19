module

public import Carleman.Spatial.HeatGradientExpression
public import Carleman.Spatial.WeakTrajectoryHeatEnergies

/-! Exact identification of the transfer energies with the original weak heat energies. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hd : 0 < d)
  (hb : Bornology.IsBounded S)
  {X F Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [AddCommGroup F] [Module ℝ F] [AddCommGroup Y] [Module ℝ Y]
  (w : TimeWeight) (ρ : SpatialProfile (volume.restrict S))
  (W : Set (SpatialCoordinates d)) (hW : MeasurableSet W)
  (state : ℝ → Seminorm ℝ X) (load : ℝ → Seminorm ℝ F) (control : ℝ → Seminorm ℝ Y)
  (hstate : ∀ t v, state t v = 0 → v = 0)
  (hload : ∀ t v, load t v = 0 → v = 0)
  (hcontrol : ∀ t v, control t v = 0 → v = 0)

local notation "B" => boundedDirichletOriginalForm hS hd hb
set_option quotPrecheck false in
local notation "p" => sobolevGeometry (a := CarlemanExponents.heat) hS
  (ae_restrict_mem hS.measurableSet) (boundedDirichletOriginalForm hS hd hb).sobolev
  w ρ heatDifferentialFamily W hW
  state load control hstate hload hcontrol

theorem dirichletHeatGeometry_energy (g : TimeGrid)
    (u : PeriodicWeakTrajectory g (B).model.domain (B).model.operator) :
    (p).continuousEnergy g ((p).trajectory g (B).domain_le u) =
      timeSq g w.q 3 (fun t => (ρ.expMultiplier (w.q t)).seminorm) u.value+
        timeSq g w.q 1 (fun t => (ρ.expMultiplier (w.q t)).seminorm)
          (fun t => WeakSobolevJet.field 1 (dirichletDomainJet hS hd hb (u.domainValue t))) := by
  unfold TransferGeometry.continuousEnergy
  simp only [CarlemanExponents.heat, Fin.sum_univ_one]
  apply congrArg₂ (fun x y : ℝ => x+y)
  · change timeSq g w.q 3 (fun t => (ρ.multiplier w 0 t).seminorm)
      (fun t => (u.domainValue t : Lp ℝ 2 (volume.restrict S))) = _
    rw [timeSq_congr_ae g w.q 3 _ u.domainValue_ae]
    exact ρ.timeSq_eq_exp_of_eqOn g w w.q (fun _ _ => rfl) 3 u.value
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by
      change w.q t ^ (1:ℝ) *
        ((ρ.multiplier w 0 t).seminorm (conformingExpression (a := CarlemanExponents.heat)
          hS (ae_restrict_mem hS.measurableSet) (B).sobolev (0 : Fin 1) (heatDifferentialFamily 0)
          ((B).model.domain.inclusion (B).domain_le (u.domainValue t))))^2 = _
      rw [conforming_heat_expression,dirichlet_conforming_gradient,
        ρ.zero_multiplier_seminorm_eq_exp]
      rfl

theorem dirichletHeatGeometry_residual (g : TimeGrid) (ε : ℝ)
    (u : PeriodicWeakTrajectory g (B).model.domain (B).model.operator) :
    timeSq g w.q 0 (p).space (fun t => ε • u.derivative t+(B).model.operator (u.domainValue t)) =
      timeSq g w.q 0 (fun t => (ρ.expMultiplier (w.q t)).seminorm)
        (fun t => ε • u.derivative t+(B).model.operator (u.domainValue t)) :=
  ρ.timeSq_eq_exp_of_eqOn g w w.q (fun _ _ => rfl) 0 _

theorem dirichletHeatGeometry_observation (g : TimeGrid)
    (u : PeriodicWeakTrajectory g (B).model.domain (B).model.operator) :
    timeSq g w.q CarlemanExponents.heat.o (p).observation
        (fun t => (u.domainValue t : Lp ℝ 2 (volume.restrict S))) =
      timeSq g w.q 3 (fun t => (ρ.expMultiplier (w.q t)).seminorm)
        (fun t => (BoundedMultiplier.cutoff W hW).map (u.value t)) := by
  change timeSq g w.q 3 (fun t => (ρ.multiplier w 0 t).seminorm)
    (fun t => (BoundedMultiplier.cutoff W hW).map (u.domainValue t : Lp ℝ 2 (volume.restrict S))) = _
  have he : (fun t => (BoundedMultiplier.cutoff W hW).map
      (u.domainValue t : Lp ℝ 2 (volume.restrict S))) =ᵐ[g.timeMeasure]
      (fun t => (BoundedMultiplier.cutoff W hW).map (u.value t)) := by
    filter_upwards [u.domainValue_ae] with t ht
    rw [ht]
  rw [timeSq_congr_ae g w.q 3 _ he]
  exact ρ.timeSq_eq_exp_of_eqOn g w w.q (fun _ _ => rfl) 3 _

end Carleman
