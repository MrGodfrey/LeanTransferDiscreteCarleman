module

public import Carleman.Transfer.DirichletHeatGeometry
public import Carleman.Spatial.BoxOriginalWeakHeat
public import Carleman.Weights.IntervalQClass

/-! The box theorem discharges the actual continuous hypothesis of the original transfer interface. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory Set
universe u v y
namespace Carleman
variable {d : ℕ}

theorem box_heat_continuous_data (lo hi : Fin (d+1) → ℝ) (hpos : ∀ i, lo i < hi i)
    {W : Set (SpatialCoordinates (d+1))} (hW : IsOpen W) (hne : W.Nonempty)
    (hWS : W ⊆ openCoordinateBox lo hi) :
    ∃ (c : SpatialCoordinates (d+1)) (l β qc C : ℝ), c ∈ W ∧ ∃ hl : 1 ≤ l,
      0 < β ∧ β ≤ 1 ∧ 1 ≤ qc ∧ 0 < C ∧
      (∀ x, -2 < interiorCarlemanProfile c l x ∧ interiorCarlemanProfile c l x ≤ -1) ∧
      let B := boundedDirichletOriginalForm (openCoordinateBox_isOpen lo hi) (Nat.zero_lt_succ d)
        (openCoordinateBox_isBounded lo hi)
      let ρ := interiorSpatialProfile (volume.restrict (openCoordinateBox lo hi)) c (zero_le_one.trans hl)
      ∀ (X : Type u) [NormedAddCommGroup X] [InnerProductSpace ℝ X]
        (F : Type v) [AddCommGroup F] [Module ℝ F]
        (Y : Type y) [AddCommGroup Y] [Module ℝ Y]
        (state : ℝ → Seminorm ℝ X) (load : ℝ → Seminorm ℝ F) (control : ℝ → Seminorm ℝ Y)
        (hstate : ∀ t z, state t z = 0 → z = 0)
        (hload : ∀ t z, load t z = 0 → z = 0)
        (hcontrol : ∀ t z, control t z = 0 → z = 0)
        (g : TimeGrid) (w : TimeWeight), IntervalQClass w.q g.period β qc →
      let p := sobolevGeometry (a := CarlemanExponents.heat) (openCoordinateBox_isOpen lo hi)
        (ae_restrict_mem (openCoordinateBox_isOpen lo hi).measurableSet) B.sobolev w ρ
        heatDifferentialFamily W hW.measurableSet state load control hstate hload hcontrol
      ∀ (s : Orientation) (U : PeriodicWeakTrajectory g B.model.domain B.model.operator),
        p.continuousEnergy g (p.trajectory g B.domain_le U) ≤ C *
          (timeSq g w.q 0 p.space (fun t => s.sign • U.derivative t+B.model.operator (U.domainValue t))+
            timeSq g w.q CarlemanExponents.heat.o p.observation
              (fun t => (U.domainValue t : Lp ℝ 2 (volume.restrict (openCoordinateBox lo hi))))) := by
  obtain ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,hce⟩ :=
    box_original_weak_C2_heat_both_signs lo hi hpos hW hne hWS
  refine ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,?_⟩
  dsimp only
  intro X _ _ F _ _ Y _ _ state load control hstate hload hcontrol g w hq s U
  let ρ := interiorSpatialProfile (volume.restrict (openCoordinateBox lo hi)) c (zero_le_one.trans hl)
  have hL := dirichletHeatGeometry_energy (openCoordinateBox_isOpen lo hi)
    (Nat.zero_lt_succ d) (openCoordinateBox_isBounded lo hi) w ρ W hW.measurableSet
    state load control hstate hload hcontrol g U
  have hR := dirichletHeatGeometry_residual (openCoordinateBox_isOpen lo hi)
    (Nat.zero_lt_succ d) (openCoordinateBox_isBounded lo hi) w ρ W hW.measurableSet
    state load control hstate hload hcontrol g s.sign U
  have hO := dirichletHeatGeometry_observation (openCoordinateBox_isOpen lo hi)
    (Nat.zero_lt_succ d) (openCoordinateBox_isBounded lo hi) w ρ W hW.measurableSet
    state load control hstate hload hcontrol g U
  have hh := hce g w.q hq.smooth hq.endpoint hq.first_endpoint hq.second_endpoint hq.lower
    hq.first_bound hq.second_bound s.sign (by cases s <;> simp [Orientation.sign]) U
  exact hL.trans_le (hh.trans_eq (congrArg (fun z : ℝ => C*z)
    (congrArg₂ (fun x y : ℝ => x+y) hR hO).symm))

end Carleman
