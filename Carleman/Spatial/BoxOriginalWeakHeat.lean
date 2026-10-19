module

public import Carleman.Spatial.BoxIntervalWeakHeat
public import Carleman.Spatial.WeakTrajectoryHeatEnergies

/-! The box estimate stated directly for every original weak trajectory and original C² interval weight. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory Set
open scoped ContDiff
namespace Carleman
variable {d : ℕ}

theorem box_original_weak_C2_heat_both_signs (a b : Fin (d+1) → ℝ) (hpos : ∀ i, a i < b i)
    {W : Set (SpatialCoordinates (d+1))} (hW : IsOpen W) (hne : W.Nonempty)
    (hWS : W ⊆ openCoordinateBox a b) :
    ∃ (c : SpatialCoordinates (d+1)) (l β qc C : ℝ), c ∈ W ∧ ∃ hl : 1 ≤ l,
      0 < β ∧ β ≤ 1 ∧ 1 ≤ qc ∧ 0 < C ∧
      (∀ x, -2 < interiorCarlemanProfile c l x ∧ interiorCarlemanProfile c l x ≤ -1) ∧
      ∀ (g : TimeGrid) (q : ℝ → ℝ), ContDiffOn ℝ 2 q (Icc 0 g.period) →
      q 0=q g.period →
      derivWithin q (Icc 0 g.period) 0=derivWithin q (Icc 0 g.period) g.period →
      derivWithin (derivWithin q (Icc 0 g.period)) (Icc 0 g.period) 0=
        derivWithin (derivWithin q (Icc 0 g.period)) (Icc 0 g.period) g.period →
      (∀ t ∈ Icc 0 g.period, qc ≤ q t) →
      (∀ t ∈ Icc 0 g.period, |derivWithin q (Icc 0 g.period) t| ≤ β*(q t)^2) →
      (∀ t ∈ Icc 0 g.period,
        |derivWithin (derivWithin q (Icc 0 g.period)) (Icc 0 g.period) t| ≤ β^2*(q t)^3) →
      ∀ ε : ℝ, (ε=1 ∨ ε=-1) →
      let B := (boundedDirichletOriginalForm (openCoordinateBox_isOpen a b) (Nat.zero_lt_succ d)
        (openCoordinateBox_isBounded a b)).model
      let ρ := interiorSpatialProfile (volume.restrict (openCoordinateBox a b)) c (zero_le_one.trans hl)
      ∀ u : PeriodicWeakTrajectory g B.domain B.operator,
        timeSq g q 3 (fun t => (ρ.expMultiplier (q t)).seminorm) u.value+
          timeSq g q 1 (fun t => (ρ.expMultiplier (q t)).seminorm)
            (fun t => WeakSobolevJet.field 1 (dirichletDomainJet (openCoordinateBox_isOpen a b)
              (Nat.zero_lt_succ d) (openCoordinateBox_isBounded a b) (u.domainValue t))) ≤
        C*(timeSq g q 0 (fun t => (ρ.expMultiplier (q t)).seminorm)
            (fun t => ε • u.derivative t+B.operator (u.domainValue t))+
          timeSq g q 3 (fun t => (ρ.expMultiplier (q t)).seminorm)
            (fun t => (BoundedMultiplier.cutoff W hW.measurableSet).map (u.value t))) := by
  obtain ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,hweak⟩ :=
    box_weak_interval_C2_gaussian_heat_both_signs a b hpos hW hne hWS
  refine ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,?_⟩
  intro g q hq he0 he1 he2 hqmin hq1 hq2 ε hε
  dsimp only
  intro u
  have hh := hweak g q hq he0 he1 he2 hqmin hq1 hq2 ε hε u.toPeriodicGraph
  rw [dirichletIntervalHeatLeft_trajectory,dirichletIntervalHeatRight_trajectory] at hh
  exact hh

end Carleman
