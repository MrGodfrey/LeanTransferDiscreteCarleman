module

public import Carleman.Spatial.BoxWeakHeatEstimate
public import Carleman.Spatial.IntervalHeatEnergies

/-! Full original closed-interval C² weights in the weak box estimate, with no extension input. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped ContDiff
namespace Carleman
variable {d : ℕ}

theorem box_weak_interval_C2_gaussian_heat_both_signs (a b : Fin (d+1) → ℝ) (hpos : ∀ i, a i < b i)
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
      let ρ := interiorSpatialProfile (volume.restrict (openCoordinateBox a b)) c (zero_le_one.trans hl)
      ∀ p : (boundedDirichletOriginalForm (openCoordinateBox_isOpen a b) (Nat.zero_lt_succ d)
          (openCoordinateBox_isBounded a b)).model.PeriodicGraph g,
        dirichletIntervalHeatLeft (openCoordinateBox_isOpen a b) (Nat.zero_lt_succ d)
          (openCoordinateBox_isBounded a b) g ρ q p ≤
        C*dirichletIntervalHeatRight (openCoordinateBox_isOpen a b) (Nat.zero_lt_succ d)
          (openCoordinateBox_isBounded a b) g ρ q ε W hW.measurableSet p := by
  obtain ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,hweak⟩ :=
    box_weak_C2_gaussian_heat_both_signs a b hpos hW hne hWS
  refine ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,?_⟩
  intro g q hq he0 he1 he2 hqmin hq1 hq2 ε hε
  dsimp only
  obtain ⟨w,_hwcont,he⟩ := exists_timeWeight_eqOn_interval g hq.continuousOn
    (fun t ht => hqc.trans (hqmin t ht))
  have hd := eqOn_interval_within_derivatives he
  have h0 : (0:ℝ) ∈ Icc 0 g.period := ⟨le_rfl,g.period_pos.le⟩
  have hT : g.period ∈ Icc 0 g.period := ⟨g.period_pos.le,le_rfl⟩
  have hw0 : w.q 0=w.q g.period := by rw [he h0,he hT,he0]
  have hw1 : derivWithin w.q (Icc 0 g.period) 0=derivWithin w.q (Icc 0 g.period) g.period := by
    rw [(hd 0 h0).2.1,(hd g.period hT).2.1,he1]
  have hw2 : derivWithin (derivWithin w.q (Icc 0 g.period)) (Icc 0 g.period) 0=
      derivWithin (derivWithin w.q (Icc 0 g.period)) (Icc 0 g.period) g.period := by
    rw [(hd 0 h0).2.2,(hd g.period hT).2.2,he2]
  have hwmin : ∀ t ∈ Icc 0 g.period, qc ≤ w.q t := fun t ht => by rw [he ht]; exact hqmin t ht
  have hwd1 : ∀ t ∈ Icc 0 g.period, |derivWithin w.q (Icc 0 g.period) t| ≤ β*(w.q t)^2 := by
    intro t ht
    rw [(hd t ht).2.1,he ht]
    exact hq1 t ht
  have hwd2 : ∀ t ∈ Icc 0 g.period,
      |derivWithin (derivWithin w.q (Icc 0 g.period)) (Icc 0 g.period) t| ≤ β^2*(w.q t)^3 := by
    intro t ht
    rw [(hd t ht).2.2,he ht]
    exact hq2 t ht
  let ρ := interiorSpatialProfile (volume.restrict (openCoordinateBox a b)) c (zero_le_one.trans hl)
  intro p
  have hh := hweak g w (hq.congr he) hw0 hw1 hw2 hwmin hwd1 hwd2 ε hε p
  change dirichletHeatLeft (openCoordinateBox_isOpen a b) (Nat.zero_lt_succ d)
    (openCoordinateBox_isBounded a b) g ρ w p ≤
    C*dirichletHeatRight (openCoordinateBox_isOpen a b) (Nat.zero_lt_succ d)
      (openCoordinateBox_isBounded a b) g ρ w ε W hW.measurableSet p at hh
  rw [dirichletHeatLeft_eq_interval _ _ _ _ _ q w he,
    dirichletHeatRight_eq_interval _ _ _ _ _ q w he] at hh
  exact hh

end Carleman
