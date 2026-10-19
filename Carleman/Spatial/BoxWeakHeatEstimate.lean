module

public import Carleman.Spatial.DirichletHeatIntegral
public import Carleman.Spatial.BoxIntervalC2HeatEstimate

/-! The actual two-sign weighted heat estimate on the full weak periodic Dirichlet graph of a box. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped ContDiff
namespace Carleman
variable {d : ℕ}

theorem box_weak_C2_gaussian_heat_both_signs (a b : Fin (d+1) → ℝ) (hpos : ∀ i, a i < b i)
    {W : Set (SpatialCoordinates (d+1))} (hW : IsOpen W) (hne : W.Nonempty)
    (hWS : W ⊆ openCoordinateBox a b) :
    ∃ (c : SpatialCoordinates (d+1)) (l β qc C : ℝ), c ∈ W ∧ ∃ hl : 1 ≤ l,
      0 < β ∧ β ≤ 1 ∧ 1 ≤ qc ∧ 0 < C ∧
      (∀ x, -2 < interiorCarlemanProfile c l x ∧ interiorCarlemanProfile c l x ≤ -1) ∧
      ∀ (g : TimeGrid) (w : TimeWeight), ContDiffOn ℝ 2 w.q (Icc 0 g.period) →
      w.q 0=w.q g.period →
      derivWithin w.q (Icc 0 g.period) 0=derivWithin w.q (Icc 0 g.period) g.period →
      derivWithin (derivWithin w.q (Icc 0 g.period)) (Icc 0 g.period) 0=
        derivWithin (derivWithin w.q (Icc 0 g.period)) (Icc 0 g.period) g.period →
      (∀ t ∈ Icc 0 g.period, qc ≤ w.q t) →
      (∀ t ∈ Icc 0 g.period, |derivWithin w.q (Icc 0 g.period) t| ≤ β*(w.q t)^2) →
      (∀ t ∈ Icc 0 g.period,
        |derivWithin (derivWithin w.q (Icc 0 g.period)) (Icc 0 g.period) t| ≤ β^2*(w.q t)^3) →
      ∀ ε : ℝ, (ε=1 ∨ ε=-1) →
      let ρ := interiorSpatialProfile (volume.restrict (openCoordinateBox a b)) c (zero_le_one.trans hl)
      ∀ p : (boundedDirichletOriginalForm (openCoordinateBox_isOpen a b) (Nat.zero_lt_succ d)
          (openCoordinateBox_isBounded a b)).model.PeriodicGraph g,
        dirichletHeatLeft (openCoordinateBox_isOpen a b) (Nat.zero_lt_succ d)
          (openCoordinateBox_isBounded a b) g ρ w p ≤
        C*dirichletHeatRight (openCoordinateBox_isOpen a b) (Nat.zero_lt_succ d)
          (openCoordinateBox_isBounded a b) g ρ w ε W hW.measurableSet p := by
  obtain ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,hsmooth⟩ :=
    box_interval_C2_gaussian_heat_both_signs a b hpos hW hne hWS
  refine ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,?_⟩
  intro g w hq he0 he1 he2 hqmin hq1 hq2 ε hε
  let ρ := interiorSpatialProfile (volume.restrict (openCoordinateBox a b)) c (zero_le_one.trans hl)
  have hm : AEStronglyMeasurable w.q g.timeMeasure := by
    simpa only [TimeGrid.timeMeasure,restrict_Ioo_eq_restrict_Icc] using
      hq.continuousOn.aestronglyMeasurable measurableSet_Icc
  apply box_dirichletHeat_le_of_classical (hd := Nat.zero_lt_succ d) (g := g) (w := w)
    a b hpos ρ hm ε C W hW.measurableSet
  intro p hp
  obtain ⟨F,hF,hFp,hFb,hFt,hFd⟩ := hp
  have hleft := dirichletHeatLeft_eq_boxIntegral a b (Nat.zero_lt_succ d) g ρ w
    hq.continuousOn (interiorCarlemanProfile_contDiff c l).continuous p hF hFt
  have hright := dirichletHeatRight_eq_boxIntegral a b (Nat.zero_lt_succ d) g ρ w
    hq.continuousOn (interiorCarlemanProfile_contDiff c l).continuous p hF hFt ε W hW.measurableSet hFd
  rw [hleft,hright]
  have hh := hsmooth g.period g.period_pos w.q hq he0 he1 he2 hqmin hq1 hq2 ε hε F hF hFp hFb
  simpa only [ρ,interiorSpatialProfile,interiorGaussianHeatPhase,separableHeatPhase,mul_comm] using hh

end Carleman
