module

public import Carleman.Spatial.DirichletPeriodicGradient
public import Carleman.Spatial.WeightedTimeContinuity
public import Carleman.Spatial.BoxClassicalTimeDensity

/-! Continuity of the four genuine weighted heat energies on the full original periodic graph. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hd : 0 < d)
  (hb : Bornology.IsBounded S) (g : TimeGrid) (ρ : SpatialProfile (volume.restrict S))
  (w : TimeWeight)

def dirichletHeatLeft (p : (boundedDirichletOriginalForm hS hd hb).model.PeriodicGraph g) : ℝ :=
  timeSq g w.q 3 (fun t => (ρ.multiplier w 0 t).seminorm) (g.pathL2 p.val.1) +
    timeSq g w.q 1 (fun t => (ρ.multiplier w 0 t).seminorm)
      (dirichletPeriodicGradient hS hd hb g p)

def dirichletHeatRight (ε : ℝ) (W : Set (SpatialCoordinates d)) (hW : MeasurableSet W)
    (p : (boundedDirichletOriginalForm hS hd hb).model.PeriodicGraph g) : ℝ :=
  timeSq g w.q 0 (fun t => (ρ.multiplier w 0 t).seminorm) (ε • p.val.2.1+p.val.2.2) +
    timeSq g w.q 3 (fun t => (ρ.multiplier w 0 t).seminorm)
      ((BoundedMultiplier.cutoff W hW).continuousLinearMap.compLp (g.pathL2 p.val.1))

theorem continuous_dirichletHeatLeft (hq : AEStronglyMeasurable w.q g.timeMeasure) :
    Continuous (dirichletHeatLeft hS hd hb g ρ w) := by
  let B := (boundedDirichletOriginalForm hS hd hb).model
  exact ((ρ.continuous_timeSq g w 0 hq 3).comp
    (g.fieldsValue.comp (B.periodicGraphSubmodule g).subtypeL).continuous).add
      ((ρ.continuous_timeSq g w 0 hq 1).comp (dirichletPeriodicGradient hS hd hb g).continuous)

theorem continuous_dirichletHeatRight (hq : AEStronglyMeasurable w.q g.timeMeasure)
    (ε : ℝ) (W : Set (SpatialCoordinates d)) (hW : MeasurableSet W) :
    Continuous (dirichletHeatRight hS hd hb g ρ w ε W hW) := by
  let B := (boundedDirichletOriginalForm hS hd hb).model
  let v := g.fieldsValue.comp (B.periodicGraphSubmodule g).subtypeL
  let r := (ε • g.fieldsDerivative+g.fieldsOperator).comp (B.periodicGraphSubmodule g).subtypeL
  let o := ((BoundedMultiplier.cutoff W hW).continuousLinearMap.compLpL 2 g.timeMeasure).comp v
  exact ((ρ.continuous_timeSq g w 0 hq 0).comp r.continuous).add
    ((ρ.continuous_timeSq g w 0 hq 3).comp o.continuous)

/-- This transfer lemma leaves the smooth CE premise explicit; it introduces no new constant. -/
theorem box_dirichletHeat_le_of_classical (a b : Fin d → ℝ) (hpos : ∀ i, a i < b i)
    (ρ : SpatialProfile (volume.restrict (openCoordinateBox a b)))
    (hq : AEStronglyMeasurable w.q g.timeMeasure)
    (ε C : ℝ) (W : Set (SpatialCoordinates d)) (hW : MeasurableSet W)
    (hCE : ∀ p ∈ classicalDirichletTimeCore (openCoordinateBox_isOpen a b) hd
        (openCoordinateBox_isBounded a b) g,
      dirichletHeatLeft (openCoordinateBox_isOpen a b) hd (openCoordinateBox_isBounded a b) g ρ w p ≤
        C*dirichletHeatRight (openCoordinateBox_isOpen a b) hd (openCoordinateBox_isBounded a b)
          g ρ w ε W hW p) :
    ∀ p, dirichletHeatLeft (openCoordinateBox_isOpen a b) hd (openCoordinateBox_isBounded a b) g ρ w p ≤
      C*dirichletHeatRight (openCoordinateBox_isOpen a b) hd (openCoordinateBox_isBounded a b)
        g ρ w ε W hW p := by
  intro p
  have hc := isClosed_le
    (continuous_dirichletHeatLeft (openCoordinateBox_isOpen a b) hd (openCoordinateBox_isBounded a b)
      g ρ w hq)
    ((continuous_dirichletHeatRight (openCoordinateBox_isOpen a b) hd (openCoordinateBox_isBounded a b)
      g ρ w hq ε W hW).const_mul C)
  exact (closure_minimal hCE hc) (box_classicalDirichletTimeCore_dense hd a b hpos g p)

end Carleman
