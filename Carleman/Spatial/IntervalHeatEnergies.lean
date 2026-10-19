module

public import Carleman.Spatial.DirichletHeatContinuity
public import Carleman.Weights.IntervalTimeWeight

/-! The actual heat energies for an arbitrary original interval function q, independent of its extension. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
namespace Carleman.SpatialProfile
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ν : Measure Ω} (ρ : SpatialProfile ν)

theorem zero_multiplier_seminorm_eq_exp (w : TimeWeight) (t : ℝ) (u : Lp E 2 ν) :
    (ρ.multiplier w 0 t).seminorm u=(ρ.expMultiplier (w.q t)).seminorm u := by
  change ‖(ρ.multiplier w 0 t).map u‖=‖(ρ.expMultiplier (w.q t)).map u‖
  congr 1
  apply Lp.ext
  filter_upwards [(ρ.multiplier w 0 t).map_ae u,(ρ.expMultiplier (w.q t)).map_ae u] with x hx hy
  rw [hx,hy]
  simp only [multiplier,expMultiplier,Real.rpow_zero,one_mul]

theorem timeSq_eq_exp_of_eqOn (g : TimeGrid) (w : TimeWeight) (q : ℝ → ℝ)
    (he : EqOn w.q q (Icc 0 g.period)) (s : ℝ) (u : ℝ → Lp E 2 ν) :
    timeSq g w.q s (fun t => (ρ.multiplier w 0 t).seminorm) u=
      timeSq g q s (fun t => (ρ.expMultiplier (q t)).seminorm) u := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  unfold timeDensity
  rw [ρ.zero_multiplier_seminorm_eq_exp,he ⟨ht.1.le,ht.2.le⟩]

end Carleman.SpatialProfile

namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hd : 0 < d)
  (hb : Bornology.IsBounded S) (g : TimeGrid) (ρ : SpatialProfile (volume.restrict S))
  (q : ℝ → ℝ)

def dirichletIntervalHeatLeft
    (p : (boundedDirichletOriginalForm hS hd hb).model.PeriodicGraph g) : ℝ :=
  timeSq g q 3 (fun t => (ρ.expMultiplier (q t)).seminorm) (g.pathL2 p.val.1)+
    timeSq g q 1 (fun t => (ρ.expMultiplier (q t)).seminorm) (dirichletPeriodicGradient hS hd hb g p)

def dirichletIntervalHeatRight (ε : ℝ) (W : Set (SpatialCoordinates d)) (hW : MeasurableSet W)
    (p : (boundedDirichletOriginalForm hS hd hb).model.PeriodicGraph g) : ℝ :=
  timeSq g q 0 (fun t => (ρ.expMultiplier (q t)).seminorm) (ε • p.val.2.1+p.val.2.2)+
    timeSq g q 3 (fun t => (ρ.expMultiplier (q t)).seminorm)
      ((BoundedMultiplier.cutoff W hW).continuousLinearMap.compLp (g.pathL2 p.val.1))

theorem dirichletHeatLeft_eq_interval (w : TimeWeight) (he : EqOn w.q q (Icc 0 g.period))
    (p : (boundedDirichletOriginalForm hS hd hb).model.PeriodicGraph g) :
    dirichletHeatLeft hS hd hb g ρ w p=dirichletIntervalHeatLeft hS hd hb g ρ q p := by
  unfold dirichletHeatLeft dirichletIntervalHeatLeft
  rw [ρ.timeSq_eq_exp_of_eqOn g w q he,ρ.timeSq_eq_exp_of_eqOn g w q he]

theorem dirichletHeatRight_eq_interval (w : TimeWeight) (he : EqOn w.q q (Icc 0 g.period))
    (ε : ℝ) (W : Set (SpatialCoordinates d)) (hW : MeasurableSet W)
    (p : (boundedDirichletOriginalForm hS hd hb).model.PeriodicGraph g) :
    dirichletHeatRight hS hd hb g ρ w ε W hW p=
      dirichletIntervalHeatRight hS hd hb g ρ q ε W hW p := by
  unfold dirichletHeatRight dirichletIntervalHeatRight
  rw [ρ.timeSq_eq_exp_of_eqOn g w q he,ρ.timeSq_eq_exp_of_eqOn g w q he]

end Carleman
