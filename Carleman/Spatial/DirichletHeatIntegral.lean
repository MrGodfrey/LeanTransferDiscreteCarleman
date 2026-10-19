module

public import Carleman.Spatial.BochnerBoxIntegral
public import Carleman.Spatial.PeriodicClassicalRepresentatives

/-! The same smooth representative identifies all four actual heat energies with manuscript integrals. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped ContDiff
namespace Carleman
variable {d : ℕ}

theorem smooth_spatial_gradient_sq_continuous {F : (ℝ × SpatialCoordinates d) → ℝ}
    (hF : ContDiff ℝ ∞ F) :
    Continuous (fun tx : ℝ × SpatialCoordinates d => ‖gradient (fun y => F (tx.1,y)) tx.2‖^2) := by
  have he : (fun tx : ℝ × SpatialCoordinates d => ‖gradient (fun y => F (tx.1,y)) tx.2‖^2)=
      directionalEnergy spaceTimeSpatialDirection F :=
    funext fun tx => (spaceTime_directionalEnergy_gradient hF tx.1 tx.2).symm
  rw [he]
  exact (directionalEnergy_contDiff _ hF).continuous

theorem smooth_oriented_heat_continuous (ε : ℝ) {F : (ℝ × SpatialCoordinates d) → ℝ}
    (hF : ContDiff ℝ ∞ F) : Continuous (spaceTimeOrientedHeat ε F) := by
  have he : spaceTimeOrientedHeat ε F=(fun tx => ε*smoothD (1,0) F tx-
      directionalLap spaceTimeSpatialDirection F tx) := by
    funext tx
    rw [spaceTime_timeD hF tx.1 tx.2,spaceTime_directionalLap hF tx.1 tx.2]
    rfl
  rw [he]
  exact (continuous_const.mul (smoothD_contDiff hF _).continuous).sub (directionalLap_contDiff _ hF).continuous

variable (a b : Fin d → ℝ) (hd : 0 < d) (g : TimeGrid)
  (ρ : SpatialProfile (volume.restrict (openCoordinateBox a b))) (w : TimeWeight)
  (hq : ContinuousOn w.q (Icc 0 g.period)) (hρ : Continuous ρ.value)
  (p : (boundedDirichletOriginalForm (openCoordinateBox_isOpen a b) hd
    (openCoordinateBox_isBounded a b)).model.PeriodicGraph g)
  {F : (ℝ × SpatialCoordinates d) → ℝ} (hF : ContDiff ℝ ∞ F)
  (htrace : ∀ t : Icc 0 g.period,
    p.val.1 t =ᵐ[volume.restrict (openCoordinateBox a b)] (fun x => F (t,x)))

include hq hρ hF htrace in
theorem dirichletHeatLeft_eq_boxIntegral :
    dirichletHeatLeft (openCoordinateBox_isOpen a b) hd (openCoordinateBox_isBounded a b) g ρ w p =
      boxTimeIntegral a b g.period (fun tx =>
        (w.q tx.1)^3*(Real.exp (ρ.value tx.2*w.q tx.1))^2*(F tx)^2)+
      boxTimeIntegral a b g.period (fun tx =>
        w.q tx.1*(Real.exp (ρ.value tx.2*w.q tx.1))^2*‖gradient (fun y => F (tx.1,y)) tx.2‖^2) := by
  have hv := periodicGraph_value_classical_ae (openCoordinateBox_isOpen a b) hd
    (openCoordinateBox_isBounded a b) g p htrace
  have hzero := timeSq_eq_boxTimeIntegral_of_continuous a b g ρ w 3 hq hρ
    (g.pathL2 p.val.1) (hF.continuous.pow 2) (by
      filter_upwards [hv] with t ht
      filter_upwards [ht] with x hx
      simp only [hx,Real.norm_eq_abs,sq_abs,Pi.pow_apply])
  have hgrad := timeSq_eq_boxTimeIntegral_of_continuous a b g ρ w 1 hq hρ
    (dirichletPeriodicGradient (openCoordinateBox_isOpen a b) hd (openCoordinateBox_isBounded a b) g p)
    (smooth_spatial_gradient_sq_continuous hF)
    (dirichletPeriodicGradient_smooth_norm (openCoordinateBox_isOpen a b) hd
      (openCoordinateBox_isBounded a b) g p hF htrace)
  unfold dirichletHeatLeft
  simpa only [Nat.cast_ofNat,Nat.cast_one,pow_one,Pi.pow_apply] using congrArg₂ (fun x y : ℝ => x+y) hzero hgrad

include hq hρ hF htrace in
theorem dirichletHeatRight_eq_boxIntegral (ε : ℝ) (W : Set (SpatialCoordinates d)) (hW : MeasurableSet W)
    (hfields : ∀ᵐ t ∂g.timeMeasure,
      (p.val.2.1 t =ᵐ[volume.restrict (openCoordinateBox a b)] (fun x => smoothD (1,0) F (t,x))) ∧
      (p.val.2.2 t =ᵐ[volume.restrict (openCoordinateBox a b)]
        (fun x => -directionalLap spaceTimeSpatialDirection F (t,x)))) :
    dirichletHeatRight (openCoordinateBox_isOpen a b) hd (openCoordinateBox_isBounded a b)
      g ρ w ε W hW p =
      boxTimeIntegral a b g.period (fun tx =>
        (Real.exp (ρ.value tx.2*w.q tx.1)*spaceTimeOrientedHeat ε F tx)^2)+
      boxTimeIntegral a b g.period ((Prod.snd ⁻¹' W).indicator (fun tx =>
        (w.q tx.1)^3*(Real.exp (ρ.value tx.2*w.q tx.1))^2*(F tx)^2)) := by
  have hr := periodicGraph_residual_classical_ae (openCoordinateBox_isOpen a b) hd
    (openCoordinateBox_isBounded a b) g p ε hF hfields
  have hres := timeSq_eq_boxTimeIntegral_of_continuous a b g ρ w 0 hq hρ
    (ε • p.val.2.1+p.val.2.2) ((smooth_oriented_heat_continuous ε hF).pow 2) (by
      filter_upwards [hr] with t ht
      filter_upwards [ht] with x hx
      simp only [hx,Real.norm_eq_abs,sq_abs,Pi.pow_apply])
  have ho := periodicGraph_observation_classical_ae (openCoordinateBox_isOpen a b) hd
    (openCoordinateBox_isBounded a b) g p W hW htrace
  have hobs := timeSq_eq_boxTimeIntegral_of_indicator a b g ρ w 3 hq hρ W hW
    ((BoundedMultiplier.cutoff W hW).continuousLinearMap.compLp (g.pathL2 p.val.1))
    (hF.continuous.pow 2) (by
      filter_upwards [ho] with t ht
      filter_upwards [ht] with x hx
      rw [hx]
      by_cases hw : x ∈ W <;> simp [hw,Real.norm_eq_abs,sq_abs])
  unfold dirichletHeatRight
  simpa only [Nat.cast_ofNat,Nat.cast_zero,pow_zero,one_mul,mul_pow,Pi.pow_apply] using
    congrArg₂ (fun x y : ℝ => x+y) hres hobs

end Carleman
