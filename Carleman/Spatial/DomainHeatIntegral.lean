module

public import Carleman.Spatial.WeightedTimeContinuity
public import Carleman.Spatial.UniformInnerC2Heat
public import Carleman.Spatial.DirichletHeatIntegral

/-! Exact Fubini identification of the original weighted Bochner squares and actual cylinders. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff
namespace Carleman
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (S : Set (SpatialCoordinates d)) (hbounded : Bornology.IsBounded S) (g : TimeGrid) (ρ : SpatialProfile (volume.restrict (S)))
  (w : TimeWeight)

include hbounded in
theorem weighted_domain_density_integrable (n : ℕ)
    (hq : ContinuousOn w.q (Icc 0 g.period)) (hρ : Continuous ρ.value)
    {F : (ℝ × SpatialCoordinates d) → ℝ} (hF : Continuous F) :
    Integrable (fun tx => (w.q tx.1)^n*(Real.exp (ρ.value tx.2*w.q tx.1))^2*F tx)
      ((volume.restrict (Icc 0 g.period)).prod (volume.restrict (S))) := by
  let K := (Icc (0:ℝ) g.period) ×ˢ closure (S)
  have hk : IsCompact K := isCompact_Icc.prod hbounded.isCompact_closure
  have hcq : ContinuousOn (fun tx : ℝ × SpatialCoordinates d => w.q tx.1) K :=
    hq.comp continuous_fst.continuousOn (fun _ hx => hx.1)
  have hce : ContinuousOn (fun tx : ℝ × SpatialCoordinates d =>
      Real.exp (ρ.value tx.2*w.q tx.1)) K :=
    Real.continuous_exp.comp_continuousOn ((hρ.comp continuous_snd).continuousOn.mul hcq)
  have hi := ContinuousOn.integrableOn_compact (μ := volume) hk
    (((hcq.pow n).mul (hce.pow 2)).mul hF.continuousOn)
  rw [Measure.prod_restrict]
  exact hi.mono_set (prod_mono subset_rfl subset_closure)

theorem timeSq_eq_domainTimeIntegral_of_norm_sq (s : ℝ)
    (u : Lp (Lp E 2 (volume.restrict (S))) 2 g.timeMeasure)
    {F : (ℝ × SpatialCoordinates d) → ℝ}
    (hF : ∀ᵐ t ∂g.timeMeasure,
      (fun x => ‖u t x‖^2) =ᵐ[volume.restrict (S)] (fun x => F (t,x)))
    (hi : Integrable (fun tx => (w.q tx.1)^s*(Real.exp (ρ.value tx.2*w.q tx.1))^2*F tx)
      ((volume.restrict (Icc 0 g.period)).prod (volume.restrict (S)))) :
    timeSq g w.q s (fun t => (ρ.multiplier w 0 t).seminorm) u =
      domainTimeIntegral S g.period (fun tx =>
        (w.q tx.1)^s*(Real.exp (ρ.value tx.2*w.q tx.1))^2*F tx) := by
  unfold domainTimeIntegral
  rw [integral_prod _ hi]
  change (∫ t, timeDensity w.q s (fun t => (ρ.multiplier w 0 t).seminorm) u t ∂g.timeMeasure)=_
  have hm : volume.restrict (Icc (0:ℝ) g.period)=g.timeMeasure :=
    (restrict_Ioo_eq_restrict_Icc : volume.restrict (Ioo (0:ℝ) g.period)=_).symm
  rw [hm]
  apply integral_congr_ae
  filter_upwards [hF] with t ht
  unfold timeDensity
  rw [BoundedMultiplier.seminorm_sq_integral,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ht] with x hx
  simp only [SpatialProfile.multiplier,Real.rpow_zero,one_mul,
    abs_of_pos (Real.exp_pos _),hx]
  ring

include hbounded in
theorem timeSq_eq_domainTimeIntegral_of_continuous (n : ℕ)
    (hq : ContinuousOn w.q (Icc 0 g.period)) (hρ : Continuous ρ.value)
    (u : Lp (Lp E 2 (volume.restrict (S))) 2 g.timeMeasure)
    {F : (ℝ × SpatialCoordinates d) → ℝ} (hc : Continuous F)
    (hF : ∀ᵐ t ∂g.timeMeasure,
      (fun x => ‖u t x‖^2) =ᵐ[volume.restrict (S)] (fun x => F (t,x))) :
    timeSq g w.q (n:ℝ) (fun t => (ρ.multiplier w 0 t).seminorm) u =
      domainTimeIntegral S g.period (fun tx =>
        (w.q tx.1)^n*(Real.exp (ρ.value tx.2*w.q tx.1))^2*F tx) := by
  simpa only [Real.rpow_natCast] using timeSq_eq_domainTimeIntegral_of_norm_sq S g ρ w (n:ℝ) u hF
    (by simpa only [Real.rpow_natCast] using weighted_domain_density_integrable S hbounded g ρ w n hq hρ hc)

include hbounded in
theorem timeSq_eq_domainTimeIntegral_of_indicator (n : ℕ)
    (hq : ContinuousOn w.q (Icc 0 g.period)) (hρ : Continuous ρ.value)
    (W : Set (SpatialCoordinates d)) (hW : MeasurableSet W)
    (u : Lp (Lp E 2 (volume.restrict (S))) 2 g.timeMeasure)
    {F : (ℝ × SpatialCoordinates d) → ℝ} (hc : Continuous F)
    (hF : ∀ᵐ t ∂g.timeMeasure,
      (fun x => ‖u t x‖^2) =ᵐ[volume.restrict (S)]
        (fun x => W.indicator (fun y => F (t,y)) x)) :
    timeSq g w.q (n:ℝ) (fun t => (ρ.multiplier w 0 t).seminorm) u =
      domainTimeIntegral S g.period ((Prod.snd ⁻¹' W).indicator (fun tx =>
        (w.q tx.1)^n*(Real.exp (ρ.value tx.2*w.q tx.1))^2*F tx)) := by
  have he : (fun tx : ℝ × SpatialCoordinates d => (w.q tx.1)^n*
      (Real.exp (ρ.value tx.2*w.q tx.1))^2*((Prod.snd ⁻¹' W).indicator F tx))=
      ((Prod.snd ⁻¹' W).indicator (fun tx =>
        (w.q tx.1)^n*(Real.exp (ρ.value tx.2*w.q tx.1))^2*F tx)) := by
    funext tx
    by_cases hx : tx ∈ Prod.snd ⁻¹' W <;> simp [hx]
  have hi := (weighted_domain_density_integrable S hbounded g ρ w n hq hρ hc).indicator
    (hW.preimage measurable_snd)
  have hn := timeSq_eq_domainTimeIntegral_of_norm_sq S g ρ w (n:ℝ) u
    (F := (Prod.snd ⁻¹' W).indicator F) (by
      filter_upwards [hF] with t ht
      filter_upwards [ht] with x hx
      by_cases hw : x ∈ W <;> simpa [hw] using hx)
    (by simpa only [Real.rpow_natCast,he] using hi)
  simpa only [Real.rpow_natCast,he] using hn


end Carleman

namespace Carleman
variable {d : ℕ}
variable (S : Set (SpatialCoordinates d)) (hS : IsOpen S) (hd : 0 < d)
  (hb : Bornology.IsBounded S) (g : TimeGrid)
  (ρ : SpatialProfile (volume.restrict (S))) (w : TimeWeight)
  (hq : ContinuousOn w.q (Icc 0 g.period)) (hρ : Continuous ρ.value)
  (p : (boundedDirichletOriginalForm hS hd
    hb).model.PeriodicGraph g)
  {F : (ℝ × SpatialCoordinates d) → ℝ} (hF : ContDiff ℝ ∞ F)
  (htrace : ∀ t : Icc 0 g.period,
    p.val.1 t =ᵐ[volume.restrict (S)] (fun x => F (t,x)))

include hq hρ hF htrace in
theorem dirichletHeatLeft_eq_domainIntegral :
    dirichletHeatLeft hS hd hb g ρ w p =
      domainTimeIntegral S g.period (fun tx =>
        (w.q tx.1)^3*(Real.exp (ρ.value tx.2*w.q tx.1))^2*(F tx)^2)+
      domainTimeIntegral S g.period (fun tx =>
        w.q tx.1*(Real.exp (ρ.value tx.2*w.q tx.1))^2*‖gradient (fun y => F (tx.1,y)) tx.2‖^2) := by
  have hv := periodicGraph_value_classical_ae hS hd
    hb g p htrace
  have hzero := timeSq_eq_domainTimeIntegral_of_continuous S hb g ρ w 3 hq hρ
    (g.pathL2 p.val.1) (hF.continuous.pow 2) (by
      filter_upwards [hv] with t ht
      filter_upwards [ht] with x hx
      simp only [hx,Real.norm_eq_abs,sq_abs,Pi.pow_apply])
  have hgrad := timeSq_eq_domainTimeIntegral_of_continuous S hb g ρ w 1 hq hρ
    (dirichletPeriodicGradient hS hd hb g p)
    (smooth_spatial_gradient_sq_continuous hF)
    (dirichletPeriodicGradient_smooth_norm hS hd
      hb g p hF htrace)
  unfold dirichletHeatLeft
  simpa only [Nat.cast_ofNat,Nat.cast_one,pow_one,Pi.pow_apply] using congrArg₂ (fun x y : ℝ => x+y) hzero hgrad

include hq hρ hF htrace in
theorem dirichletHeatRight_eq_domainIntegral (ε : ℝ) (W : Set (SpatialCoordinates d)) (hW : MeasurableSet W)
    (hfields : ∀ᵐ t ∂g.timeMeasure,
      (p.val.2.1 t =ᵐ[volume.restrict (S)] (fun x => smoothD (1,0) F (t,x))) ∧
      (p.val.2.2 t =ᵐ[volume.restrict (S)]
        (fun x => -directionalLap spaceTimeSpatialDirection F (t,x)))) :
    dirichletHeatRight hS hd hb
      g ρ w ε W hW p =
      domainTimeIntegral S g.period (fun tx =>
        (Real.exp (ρ.value tx.2*w.q tx.1)*spaceTimeOrientedHeat ε F tx)^2)+
      domainTimeIntegral S g.period ((Prod.snd ⁻¹' W).indicator (fun tx =>
        (w.q tx.1)^3*(Real.exp (ρ.value tx.2*w.q tx.1))^2*(F tx)^2)) := by
  have hr := periodicGraph_residual_classical_ae hS hd
    hb g p ε hF hfields
  have hres := timeSq_eq_domainTimeIntegral_of_continuous S hb g ρ w 0 hq hρ
    (ε • p.val.2.1+p.val.2.2) ((smooth_oriented_heat_continuous ε hF).pow 2) (by
      filter_upwards [hr] with t ht
      filter_upwards [ht] with x hx
      simp only [hx,Real.norm_eq_abs,sq_abs,Pi.pow_apply])
  have ho := periodicGraph_observation_classical_ae hS hd
    hb g p W hW htrace
  have hobs := timeSq_eq_domainTimeIntegral_of_indicator S hb g ρ w 3 hq hρ W hW
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
