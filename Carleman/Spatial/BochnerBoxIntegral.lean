module

public import Carleman.Spatial.WeightedTimeContinuity
public import Carleman.Spatial.BoxObservationIntegral

/-! Exact Fubini identification of the original weighted Bochner squares and actual cylinders. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
namespace Carleman
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (a b : Fin d → ℝ) (g : TimeGrid) (ρ : SpatialProfile (volume.restrict (openCoordinateBox a b)))
  (w : TimeWeight)

theorem weighted_box_density_integrable (n : ℕ)
    (hq : ContinuousOn w.q (Icc 0 g.period)) (hρ : Continuous ρ.value)
    {F : (ℝ × SpatialCoordinates d) → ℝ} (hF : Continuous F) :
    Integrable (fun tx => (w.q tx.1)^n*(Real.exp (ρ.value tx.2*w.q tx.1))^2*F tx)
      ((volume.restrict (Icc 0 g.period)).prod (volume.restrict (openCoordinateBox a b))) := by
  let K := (Icc (0:ℝ) g.period) ×ˢ closure (openCoordinateBox a b)
  have hk : IsCompact K := isCompact_Icc.prod (openCoordinateBox_isBounded a b).isCompact_closure
  have hcq : ContinuousOn (fun tx : ℝ × SpatialCoordinates d => w.q tx.1) K :=
    hq.comp continuous_fst.continuousOn (fun _ hx => hx.1)
  have hce : ContinuousOn (fun tx : ℝ × SpatialCoordinates d =>
      Real.exp (ρ.value tx.2*w.q tx.1)) K :=
    Real.continuous_exp.comp_continuousOn ((hρ.comp continuous_snd).continuousOn.mul hcq)
  have hi := ContinuousOn.integrableOn_compact (μ := volume) hk
    (((hcq.pow n).mul (hce.pow 2)).mul hF.continuousOn)
  rw [Measure.prod_restrict]
  exact hi.mono_set (prod_mono subset_rfl subset_closure)

theorem timeSq_eq_boxTimeIntegral_of_norm_sq (s : ℝ)
    (u : Lp (Lp E 2 (volume.restrict (openCoordinateBox a b))) 2 g.timeMeasure)
    {F : (ℝ × SpatialCoordinates d) → ℝ}
    (hF : ∀ᵐ t ∂g.timeMeasure,
      (fun x => ‖u t x‖^2) =ᵐ[volume.restrict (openCoordinateBox a b)] (fun x => F (t,x)))
    (hi : Integrable (fun tx => (w.q tx.1)^s*(Real.exp (ρ.value tx.2*w.q tx.1))^2*F tx)
      ((volume.restrict (Icc 0 g.period)).prod (volume.restrict (openCoordinateBox a b)))) :
    timeSq g w.q s (fun t => (ρ.multiplier w 0 t).seminorm) u =
      boxTimeIntegral a b g.period (fun tx =>
        (w.q tx.1)^s*(Real.exp (ρ.value tx.2*w.q tx.1))^2*F tx) := by
  unfold boxTimeIntegral
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

theorem timeSq_eq_boxTimeIntegral_of_continuous (n : ℕ)
    (hq : ContinuousOn w.q (Icc 0 g.period)) (hρ : Continuous ρ.value)
    (u : Lp (Lp E 2 (volume.restrict (openCoordinateBox a b))) 2 g.timeMeasure)
    {F : (ℝ × SpatialCoordinates d) → ℝ} (hc : Continuous F)
    (hF : ∀ᵐ t ∂g.timeMeasure,
      (fun x => ‖u t x‖^2) =ᵐ[volume.restrict (openCoordinateBox a b)] (fun x => F (t,x))) :
    timeSq g w.q (n:ℝ) (fun t => (ρ.multiplier w 0 t).seminorm) u =
      boxTimeIntegral a b g.period (fun tx =>
        (w.q tx.1)^n*(Real.exp (ρ.value tx.2*w.q tx.1))^2*F tx) := by
  simpa only [Real.rpow_natCast] using timeSq_eq_boxTimeIntegral_of_norm_sq a b g ρ w (n:ℝ) u hF
    (by simpa only [Real.rpow_natCast] using weighted_box_density_integrable a b g ρ w n hq hρ hc)

theorem timeSq_eq_boxTimeIntegral_of_indicator (n : ℕ)
    (hq : ContinuousOn w.q (Icc 0 g.period)) (hρ : Continuous ρ.value)
    (W : Set (SpatialCoordinates d)) (hW : MeasurableSet W)
    (u : Lp (Lp E 2 (volume.restrict (openCoordinateBox a b))) 2 g.timeMeasure)
    {F : (ℝ × SpatialCoordinates d) → ℝ} (hc : Continuous F)
    (hF : ∀ᵐ t ∂g.timeMeasure,
      (fun x => ‖u t x‖^2) =ᵐ[volume.restrict (openCoordinateBox a b)]
        (fun x => W.indicator (fun y => F (t,y)) x)) :
    timeSq g w.q (n:ℝ) (fun t => (ρ.multiplier w 0 t).seminorm) u =
      boxTimeIntegral a b g.period ((Prod.snd ⁻¹' W).indicator (fun tx =>
        (w.q tx.1)^n*(Real.exp (ρ.value tx.2*w.q tx.1))^2*F tx)) := by
  have he : (fun tx : ℝ × SpatialCoordinates d => (w.q tx.1)^n*
      (Real.exp (ρ.value tx.2*w.q tx.1))^2*((Prod.snd ⁻¹' W).indicator F tx))=
      ((Prod.snd ⁻¹' W).indicator (fun tx =>
        (w.q tx.1)^n*(Real.exp (ρ.value tx.2*w.q tx.1))^2*F tx)) := by
    funext tx
    by_cases hx : tx ∈ Prod.snd ⁻¹' W <;> simp [hx]
  have hi := (weighted_box_density_integrable a b g ρ w n hq hρ hc).indicator
    (hW.preimage measurable_snd)
  have hn := timeSq_eq_boxTimeIntegral_of_norm_sq a b g ρ w (n:ℝ) u
    (F := (Prod.snd ⁻¹' W).indicator F) (by
      filter_upwards [hF] with t ht
      filter_upwards [ht] with x hx
      by_cases hw : x ∈ W <;> simpa [hw] using hx)
    (by simpa only [Real.rpow_natCast,he] using hi)
  simpa only [Real.rpow_natCast,he] using hn

end Carleman
