module

public import Carleman.Spatial.L2Averaging
public import Carleman.Continuous.ScalarIntervalTrace
public import Carleman.Continuous.BochnerNormAlgebra

/-! Actual endpoint integral operators on product L² data. Their measurable
face values and scaled L² bounds are established before identifying spatial
weak derivatives with the one-dimensional weak slices. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

def fiberEndpointIntegral (g : TimeGrid) (c : ℝ) (f v : X × ℝ → ℝ) (x : X) : ℝ :=
  g.period⁻¹*(∫ t, (f (x,t)+(t-c)*v (x,t)) ∂g.timeMeasure)

omit [SFinite μ] in
theorem fiberEndpointIntegral_congr (g : TimeGrid) (c : ℝ) {f v f' v' : X × ℝ → ℝ}
    (hf : f =ᵐ[μ.prod g.timeMeasure] f') (hv : v =ᵐ[μ.prod g.timeMeasure] v') :
    fiberEndpointIntegral g c f v =ᵐ[μ] fiberEndpointIntegral g c f' v' := by
  filter_upwards [Measure.ae_ae_of_ae_prod hf,Measure.ae_ae_of_ae_prod hv] with x hx hdx
  apply congrArg (fun a => g.period⁻¹*a)
  apply integral_congr_ae
  filter_upwards [hx,hdx] with t ht hdt
  rw [ht,hdt]

theorem fiberEndpointIntegral_memLp_bound (g : TimeGrid) {c : ℝ}
    (hc : c ∈ Icc 0 g.period) {f v : X × ℝ → ℝ}
    (hf : MemLp f 2 (μ.prod g.timeMeasure)) (hv : MemLp v 2 (μ.prod g.timeMeasure)) :
    MemLp (fiberEndpointIntegral g c f v) 2 μ ∧
      (bochnerL2Norm μ (fiberEndpointIntegral g c f v))^2 ≤
        2/g.period*(bochnerL2Norm (μ.prod g.timeMeasure) f)^2+
          2*g.period*(bochnerL2Norm (μ.prod g.timeMeasure) v)^2 := by
  let w : X × ℝ → ℝ := fun p => (p.2-c)*v p
  have hcoeff : ∀ᵐ p ∂μ.prod g.timeMeasure, |p.2-c| ≤ g.period := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioo)] with p hp
    exact abs_le.mpr ⟨by linarith [hc.2,hp.1],by linarith [hc.1,hp.2]⟩
  have hw : MemLp w 2 (μ.prod g.timeMeasure) := by
    apply hv.of_le_mul (c := g.period)
    · exact ((measurable_snd.sub measurable_const).aestronglyMeasurable.mul hv.aestronglyMeasurable)
    · filter_upwards [hcoeff] with p hp
      change ‖(p.2-c)*v p‖ ≤ g.period*‖v p‖
      simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul_of_nonneg_right hp (abs_nonneg (v p))
  have hF : MemLp (fun p => f p+w p) 2 (μ.prod g.timeMeasure) := hf.add hw
  obtain ⟨havg,he⟩ := l2_average_square_le hF.aestronglyMeasurable hF.integrable_sq
  have hm : MemLp (fiberEndpointIntegral g c f v) 2 μ := havg.const_mul g.period⁻¹
  refine ⟨hm,?_⟩
  have hpoint : ∀ᵐ p ∂μ.prod g.timeMeasure,
      (f p+w p)^2 ≤ 2*(f p)^2+2*g.period^2*(v p)^2 := by
    filter_upwards [hcoeff] with p hp
    have hw2 : (w p)^2 ≤ g.period^2*(v p)^2 := by
      have ha : (p.2-c)^2 ≤ g.period^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) g.period_pos.le).mpr hp
      simpa only [w,mul_pow] using mul_le_mul_of_nonneg_right ha (sq_nonneg (v p))
    nlinarith [sq_nonneg (f p-w p)]
  have hmajor : Integrable (fun p => 2*(f p)^2+2*g.period^2*(v p)^2) (μ.prod g.timeMeasure) :=
    (hf.integrable_sq.const_mul 2).add (hv.integrable_sq.const_mul (2*g.period^2))
  have hi := integral_mono_ae hF.integrable_sq hmajor hpoint
  rw [integral_add (hf.integrable_sq.const_mul 2) (hv.integrable_sq.const_mul (2*g.period^2)),
    integral_const_mul,integral_const_mul,integral_sq_eq_bochnerL2Norm_sq hf,
    integral_sq_eq_bochnerL2Norm_sq hv] at hi
  have hscale : bochnerL2Norm μ (fiberEndpointIntegral g c f v)=
      g.period⁻¹*bochnerL2Norm μ (fun x => ∫ t, (f (x,t)+w (x,t)) ∂g.timeMeasure) := by
    change bochnerL2Norm μ (g.period⁻¹ • (fun x => ∫ t, (f (x,t)+w (x,t)) ∂g.timeMeasure))= _
    rw [bochnerL2Norm_const_smul,abs_of_pos (inv_pos.mpr g.period_pos)]
  rw [hscale,mul_pow]
  rw [g.timeMeasure_real_univ] at he
  calc
    _ ≤ g.period⁻¹^2*(g.period*(∫ p, (f p+w p)^2 ∂μ.prod g.timeMeasure)) :=
      mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ ≤ g.period⁻¹^2*(g.period*(2*(bochnerL2Norm (μ.prod g.timeMeasure) f)^2+
        2*g.period^2*(bochnerL2Norm (μ.prod g.timeMeasure) v)^2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hi g.period_pos.le) (sq_nonneg _)
    _ = _ := by field_simp [g.period_pos.ne']

end Carleman
