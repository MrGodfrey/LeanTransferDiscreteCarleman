module

public import Carleman.Spatial.ProductFaceTrace

/-! The actual endpoint integral defines a linear operator on product L²
data. Integrability is established on almost every interval before splitting
the Bochner integral. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem fiberEndpoint_integrable_slices (g : TimeGrid) (c : Icc (0:ℝ) g.period)
    (f v : Lp ℝ 2 (μ.prod g.timeMeasure)) :
    ∀ᵐ x ∂μ, Integrable (fun t => f (x,t)+(t-c)*v (x,t)) g.timeMeasure := by
  filter_upwards [(Lp.memLp f).aestronglyMeasurable.prodMk_left,
    (Lp.memLp f).integrable_sq.prod_right_ae,(Lp.memLp v).aestronglyMeasurable.prodMk_left,
    (Lp.memLp v).integrable_sq.prod_right_ae] with x hfm hfi hvm hvi
  have hf := (memLp_two_iff_integrable_sq hfm).mpr hfi
  have hv := (memLp_two_iff_integrable_sq hvm).mpr hvi
  have hw : MemLp (fun t : ℝ => (t-c)*v (x,t)) 2 g.timeMeasure := by
    apply hv.of_le_mul (c := g.period)
    · exact ((measurable_id.sub measurable_const).aestronglyMeasurable.mul hvm)
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have he : |t-c| ≤ g.period := abs_le.mpr ⟨by linarith [c.property.2,ht.1],
        by linarith [c.property.1,ht.2]⟩
      simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul_of_nonneg_right he (abs_nonneg (v (x,t)))
  exact (hf.add hw).integrable (by norm_num)

theorem fiberEndpointLp_add (g : TimeGrid) (c : Icc (0:ℝ) g.period)
    (f v f' v' : Lp ℝ 2 (μ.prod g.timeMeasure)) :
    fiberEndpointLp g c (f+f') (v+v')=fiberEndpointLp g c f v+fiberEndpointLp g c f' v' := by
  apply Lp.ext
  filter_upwards [fiberEndpointLp_ae g c (f+f') (v+v'),
    fiberEndpointIntegral_congr g (c:ℝ) (Lp.coeFn_add f f') (Lp.coeFn_add v v'),
    fiberEndpointLp_ae g c f v,fiberEndpointLp_ae g c f' v',
    Lp.coeFn_add (fiberEndpointLp g c f v) (fiberEndpointLp g c f' v'),
    fiberEndpoint_integrable_slices g c f v,fiberEndpoint_integrable_slices g c f' v']
    with x hsum hcon h1 h2 hout hi1 hi2
  rw [hsum,hcon,hout,Pi.add_apply,h1,h2]
  unfold fiberEndpointIntegral
  have he : (fun t => ((f: X × ℝ → ℝ)+(f': X × ℝ → ℝ)) (x,t)+
      (t-(c:ℝ))*((v: X × ℝ → ℝ)+(v': X × ℝ → ℝ)) (x,t)) =
      (fun t => (f (x,t)+(t-c)*v (x,t))+(f' (x,t)+(t-c)*v' (x,t))) := by
    funext t
    simp only [Pi.add_apply]
    ring
  rw [he,integral_add hi1 hi2,mul_add]

theorem fiberEndpointLp_smul (g : TimeGrid) (c : Icc (0:ℝ) g.period)
    (r : ℝ) (f v : Lp ℝ 2 (μ.prod g.timeMeasure)) :
    fiberEndpointLp g c (r • f) (r • v)=r • fiberEndpointLp g c f v := by
  apply Lp.ext
  filter_upwards [fiberEndpointLp_ae g c (r • f) (r • v),
    fiberEndpointIntegral_congr g (c:ℝ) (Lp.coeFn_smul r f) (Lp.coeFn_smul r v),
    fiberEndpointLp_ae g c f v,Lp.coeFn_smul r (fiberEndpointLp g c f v)] with x hsum hcon h1 hout
  rw [hsum,hcon,hout,Pi.smul_apply,h1]
  unfold fiberEndpointIntegral
  have he : (fun t => (r • (f: X × ℝ → ℝ)) (x,t)+(t-(c:ℝ))*(r • (v: X × ℝ → ℝ)) (x,t)) =
      (fun t => r*(f (x,t)+(t-c)*v (x,t))) := by
    funext t
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  rw [he,integral_const_mul]
  simp only [smul_eq_mul]
  ring

def fiberEndpointLinearMap (g : TimeGrid) (c : Icc (0:ℝ) g.period) :
    (Lp ℝ 2 (μ.prod g.timeMeasure) × Lp ℝ 2 (μ.prod g.timeMeasure)) →ₗ[ℝ] Lp ℝ 2 μ where
  toFun p := fiberEndpointLp g c p.1 p.2
  map_add' p q := fiberEndpointLp_add g c p.1 p.2 q.1 q.2
  map_smul' r p := fiberEndpointLp_smul g c r p.1 p.2

end Carleman
