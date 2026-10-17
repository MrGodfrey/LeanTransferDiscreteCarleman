module

public import Carleman.Continuous.WeakTimeProduct
public import Carleman.Continuous.WeakPeriodicUnique

/-! Periodic integration by parts for arbitrary H-valued weak H¹ paths.
The actual continuous endpoint representatives are used, with no pointwise
operator-domain hypothesis. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem HasWeakTimeDerivative.periodic_pairing {g : TimeGrid} {u du v dv : ℝ → H}
    (hu : HasWeakTimeDerivative g u du) (hv : HasWeakTimeDerivative g v dv)
    (huc : ContinuousOn u (Icc 0 g.period)) (hvc : ContinuousOn v (Icc 0 g.period))
    (hdu : MemLp du 2 g.timeMeasure) (hdv : MemLp dv 2 g.timeMeasure)
    (hup : u 0 = u g.period) (hvp : v 0 = v g.period) :
    (∫ t, inner ℝ (du t) (v t) ∂g.timeMeasure) +
      (∫ t, inner ℝ (u t) (dv t) ∂g.timeMeasure) = 0 := by
  have hACu := hu.absolutelyContinuous huc hdu
  have hACv := hv.absolutelyContinuous hvc hdv
  have hW : AbsolutelyContinuousOnInterval (fun t => innerSL ℝ (u t)) 0 g.period :=
    (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ).lipschitzWith.comp_absolutelyContinuousOnInterval hACu
  have hh := absolutelyContinuous_clm_apply hW hACv
  have hAC : AbsolutelyContinuousOnInterval (fun t => inner ℝ (u t) (v t)) 0 g.period := by
    simpa only [innerSL_apply_apply] using hh
  have he := hAC.integral_deriv_eq_sub
  rw [← g.timeIntegral_eq_intervalIntegral, ← hup, ← hvp, sub_self] at he
  have hd : (fun t => deriv (fun x => inner ℝ (u x) (v x)) t) =ᵐ[g.timeMeasure]
      (fun t => inner ℝ (du t) (v t) + inner ℝ (u t) (dv t)) := by
    filter_upwards [hu.ae_hasDerivAt huc hdu, hv.ae_hasDerivAt hvc hdv] with t h1 h2
    simpa only [add_comm] using (h1.inner ℝ h2).deriv
  rw [integral_congr_ae hd, integral_add
    (integrable_inner_of_memLp hdu (g.memLp_of_continuousOn hvc))
    (integrable_inner_of_memLp (g.memLp_of_continuousOn huc) hdv)] at he
  exact he

end Carleman
