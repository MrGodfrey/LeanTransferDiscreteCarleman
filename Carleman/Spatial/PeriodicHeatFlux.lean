module

public import Carleman.Spatial.SpacetimeHeatIdentity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Algebra.Ring.Periodic

/-! Exact cancellation of the actual smooth heat time flux over a period. -/
@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace Carleman
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

theorem smoothD_periodic {f : E → ℝ} {a : E} (hf : Function.Periodic f a) (e : E) :
    Function.Periodic (smoothD e f) a := by
  intro x
  have he : (fun y => f (y+a))=f := funext hf
  change fderiv ℝ f (x+a) e=fderiv ℝ f x e
  rw [← fderiv_comp_add_right a,he]

theorem directionalLap_periodic (e : ι → E) {f : E → ℝ} {a : E}
    (hf : Function.Periodic f a) : Function.Periodic (directionalLap e f) a := by
  intro x
  exact Finset.sum_congr rfl fun i _ => smoothD_periodic (smoothD_periodic hf (e i)) (e i) x

theorem directionalEnergy_periodic (e : ι → E) {f : E → ℝ} {a : E}
    (hf : Function.Periodic f a) : Function.Periodic (directionalEnergy e f) a := by
  intro x
  exact Finset.sum_congr rfl fun i _ => congrArg (fun r : ℝ => r^2) (smoothD_periodic hf (e i) x)

theorem heatConjugationK_periodic (e : ι → E) (t : E) {l p : E → ℝ} {a : E}
    (hl : Function.Periodic l a) (hp : Function.Periodic p a) :
    Function.Periodic (heatConjugationK e t l p) a := by
  intro x
  simp only [heatConjugationK,smoothD_periodic hl t x,directionalEnergy_periodic e hl x,
    directionalLap_periodic e hl x,hp x]

theorem pointwiseHeatTimeFlux_contDiff (e : ι → E) {k z : E → ℝ}
    (hk : ContDiff ℝ ∞ k) (hz : ContDiff ℝ ∞ z) :
    ContDiff ℝ ∞ (pointwiseHeatTimeFlux e k z) :=
  (hk.mul (hz.pow 2)).sub (directionalEnergy_contDiff e hz)

theorem pointwiseHeatTimeFlux_periodic (e : ι → E) {k z : E → ℝ} {a : E}
    (hk : Function.Periodic k a) (hz : Function.Periodic z a) :
    Function.Periodic (pointwiseHeatTimeFlux e k z) a := by
  intro x
  simp only [pointwiseHeatTimeFlux,hk x,hz x,directionalEnergy_periodic e hz x]

theorem spacetime_periodic_derivative_integral {d : ℕ}
    {f : (ℝ × SpatialCoordinates d) → ℝ} (hf : ContDiff ℝ ∞ f) (T : ℝ)
    (hp : Function.Periodic f (T,0)) (x : SpatialCoordinates d) :
    (∫ t in (0:ℝ)..T, smoothD (1,0) f (t,x))=0 := by
  have hc : ContDiff ℝ ∞ (fun t : ℝ => f (t,x)) :=
    hf.comp (contDiff_id.prodMk contDiff_const)
  simp_rw [spaceTime_timeD hf]
  rw [intervalIntegral.integral_deriv_eq_sub (fun t _ => hc.differentiable (by simp) t)
    ((hc.continuous_deriv (by simp)).intervalIntegrable 0 T)]
  have he := hp (0,x)
  simpa only [Prod.mk_add_mk,zero_add,add_zero] using sub_eq_zero.mpr he

theorem spacetime_heat_time_flux_integral {d : ℕ}
    {l p u : (ℝ × SpatialCoordinates d) → ℝ}
    (hl : ContDiff ℝ ∞ l) (hp : ContDiff ℝ ∞ p) (hu : ContDiff ℝ ∞ u) (T : ℝ)
    (hpl : Function.Periodic l (T,0)) (hpp : Function.Periodic p (T,0))
    (hpu : Function.Periodic u (T,0)) (x : SpatialCoordinates d) :
    let e := spaceTimeSpatialDirection (d := d)
    let z := fun y => Real.exp (l y)*u y
    let k := heatConjugationK e (1,0) l p
    (∫ t in (0:ℝ)..T, smoothD (1,0) (pointwiseHeatTimeFlux e k z) (t,x))=0 := by
  dsimp only
  apply spacetime_periodic_derivative_integral
  · exact pointwiseHeatTimeFlux_contDiff _ (heatConjugationK_contDiff _ _ hl hp) (hl.exp.mul hu)
  · exact pointwiseHeatTimeFlux_periodic _ (heatConjugationK_periodic _ _ hpl hpp)
      ((hpl.comp Real.exp).mul hpu)

end Carleman
