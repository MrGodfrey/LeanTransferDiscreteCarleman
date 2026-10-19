module

public import Carleman.Spatial.SmoothBoxDivergence
public import Carleman.Spatial.PeriodicHeatFlux

/-! Actual space-time integration on finite cylinders, with internal integrability. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff BigOperators
namespace Carleman
variable {d : ℕ}

def boxTimeIntegral (a b : Fin d → ℝ) (T : ℝ)
    (f : (ℝ × SpatialCoordinates d) → ℝ) : ℝ :=
  ∫ tx, f tx ∂((volume.restrict (Icc 0 T)).prod (volume.restrict (openCoordinateBox a b)))

theorem continuous_box_time_integrable (a b : Fin d → ℝ) (T : ℝ)
    {f : (ℝ × SpatialCoordinates d) → ℝ} (hf : Continuous f) :
    Integrable f ((volume.restrict (Icc 0 T)).prod (volume.restrict (openCoordinateBox a b))) := by
  have hk : IsCompact ((Icc (0:ℝ) T) ×ˢ closure (openCoordinateBox a b)) :=
    isCompact_Icc.prod (openCoordinateBox_isBounded a b).isCompact_closure
  have hi := ContinuousOn.integrableOn_compact (μ := volume) hk hf.continuousOn
  rw [Measure.prod_restrict]
  exact hi.mono_set (prod_mono subset_rfl subset_closure)

theorem boxTimeIntegral_eq_iterated (a b : Fin d → ℝ) (T : ℝ)
    {f : (ℝ × SpatialCoordinates d) → ℝ} (hf : Continuous f) :
    boxTimeIntegral a b T f = ∫ t in Icc 0 T, ∫ x in openCoordinateBox a b, f (t,x) :=
  integral_prod f (continuous_box_time_integrable a b T hf)

theorem boxTimeIntegral_add (a b : Fin d → ℝ) (T : ℝ)
    {f g : (ℝ × SpatialCoordinates d) → ℝ} (hf : Continuous f) (hg : Continuous g) :
    boxTimeIntegral a b T (fun x => f x+g x)=boxTimeIntegral a b T f+boxTimeIntegral a b T g :=
  integral_add (continuous_box_time_integrable a b T hf) (continuous_box_time_integrable a b T hg)

theorem boxTimeIntegral_mono (a b : Fin d → ℝ) (T : ℝ)
    {f g : (ℝ × SpatialCoordinates d) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x, f x ≤ g x) : boxTimeIntegral a b T f ≤ boxTimeIntegral a b T g :=
  integral_mono (continuous_box_time_integrable a b T hf) (continuous_box_time_integrable a b T hg) hfg

theorem boxTimeIntegral_nonpos_of_spatial (a b : Fin d → ℝ) (T : ℝ)
    {f : (ℝ × SpatialCoordinates d) → ℝ} (hf : Continuous f)
    (hs : ∀ t ∈ Icc 0 T, (∫ x in openCoordinateBox a b, f (t,x)) ≤ 0) :
    boxTimeIntegral a b T f ≤ 0 := by
  rw [boxTimeIntegral_eq_iterated a b T hf]
  exact setIntegral_nonpos measurableSet_Icc hs

theorem boxTimeIntegral_periodic_derivative (a b : Fin d → ℝ) {T : ℝ} (hT : 0 ≤ T)
    {f : (ℝ × SpatialCoordinates d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f (T,0)) :
    boxTimeIntegral a b T (smoothD (1,0) f)=0 := by
  unfold boxTimeIntegral
  rw [integral_prod_symm _ (continuous_box_time_integrable a b T
    (smoothD_contDiff hf (1,0)).continuous)]
  have he (x : SpatialCoordinates d) : (∫ t in Icc 0 T, smoothD (1,0) f (t,x))=0 := by
    rw [← setIntegral_congr_set (Ioc_ae_eq_Icc : Ioc (0:ℝ) T =ᵐ[volume] Icc 0 T),
      ← intervalIntegral.integral_of_le hT]
    exact spacetime_periodic_derivative_integral hf T hp x
  simp only [he,integral_zero]

end Carleman
