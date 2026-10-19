module

public import Carleman.Spatial.SmoothBoxTimeIntegral

/-! Order and scalar operations for the actual restricted cylinder integral. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem boxTimeIntegral_const_mul (a b : Fin d → ℝ) (T C : ℝ)
    (f : (ℝ × SpatialCoordinates d) → ℝ) :
    boxTimeIntegral a b T (fun x => C*f x)=C*boxTimeIntegral a b T f :=
  integral_const_mul C f

theorem boxTimeIntegral_mono_on (a b : Fin d → ℝ) (T : ℝ)
    {f g : (ℝ × SpatialCoordinates d) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ t ∈ Icc 0 T, ∀ x ∈ openCoordinateBox a b, f (t,x) ≤ g (t,x)) :
    boxTimeIntegral a b T f ≤ boxTimeIntegral a b T g := by
  have hfi := continuous_box_time_integrable a b T hf
  have hgi := continuous_box_time_integrable a b T hg
  unfold boxTimeIntegral
  rw [Measure.prod_restrict] at hfi hgi ⊢
  exact setIntegral_mono_on hfi hgi
    (measurableSet_Icc.prod (openCoordinateBox_isOpen a b).measurableSet)
    (fun tx hx => hfg tx.1 hx.1 tx.2 hx.2)

end Carleman
