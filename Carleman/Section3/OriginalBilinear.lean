module

public import Carleman.Section3.OriginalForm

/-! Construct the Hilbert bounded form from the original bilinear form and
its explicit H^m norm bound. Thus the continuous-map representation adds no
analytic assumption to A1. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory Set
namespace Carleman

def boundedRealForm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (C : ℝ) (hf : ∀ u v, ‖f u v‖ ≤ C*‖u‖*‖v‖) :
    E →L[ℝ] E →L[ℝ] ℝ := f.mkContinuous₂ C hf

variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  (V : Submodule ℝ (Lp ℝ 2 ν))

def conformingValue : conformingHilbert (m := m) (S := S) V →ₗ[ℝ] V :=
  (conformingEmbed (m := m) (S := S) V).toLinearMap.codRestrict V (fun u => u.property)

namespace OriginalForm
variable (hV : V ≤ sobolevSubspace d m ν S)
  (hclosed : IsClosed {u : WeakSobolevJet d m ν S | WeakSobolevJet.value u ∈ V})
  (hdense : Dense (V : Set (Lp ℝ 2 ν))) (a : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  (C : ℝ) (hbound : ∀ u v : conformingHilbert (m := m) (S := S) V,
    |a (conformingValue (m := m) (S := S) V u) (conformingValue (m := m) (S := S) V v)| ≤ C*‖u‖*‖v‖)
  (hsym : ∀ u v, a u v = a v u)
  (hcoer : ∃ c > (0 : ℝ), ∀ u : conformingHilbert (m := m) (S := S) V,
    c*‖u‖*‖u‖ ≤ a (conformingValue (m := m) (S := S) V u) (conformingValue (m := m) (S := S) V u))

def ofBilinear : OriginalForm (m := m) hS hν where
  V := V
  sobolev := hV
  closed := hclosed
  dense := hdense
  form := by
    letI : NormedSpace ℝ (conformingHilbert (m := m) (S := S) V) := inferInstance
    let f : conformingHilbert (m := m) (S := S) V →ₗ[ℝ]
        conformingHilbert (m := m) (S := S) V →ₗ[ℝ] ℝ :=
      a.compl₁₂ (conformingValue (m := m) (S := S) V) (conformingValue (m := m) (S := S) V)
    exact @boundedRealForm (conformingHilbert (m := m) (S := S) V) inferInstance inferInstance f C (fun u v => by
      change ‖a (conformingValue (m := m) (S := S) V u) (conformingValue (m := m) (S := S) V v)‖ ≤ C*‖u‖*‖v‖
      rw [Real.norm_eq_abs]
      exact hbound u v)
  symmetric u v := hsym _ _
  coercive := hcoer

set_option maxHeartbeats 1600000 in
/-- The realized scalar form agrees on all original V states. -/
theorem ofBilinear_scalarForm (u v : V) :
    (ofBilinear hS hν V hV hclosed hdense a C hbound hsym hcoer).scalarForm u v = a u v := by
  let B := ofBilinear hS hν V hV hclosed hdense a C hbound hsym hcoer
  change B.form (B.valueEquiv.symm u) (B.valueEquiv.symm v) = a u v
  change a (B.valueEquiv (B.valueEquiv.symm u)) (B.valueEquiv (B.valueEquiv.symm v)) = a u v
  exact congrArg₂ (fun x y : B.V => a x y) (B.valueEquiv.apply_symm_apply u) (B.valueEquiv.apply_symm_apply v)
end OriginalForm
end Carleman
