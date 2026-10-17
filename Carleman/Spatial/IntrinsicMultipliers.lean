module

public import Carleman.Spatial.WeakLeibniz
public import Carleman.Weights.IntrinsicDerivatives

/-! Interior coefficient derivatives as actual bounded L² multipliers. The
measure is concentrated in the open domain; boundary values are irrelevant. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Carleman
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)}
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S)
  (hνS : ∀ᵐ x ∂ν, x ∈ S) {f : SpatialCoordinates d → ℝ} (hf : BoundedSmoothOn f S)

def intrinsicWordMultiplier (l : List (Fin d)) : BoundedMultiplier ν where
  value := wordDerivative l f
  measurable := by
    have hc := (wordDerivative_smooth hS hf.1 l).continuousOn
    have hm := hc.aestronglyMeasurable (μ := ν) hS.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem hνS] at hm
  bound := (hf.2 l.length).choose
  bound_nonneg := zero_le_one.trans (hf.2 l.length).choose_spec.1
  bounded := by
    filter_upwards [hνS] with x hx
    exact (abs_coordinateDerivative_le (wordVector l).get f x).trans
      ((hf.2 l.length).choose_spec.2 l.length le_rfl x hx)

theorem intrinsicWordMultiplier_smooth (l : List (Fin d)) :
    ContDiffOn ℝ ∞ (intrinsicWordMultiplier hS hνS hf l).value S :=
  wordDerivative_smooth hS hf.1 l

theorem intrinsicWordMultiplier_derivative (l : List (Fin d)) (i : Fin d) :
    (intrinsicWordMultiplier hS hνS hf (i::l)).value =ᵐ[ν]
      (fun x => fderiv ℝ (intrinsicWordMultiplier hS hνS hf l).value x
        (EuclideanSpace.basisFun (Fin d) ℝ i)) := by
  filter_upwards [hνS] with x hx
  exact wordDerivative_cons l i (hf.1.contDiffAt (hS.mem_nhds hx))

theorem intrinsicWordMultiplier_nil (w : BoundedMultiplier ν) (hw : w.value = f)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u : Lp E 2 ν) :
    (intrinsicWordMultiplier hS hνS hf []).map u = w.map u := by
  apply Lp.ext
  filter_upwards [(intrinsicWordMultiplier hS hνS hf []).map_ae u, w.map_ae u] with x h1 h2
  rw [h1, h2]
  change wordDerivative [] f x • u x = w.value x • u x
  rw [wordDerivative_nil, hw]

variable [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]

/-- Full weak Leibniz on the original domain, using actual bounded interior
derivatives. No exterior smooth extension or additional trace condition. -/
theorem weak_leibniz_intrinsic {n : ℕ} (w : BoundedMultiplier ν) (hw : w.value = f)
    (u v : WeakSobolevJet d n ν S) (hv : WeakSobolevJet.value v = w.map (WeakSobolevJet.value u))
    (l : List (Fin d)) (hl : l.length ≤ n) :
    WeakSobolevJet.wordField v l =
      WeakSobolevJet.leibnizField (intrinsicWordMultiplier hS hνS hf) u l := by
  apply WeakSobolevJet.wordField_mul hS hνS (intrinsicWordMultiplier hS hνS hf)
    (intrinsicWordMultiplier_smooth hS hνS hf)
    (intrinsicWordMultiplier_derivative hS hνS hf) u v _ l hl
  rw [intrinsicWordMultiplier_nil hS hνS hf w hw]
  exact hv

end Carleman
