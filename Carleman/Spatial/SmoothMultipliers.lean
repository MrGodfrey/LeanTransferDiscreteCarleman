module

public import Carleman.Spatial.WeakLeibniz
public import Carleman.Weights.SmoothClosure

/-! Actual smooth coefficient derivatives on a compact closure are bounded
L² multipliers, constructed rather than assumed. Bounds used for construction
are kept separate from the uniform relative estimates. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Carleman
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)}
  {U K : Set (SpatialCoordinates d)} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
  (hνK : ∀ᵐ x ∂ν, x ∈ K) {f : SpatialCoordinates d → ℝ} (hf : ContDiffOn ℝ ∞ f U)

def smoothWordMultiplier (l : List (Fin d)) : BoundedMultiplier ν where
  value := wordDerivative l f
  measurable := by
    have hc := (wordDerivative_smooth hU hf l).continuousOn
    have hm := hc.aestronglyMeasurable (μ := ν) hU.measurableSet
    have hu : ∀ᵐ x ∂ν, x ∈ U := hνK.mono fun _ hx => hKU hx
    rwa [Measure.restrict_eq_self_of_ae_mem hu] at hm
  bound := (exists_profile_actual_bound hU hK hKU hf l.length).choose
  bound_nonneg := zero_le_one.trans (exists_profile_actual_bound hU hK hKU hf l.length).choose_spec.1
  bounded := by
    filter_upwards [hνK] with x hx
    exact (abs_coordinateDerivative_le (wordVector l).get f x).trans
      ((exists_profile_actual_bound hU hK hKU hf l.length).choose_spec.2 l.length le_rfl x hx)

theorem smoothWordMultiplier_smooth (l : List (Fin d)) :
    ContDiffOn ℝ ∞ (smoothWordMultiplier hU hK hKU hνK hf l).value U :=
  wordDerivative_smooth hU hf l

theorem smoothWordMultiplier_derivative (l : List (Fin d)) (i : Fin d) :
    (smoothWordMultiplier hU hK hKU hνK hf (i::l)).value =ᵐ[ν]
      (fun x => fderiv ℝ (smoothWordMultiplier hU hK hKU hνK hf l).value x
        (EuclideanSpace.basisFun (Fin d) ℝ i)) := by
  filter_upwards [hνK] with x hx
  exact wordDerivative_cons l i (hf.contDiffAt (hU.mem_nhds (hKU hx)))

theorem smoothWordMultiplier_nil (w : BoundedMultiplier ν) (hw : w.value = f)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u : Lp E 2 ν) :
    (smoothWordMultiplier hU hK hKU hνK hf []).map u = w.map u := by
  apply Lp.ext
  filter_upwards [(smoothWordMultiplier hU hK hKU hνK hf []).map_ae u, w.map_ae u] with x h1 h2
  rw [h1, h2]
  change wordDerivative [] f x • u x = w.value x • u x
  rw [wordDerivative_nil, hw]

variable [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hSU : S ⊆ U)
  (hνS : ∀ᵐ x ∂ν, x ∈ S)

include hS hSU hνS
/-- The full weak Leibniz formula instantiated with actual classical derivatives
of the smooth coefficient, on the original domain and existing weak jets. -/
theorem weak_leibniz_smooth {n : ℕ} (w : BoundedMultiplier ν) (hw : w.value = f)
    (u v : WeakSobolevJet d n ν S) (hv : WeakSobolevJet.value v = w.map (WeakSobolevJet.value u))
    (l : List (Fin d)) (hl : l.length ≤ n) :
    WeakSobolevJet.wordField v l =
      WeakSobolevJet.leibnizField (smoothWordMultiplier hU hK hKU hνK hf) u l := by
  apply WeakSobolevJet.wordField_mul hS hνS
    (smoothWordMultiplier hU hK hKU hνK hf)
    (fun l => (smoothWordMultiplier_smooth hU hK hKU hνK hf l).mono hSU)
    (smoothWordMultiplier_derivative hU hK hKU hνK hf) u v _ l hl
  rw [smoothWordMultiplier_nil hU hK hKU hνK hf w hw]
  exact hv

end Carleman
