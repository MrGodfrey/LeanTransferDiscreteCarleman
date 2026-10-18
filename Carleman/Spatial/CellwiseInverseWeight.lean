module

public import Carleman.Spatial.SimplicialIntegrals

/-! The actual inverse mesh-size multiplier and its weighted L² integral.
Finite cell overlap is removed a.e. by the genuine partition theorem. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman

def BoundedMultiplier.restrictMeasure {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    (w : BoundedMultiplier μ) (hν : ν ≤ μ) : BoundedMultiplier ν where
  value := w.value
  measurable := w.measurable.mono_measure hν
  bound := w.bound
  bound_nonneg := w.bound_nonneg
  bounded := w.bounded.filter_mono (ae_mono hν)

namespace SimplicialPartition
variable {d : ℕ} {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}
  (M : Carleman.SimplicialPartition S ι)

def inverseScale (h : ι → ℝ) : BoundedMultiplier (volume.restrict S) where
  value x := ∑ i, (M.cell i).indicator (fun _ => (h i)⁻¹) x
  measurable := Finset.univ.aestronglyMeasurable_fun_sum (fun i _ =>
    aestronglyMeasurable_const.indicator (simplicialCell_measurable (M.simplex i).points))
  bound := ∑ i, |(h i)⁻¹|
  bound_nonneg := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  bounded := Filter.Eventually.of_forall (fun x => by
    classical
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : x ∈ M.cell i
    · rw [Set.indicator_of_mem hi]
    · rw [Set.indicator_of_notMem hi,abs_zero]
      exact abs_nonneg _)

theorem inverseScale_on_cell (hS : MeasurableSet S) (h : ι → ℝ) (i : ι) :
    ∀ᵐ x ∂volume.restrict S, x ∈ M.cell i → (M.inverseScale h).value x=(h i)⁻¹ := by
  classical
  filter_upwards [M.ae_partition hS] with x hx
  intro hi
  obtain ⟨j,_,hu⟩ := hx
  have hij := hu i hi
  subst j
  change (∑ j, (M.cell j).indicator (fun _ => (h j)⁻¹) x) = _
  rw [Finset.sum_eq_single i]
  · exact Set.indicator_of_mem hi _
  · intro j _ hji
    exact Set.indicator_of_notMem (fun hj => hji (hu j hj)) _
  · simp

def inverseWeight (h : ι → ℝ) (w : BoundedMultiplier (volume.restrict S)) :
    BoundedMultiplier (volume.restrict S) := (M.inverseScale h).mul w

theorem inverseWeight_on_cell (hS : MeasurableSet S) (h : ι → ℝ)
    (w : BoundedMultiplier (volume.restrict S)) (i : ι) :
    ∀ᵐ x ∂volume.restrict S, x ∈ M.cell i → (M.inverseWeight h w).value x=(h i)⁻¹*w.value x := by
  filter_upwards [M.inverseScale_on_cell hS h i] with x hx
  intro hi
  change (M.inverseScale h).value x*w.value x = _
  rw [hx hi]

theorem inverseWeight_sq_sum (hS : IsOpen S) (hc : Convex ℝ S) (h : ι → ℝ)
    (w : BoundedMultiplier (volume.restrict S)) (u : Lp ℝ 2 (volume.restrict S)) :
    ((M.inverseWeight h w).seminorm u)^2 =
      ∑ i, ((h i)⁻¹)^2 * ∫ x in M.cell i, |w.value x|^2*‖u x‖^2 := by
  rw [BoundedMultiplier.seminorm_sq_integral,
    M.integral_eq_sum_cells hS hc _ ((M.inverseWeight h w).integrable_density u)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [(M.inverseWeight_on_cell hS.measurableSet h w i).filter_mono
    (ae_mono (M.cell_measure_le_domain hS hc i)),
    ae_restrict_mem (simplicialCell_measurable (M.simplex i).points)] with x hx hi
  rw [hx hi,abs_mul,mul_pow,sq_abs]
  ring

end SimplicialPartition
end Carleman
