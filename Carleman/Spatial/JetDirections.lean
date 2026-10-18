module

public import Carleman.Spatial.WeakDirections
public import Carleman.Spatial.ComponentNorms

/-! Actual first and second directional derivatives of a component of a
symmetric weak Sobolev jet, with explicit finite coefficient bounds. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)}
  {S : Set (SpatialCoordinates d)}

def coordinateCombination (z : SpatialCoordinates d) (v : Fin d → Lp ℝ 2 ν) : Lp ℝ 2 ν :=
  ∑ i, (z i) • v i

def coordinateSize (z : SpatialCoordinates d) : ℝ := ∑ i, |z i|

theorem coordinateSize_nonneg (z : SpatialCoordinates d) : 0 ≤ coordinateSize z :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem coordinateCombination_add (z e : SpatialCoordinates d) (v : Fin d → Lp ℝ 2 ν) :
    coordinateCombination (z+e) v = coordinateCombination z v+coordinateCombination e v := by
  simp only [coordinateCombination,PiLp.add_apply,add_smul,Finset.sum_add_distrib]

theorem coordinateCombination_basis (i : Fin d) (v : Fin d → Lp ℝ 2 ν) :
    coordinateCombination (EuclideanSpace.basisFun (Fin d) ℝ i) v = v i := by
  simp [coordinateCombination,EuclideanSpace.basisFun_apply]

theorem coordinateCombination_norm_le (z : SpatialCoordinates d) (v : Fin d → Lp ℝ 2 ν)
    {B : ℝ} (hb : ∀ i, ‖v i‖ ≤ B) : ‖coordinateCombination z v‖ ≤ coordinateSize z*B := by
  calc
    _ ≤ ∑ i, ‖(z i) • v i‖ := norm_sum_le _ _
    _ ≤ ∑ i, |z i| *B := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [norm_smul,Real.norm_eq_abs] using mul_le_mul_of_nonneg_left (hb i) (abs_nonneg (z i))
    _ = _ := by rw [coordinateSize,Finset.sum_mul]

variable [IsFiniteMeasureOnCompacts ν]

theorem weak_coordinateCombination {u : Lp ℝ 2 ν} {v : Fin d → Lp ℝ 2 ν}
    (h : ∀ i, IsWeakSpatialDerivative ν S (EuclideanSpace.basisFun (Fin d) ℝ i) u (v i))
    (z : SpatialCoordinates d) : IsWeakSpatialDerivative ν S z u (coordinateCombination z v) := by
  have he := IsWeakSpatialDerivative.direction_sum Finset.univ
    (fun i => (z i) • EuclideanSpace.basisFun (Fin d) ℝ i) (fun i => (z i) • v i)
    (fun i _ => (h i).direction_smul (z i))
  have hz : (∑ i, z i • EuclideanSpace.basisFun (Fin d) ℝ i) = z :=
    (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr z
  rwa [hz] at he

theorem weak_coordinateCombination_second {v : Fin d → Lp ℝ 2 ν}
    {w : Fin d → Fin d → Lp ℝ 2 ν}
    (h : ∀ i j, IsWeakSpatialDerivative ν S (EuclideanSpace.basisFun (Fin d) ℝ j) (v i) (w i j))
    (z : SpatialCoordinates d) : IsWeakSpatialDerivative ν S z (coordinateCombination z v)
      (coordinateCombination z (fun i => coordinateCombination z (w i))) := by
  exact IsWeakSpatialDerivative.sum_states Finset.univ _ _
    (fun i _ => (weak_coordinateCombination (h i) z).smul (z i))
end Carleman
