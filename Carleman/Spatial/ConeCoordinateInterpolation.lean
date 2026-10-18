module

public import Carleman.Spatial.WeakConeInterpolation
public import Carleman.Spatial.JetDirections

/-! Coordinate derivatives are recovered from two actual inward directions.
This turns the cone estimate into a local bound for every coordinate, with
one geometric constant and arbitrary weak states. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

def coneCoordinateConstant (p : InwardConePatch S) : ℝ :=
  coordinateSize p.direction^2+
    ∑ i : Fin d, coordinateSize (p.direction+EuclideanSpace.basisFun (Fin d) ℝ i)^2

theorem coneCoordinateConstant_nonneg (p : InwardConePatch S) : 0 ≤ coneCoordinateConstant p :=
  add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem weak_cone_coordinate_interpolation (hS : IsOpen S) (p : InwardConePatch S)
    {t : ℝ} (ht : 0 < t) (hheight : t ≤ p.height)
    {u : Lp ℝ 2 ((volume : Measure (SpatialCoordinates d)).restrict S)}
    {v : Fin d → Lp ℝ 2 (volume.restrict S)}
    {w : Fin d → Fin d → Lp ℝ 2 (volume.restrict S)}
    (hfirst : ∀ i, IsWeakSpatialDerivative (volume.restrict S) S
      (EuclideanSpace.basisFun (Fin d) ℝ i) u (v i))
    (hsecond : ∀ i j, IsWeakSpatialDerivative (volume.restrict S) S
      (EuclideanSpace.basisFun (Fin d) ℝ j) (v i) (w i j))
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ i j, ‖w i j‖ ≤ B) (i : Fin d) :
    bochnerL2Norm (volume.restrict (p.region ∩ S)) (v i) ≤
      4/t*‖u‖+t*coneCoordinateConstant p*B := by
  let ν := (volume : Measure (SpatialCoordinates d)).restrict (p.region ∩ S)
  let a := p.direction
  let b := p.direction+EuclideanSpace.basisFun (Fin d) ℝ i
  let V := fun z => coordinateCombination z v
  let W := fun z => coordinateCombination z (fun j => coordinateCombination z (w j))
  have hW (z : SpatialCoordinates d) : ‖W z‖ ≤ coordinateSize z^2*B := by
    have he := coordinateCombination_norm_le z (fun j => coordinateCombination z (w j))
      (fun j => coordinateCombination_norm_le z (w j) (hb j))
    simpa only [W,pow_two,mul_assoc] using he
  have hbound (z : SpatialCoordinates d) (hz : ‖z-p.direction‖ ≤ 1) :
      bochnerL2Norm ν (V z) ≤ 2/t*‖u‖+t*(coordinateSize z^2*B) := by
    exact (weak_cone_interpolation hS p hz ht hheight
      (weak_coordinateCombination hfirst z) (weak_coordinateCombination_second hsecond z)).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hW z) ht.le))
  have ha := hbound a (by simp [a])
  have hbn : ‖b-p.direction‖ ≤ 1 := by
    simp only [b,add_sub_cancel_left]
    exact le_of_eq ((EuclideanSpace.basisFun (Fin d) ℝ).norm_eq_one i)
  have hb' := hbound b hbn
  have hv : V b - V a = v i := by
    simp only [V,b,a,coordinateCombination_add,coordinateCombination_basis,add_sub_cancel_left]
  have hmeas (z : SpatialCoordinates d) : MemLp (V z : SpatialCoordinates d → ℝ) 2 ν :=
    (Lp.memLp (V z)).mono_measure (Measure.restrict_mono inter_subset_right le_rfl)
  have he := bochnerL2Norm_sub (hmeas b) (hmeas a)
  have heq : (fun x => V b x-V a x) =ᵐ[ν] (v i : SpatialCoordinates d → ℝ) := by
    have he' := (Lp.coeFn_sub (V b) (V a)).symm
    rw [hv] at he'
    exact he'.filter_mono (ae_mono (Measure.restrict_mono inter_subset_right le_rfl))
  rw [bochnerL2Norm_congr_ae heq] at he
  have hc : coordinateSize a^2+coordinateSize b^2 ≤ coneCoordinateConstant p := by
    exact add_le_add le_rfl (Finset.single_le_sum (fun j _ => sq_nonneg
      (coordinateSize (p.direction+EuclideanSpace.basisFun (Fin d) ℝ j))) (Finset.mem_univ i))
  have hc' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hB) ht.le
  change bochnerL2Norm ν (v i) ≤ _
  have hfour : 4/t = 2/t+2/t := by ring
  rw [hfour]
  nlinarith
end Carleman
