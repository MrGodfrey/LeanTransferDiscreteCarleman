module

public import Carleman.Spatial.PhysicalBoxH2Affine
public import Carleman.Weights.SpatialComparison

/-! Actual allowed weights are uniformly comparable on every physical box
when hq≤1. The comparison is independent of the time period and weight power. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem coordinateBox_diameter_bound (a b : Fin d → ℝ) (hpos : ∀ i, a i < b i)
    (L : ℝ) (hL : 0 ≤ L) (hupper : ∀ i, b i-a i ≤ L)
    (x y : SpatialCoordinates d) (hx : x ∈ openCoordinateBox a b) (hy : y ∈ openCoordinateBox a b) :
    dist x y ≤ (d:ℝ)*L := by
  have he : (fun i => a i+(b i-a i))=b := by funext i; ring
  exact physicalBox_diameter_bound a (fun i => b i-a i) (fun i => sub_pos.mpr (hpos i)) L hL hupper
    x y (by rwa [he]) (by rwa [he])

theorem allowedWeight_box_comparison (ρ : SpatialProfile (volume.restrict S))
    (L κ : ℝ) (hL : 0 ≤ L) (hκ : 0 ≤ κ)
    (hρ : ∀ x ∈ closure S, ∀ y ∈ closure S, |ρ.value x-ρ.value y| ≤ L*dist x y)
    (a b : Fin d → ℝ) (hpos : ∀ i, a i < b i) (hBS : openCoordinateBox a b ⊆ S)
    (h : ℝ) (hh : 0 < h) (hupper : ∀ i, b i-a i ≤ κ*h)
    (w : TimeWeight) (τ t η : ℝ) (hη : |η|=1) (hm : h*w.q t ≤ 1)
    {x y : SpatialCoordinates d} (hx : x ∈ openCoordinateBox a b) (hy : y ∈ openCoordinateBox a b) :
    |((ρ.scaled η).multiplier w τ t).value x| ≤
        Real.exp (L*(d:ℝ)*κ)*((ρ.scaled η).multiplier w τ t).value y ∧
      ((ρ.scaled η).multiplier w τ t).value y ≤
        Real.exp (L*(d:ℝ)*κ)*|((ρ.scaled η).multiplier w τ t).value x| := by
  have hb : |ρ.value x-ρ.value y| ≤ L*((d:ℝ)*(κ*h)) :=
    (hρ x (subset_closure (hBS hx)) y (subset_closure (hBS hy))).trans
      (mul_le_mul_of_nonneg_left (coordinateBox_diameter_bound a b hpos (κ*h)
        (mul_nonneg hκ hh.le) hupper x y hx hy) hL)
  have he : Real.exp ((L*((d:ℝ)*(κ*h)))*w.q t) ≤ Real.exp (L*(d:ℝ)*κ) := by
    apply Real.exp_le_exp.mpr
    calc
      _ = (L*(d:ℝ)*κ)*(h*w.q t) := by ring
      _ ≤ (L*(d:ℝ)*κ)*1 := mul_le_mul_of_nonneg_left hm (by positivity)
      _ = _ := mul_one _
  rw [abs_of_pos (ρ.scaled_multiplier_pos η w τ t x)]
  constructor
  · exact (ρ.scaled_multiplier_spatial_le η hη w τ t hb).trans
      (mul_le_mul_of_nonneg_right he (ρ.scaled_multiplier_pos η w τ t y).le)
  · have hb' : |ρ.value y-ρ.value x| ≤ L*((d:ℝ)*(κ*h)) := by simpa only [abs_sub_comm] using hb
    exact (ρ.scaled_multiplier_spatial_le η hη w τ t hb').trans
      (mul_le_mul_of_nonneg_right he (ρ.scaled_multiplier_pos η w τ t x).le)

end Carleman
