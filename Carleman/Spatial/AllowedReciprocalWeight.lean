module

public import Carleman.Spatial.NodalWeightedNorm

/-! An actual bounded reciprocal multiplier for each of the four original weights. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}
  (M : Carleman.SimplicialPartition S ι)

def gradedReciprocalWeight (inverseSize : Bool) (ℓ : ι → ℝ)
    (ρ : SpatialProfile (volume.restrict S)) (w : TimeWeight) (τ t η : ℝ) :
    BoundedMultiplier (volume.restrict S) :=
  M.gradedWeight inverseSize (fun i => (ℓ i)⁻¹) ((ρ.scaled (-η)).multiplier w (-τ) t)

theorem gradedReciprocalWeight_product_cell (hS : IsOpen S) (hc : Convex ℝ S)
    (inverseSize : Bool) (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (ρ : SpatialProfile (volume.restrict S)) (w : TimeWeight) (τ t η : ℝ) (i : ι) :
    ∀ᵐ x ∂volume.restrict (M.cell i),
      (M.gradedWeight inverseSize ℓ ((ρ.scaled η).multiplier w τ t)).value x *
        (M.gradedReciprocalWeight inverseSize ℓ ρ w τ t η).value x = 1 := by
  filter_upwards [M.gradedWeight_on_cell hS hc inverseSize ℓ ((ρ.scaled η).multiplier w τ t) i,
    M.gradedWeight_on_cell hS hc inverseSize (fun j => (ℓ j)⁻¹)
      ((ρ.scaled (-η)).multiplier w (-τ) t) i] with x hx hy
  change _ * (M.gradedWeight inverseSize (fun j => (ℓ j)⁻¹)
    ((ρ.scaled (-η)).multiplier w (-τ) t)).value x = _
  rw [hx,hy,ρ.scaled_multiplier_inverse_value]
  have hσ := (ρ.scaled_multiplier_pos η w τ t x).ne'
  have hl := (hℓ i).ne'
  cases inverseSize <;> simp [hσ,hl,mul_left_comm]

theorem gradedReciprocalWeight_product (hS : IsOpen S) (hc : Convex ℝ S)
    (inverseSize : Bool) (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (ρ : SpatialProfile (volume.restrict S)) (w : TimeWeight) (τ t η : ℝ) :
    ∀ᵐ x ∂volume.restrict S,
      (M.gradedWeight inverseSize ℓ ((ρ.scaled η).multiplier w τ t)).value x *
        (M.gradedReciprocalWeight inverseSize ℓ ρ w τ t η).value x = 1 :=
  M.ae_of_cells hS hc (M.gradedReciprocalWeight_product_cell hS hc inverseSize ℓ hℓ ρ w τ t η)

theorem gradedReciprocalWeight_cell_bound (hS : IsOpen S) (hc : Convex ℝ S)
    (inverseSize : Bool) (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (ρ : SpatialProfile (volume.restrict S)) (w : TimeWeight) (τ t η : ℝ)
    {a θ : ℝ} (ha : 0 < a) (i : ι)
    (hb : ∀ᵐ x ∂volume.restrict (M.cell i), a ≤ θ*
      |(M.gradedWeight inverseSize ℓ ((ρ.scaled η).multiplier w τ t)).value x|) :
    ∀ᵐ x ∂volume.restrict (M.cell i),
      |(M.gradedReciprocalWeight inverseSize ℓ ρ w τ t η).value x| ≤ θ/a := by
  filter_upwards [M.gradedReciprocalWeight_product_cell hS hc inverseSize ℓ hℓ ρ w τ t η i,hb]
    with x hx hb
  apply (le_div_iff₀ ha).mpr
  have he : |(M.gradedWeight inverseSize ℓ ((ρ.scaled η).multiplier w τ t)).value x| *
      |(M.gradedReciprocalWeight inverseSize ℓ ρ w τ t η).value x| = 1 := by
    rw [← abs_mul,hx,abs_one]
  have hh := mul_le_mul_of_nonneg_right hb
    (abs_nonneg ((M.gradedReciprocalWeight inverseSize ℓ ρ w τ t η).value x))
  rw [mul_assoc,he,mul_one] at hh
  simpa only [mul_comm a] using hh

end Carleman.SimplicialPartition
