module

public import Carleman.Weights.FullNodalWeakNorms

/-! The original lower comparison c h_K ≤ ℓ_K converts the local h_K⁴
value error into a uniform h² inverse-scale weighted error. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman

theorem inverseScale_diameter_four_bound {c ℓ k h : ℝ}
    (hc : 0 < c) (hℓ : 0 < ℓ) (hk : 0 ≤ k) (hkh : k ≤ h) (hscale : c*k ≤ ℓ) :
    (ℓ⁻¹)^2*k^4 ≤ (c⁻¹)^2*h^2 := by
  have hkℓ : k ≤ ℓ/c := (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hscale)
  have hratio : k/ℓ ≤ c⁻¹ := (div_le_iff₀ hℓ).mpr (by simpa only [div_eq_mul_inv,mul_comm] using hkℓ)
  have hs : (k/ℓ)^2 ≤ (c⁻¹)^2 :=
    (sq_le_sq₀ (div_nonneg hk hℓ.le) (inv_nonneg.mpr hc.le)).mpr hratio
  calc
    _ = (k/ℓ)^2*k^2 := by rw [div_eq_mul_inv]; ring
    _ ≤ (c⁻¹)^2*h^2 := mul_le_mul hs (pow_le_pow_left₀ hk hkh 2) (sq_nonneg _) (sq_nonneg _)

namespace SimplicialPartition
variable {d : ℕ} {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}
  (M : SimplicialPartition S ι)

theorem inverseWeight_residual_sq_sum (hS : IsOpen S) (hc : Convex ℝ S)
    (ℓ : ι → ℝ) (ρ : SpatialProfile (volume.restrict S)) (w : TimeWeight) (τ t η : ℝ)
    (f : SpatialCoordinates d → ℝ) (e : Lp ℝ 2 (volume.restrict S))
    (he : e =ᵐ[volume.restrict S] M.nodalProductResidual (allowedSquaredWeight ρ.value (w.q t) τ η) f) :
    ((M.inverseWeight ℓ ((ρ.scaled (-η)).multiplier w (-τ) t)).seminorm e)^2 =
      ∑ i, ((ℓ i)⁻¹)^2*(∫ x in M.cell i,
        (M.nodalProductResidual (allowedSquaredWeight ρ.value (w.q t) τ η) f x)^2/
          allowedSquaredWeight ρ.value (w.q t) τ η x) := by
  rw [M.inverseWeight_sq_sum hS hc]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply integral_congr_ae
  filter_upwards [he.filter_mono (ae_mono (M.cell_measure_le_domain hS hc i))] with x hx
  rw [hx,ρ.scaled_multiplier_inverse_value,allowedSquaredWeight_multiplier_value,Real.norm_eq_abs]
  simp only [abs_inv,inv_pow,sq_abs,div_eq_mul_inv,mul_comm]

end SimplicialPartition
end Carleman
