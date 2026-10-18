module

public import Carleman.Spatial.AffineChangeVolume

/-! Volume control along the nondegenerate half of a segment in a convex
cell. The bound retains the actual Jacobian and actual cell integral. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem integral_comp_scalar_affine (K : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) {r : ℝ} (hr : 0 < r) (b : SpatialCoordinates d) :
    (∫ x in K, f (r • x+b)) =
      (r^d)⁻¹*(∫ y in (fun x => r • x+b) '' K, f y) := by
  let A := (LinearEquiv.smulOfNeZero ℝ (SpatialCoordinates d) r hr.ne').toContinuousLinearEquiv
  have hA : A.toLinearMap = r • LinearMap.id := by
    ext x
    rfl
  have hJ : affineJacobian A = r^d := by
    rw [affineJacobian,hA,LinearMap.det_smul,LinearMap.det_id,mul_one,
      abs_of_nonneg (pow_nonneg hr.le _)]
    simp only [SpatialCoordinates,finrank_euclideanSpace,Fintype.card_fin]
  have he := integral_comp_affineChange A b K f
  rw [hJ] at he
  exact he

theorem integral_convex_segment_le {K : Set (SpatialCoordinates d)} (hK : Convex ℝ K)
    {f : SpatialCoordinates d → ℝ} (hf : IntegrableOn f K)
    (hpos : 0 ≤ᵐ[volume.restrict K] f)
    {r : ℝ} (hr : 1/2 ≤ r) (hr1 : r ≤ 1)
    {y : SpatialCoordinates d} (hy : y ∈ K) :
    (∫ x in K, f (r • x+(1-r) • y)) ≤ (2:ℝ)^d*(∫ x in K, f x) := by
  have hr0 : 0 < r := by linarith
  rw [integral_comp_scalar_affine K f hr0]
  have hsub : (fun x => r • x+(1-r) • y) '' K ⊆ K := by
    rintro _ ⟨x,hx,rfl⟩
    exact hK hx hy hr0.le (sub_nonneg.mpr hr1) (by ring)
  have hi := setIntegral_mono_set hf hpos (Filter.Eventually.of_forall hsub)
  have hp : (r^d)⁻¹ ≤ (2:ℝ)^d := by
    rw [← inv_pow]
    have hi : r⁻¹ ≤ (2:ℝ) := by
      rw [← one_div]
      exact (div_le_iff₀ hr0).mpr (by linarith)
    exact pow_le_pow_left₀ (inv_nonneg.mpr hr0.le) hi d
  exact (mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (pow_nonneg hr0.le _))).trans
    (mul_le_mul_of_nonneg_right hp (integral_nonneg_of_ae hpos))

end Carleman
