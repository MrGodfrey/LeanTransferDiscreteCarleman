module

public import Carleman.Spatial.DomainConvolution
public import Carleman.Spatial.MollifiedInterpolation
public import Carleman.Spatial.RealL2Integral
public import Carleman.Spatial.ConvexSmoothPoincare
public import Mathlib.Analysis.InnerProductSpace.Dual

/-! The actual derivative energy of a local convolution is controlled by
the original weak coordinate derivatives. Zero extension is only L² data;
the weak identity is used exclusively at points with a domain margin. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped Convolution ContDiff
namespace Carleman
variable {d : ℕ} {S K : Set (SpatialCoordinates d)}

theorem spatialLinearMap_norm_sq (A : SpatialCoordinates d →L[ℝ] ℝ) :
    ‖A‖^2=∑ i : Fin d, (A (EuclideanSpace.basisFun (Fin d) ℝ i))^2 :=
  (EuclideanSpace.basisFun (Fin d) ℝ).norm_dual A

theorem mollified_gradient_energy_le (hK : MeasurableSet K)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))
    (v : Fin d → Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))
    (hv : ∀ i, IsWeakSpatialDerivative volume S (EuclideanSpace.basisFun (Fin d) ℝ i) u (v i))
    (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hκ : ∀ x, 0 ≤ κ.value x) (hunit : ∫ x, κ.value x = 1)
    (hinside : ∀ x ∈ K, ∀ y ∈ tsupport κ.value, x-y ∈ S) :
    (∫ x in K, ‖fderiv ℝ (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) x‖^2) ≤
      ∑ i : Fin d, ‖v i‖^2 := by
  let V := fun i => v i ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value
  have hm (i : Fin d) : MemLp (V i) 2 volume ∧ bochnerL2Norm volume (V i) ≤ ‖v i‖ :=
    κ.convolution_right_memLp_norm_le hκ hunit (v i)
  have he : (∫ x in K, ‖fderiv ℝ (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) x‖^2)=
      ∫ x in K, ∑ i : Fin d, (V i x)^2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hK] with x hx
    rw [spatialLinearMap_norm_sq]
    apply Finset.sum_congr rfl
    intro i _
    rw [(hv i).fderiv_convolution_local κ x (hinside x hx)]
  rw [he,integral_finsetSum _ (fun i _ => ((hm i).1.restrict K).integrable_sq)]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ ∫ x, (V i x)^2 := setIntegral_le_integral (hm i).1.integrable_sq
      (Filter.Eventually.of_forall fun x => sq_nonneg _)
    _ = (bochnerL2Norm volume (V i))^2 := integral_sq_eq_bochnerL2Norm_sq (hm i).1
    _ ≤ ‖v i‖^2 := (sq_le_sq₀ (bochnerL2Norm_nonneg _) (norm_nonneg _)).mpr (hm i).2

theorem convex_mollified_pairwise_bound (hK : IsCompact K) (hc : Convex ℝ K)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))
    (v : Fin d → Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))
    (hv : ∀ i, IsWeakSpatialDerivative volume S (EuclideanSpace.basisFun (Fin d) ℝ i) u (v i))
    (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hκ : ∀ x, 0 ≤ κ.value x) (hunit : ∫ x, κ.value x = 1)
    (hinside : ∀ x ∈ K, ∀ y ∈ tsupport κ.value, x-y ∈ S)
    {D : ℝ} (hD : 0 ≤ D) (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) :
    let U := u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value
    (∫ x in K, ∫ y in K, (U x-U y)^2) ≤
      (2:ℝ)^d*volume.real K*D^2*(∑ i : Fin d, ‖v i‖^2) := by
  intro U
  have he := convex_smooth_pairwise_bound hK hc ((κ.smooth_convolution u).of_le (by simp)) hD hdiam
  have hg := mollified_gradient_energy_le hK.measurableSet u v hv κ hκ hunit hinside
  exact he.trans (mul_le_mul_of_nonneg_left hg (by positivity))

end Carleman
