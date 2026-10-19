module

public import Carleman.Spatial.TensorCoordinateNorm
public import Carleman.Spatial.SmoothH2PointBound

/-! Fixed-dimension tensor comparison in the actual L² norm, and a point
bound in finitely many genuine coordinate derivative L² norms. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d k : ℕ} {K : Set (SpatialCoordinates d)}

theorem tensor_norm_le_coordinate_sum (A : SpatialCoordinates d [×k]→L[ℝ] ℝ) :
    ‖A‖ ≤ tensorCoordinateBound d k * ∑ v : Fin k → Fin d, ‖tensorCoordinates A v‖ := by
  have hc : ‖tensorCoordinates A‖ ≤ ∑ v : Fin k → Fin d, ‖tensorCoordinates A v‖ := by
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mpr
    intro v
    exact Finset.single_le_sum (fun w _ => norm_nonneg (tensorCoordinates A w)) (Finset.mem_univ v)
  calc
    _ = ‖tensorReconstruction (tensorCoordinates A)‖ := by rw [tensorReconstruction_coordinates]
    _ ≤ ‖tensorReconstruction (d := d) (k := k)‖*‖tensorCoordinates A‖ := tensorReconstruction.le_opNorm _
    _ ≤ tensorCoordinateBound d k*‖tensorCoordinates A‖ :=
      mul_le_mul_of_nonneg_right (by unfold tensorCoordinateBound; linarith) (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hc tensorCoordinateBound_pos.le

theorem tensor_L2_le_coordinate_sum (hK : IsCompact K)
    {F : SpatialCoordinates d → (SpatialCoordinates d [×k]→L[ℝ] ℝ)} (hF : Continuous F) :
    bochnerL2Norm (volume.restrict K) F ≤ tensorCoordinateBound d k *
      ∑ v : Fin k → Fin d, bochnerL2Norm (volume.restrict K) (fun x => tensorCoordinates (F x) v) := by
  exact bochnerL2Norm_le_sum (continuous_memLp_compact hK hF)
    (fun v x => tensorCoordinates (F x) v)
    (fun v => continuous_memLp_compact hK ((coordinateTensorEval v).continuous.comp hF))
    tensorCoordinateBound_pos.le (Filter.Eventually.of_forall fun x => tensor_norm_le_coordinate_sum (F x))

theorem convex_smooth_h2_coordinate_point_bound (hK : IsCompact K) (hc : Convex ℝ K)
    (hvol : 0 < volume.real K) (hd : d ≤ 3)
    {f : SpatialCoordinates d → ℝ} (hf : ContDiff ℝ 2 f)
    {D : ℝ} (hD : 0 ≤ D) (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {x : SpatialCoordinates d} (hx : x ∈ K) :
    |f x| ≤ (Real.sqrt (volume.real K)/volume.real K)*
      (bochnerL2Norm (volume.restrict K) f +
        D*tensorCoordinateBound d 1*(∑ v : Fin 1 → Fin d, bochnerL2Norm (volume.restrict K) (coordinateDerivative v f)) +
        2*D^2*tensorCoordinateBound d 2*(∑ v : Fin 2 → Fin d, bochnerL2Norm (volume.restrict K) (coordinateDerivative v f))) := by
  apply (convex_smooth_h2_point_bound hK hc hvol hd hf hD hdiam hx).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have he : bochnerL2Norm (volume.restrict K) (fderiv ℝ f) =
      bochnerL2Norm (volume.restrict K) (iteratedFDeriv ℝ 1 f) := by
    rw [← bochnerL2Norm_norm _ (continuous_memLp_compact hK (hf.continuous_fderiv (by norm_num))),
      ← bochnerL2Norm_norm _ (continuous_memLp_compact hK (hf.continuous_iteratedFDeriv (by norm_num)))]
    congr 1
    funext y
    exact (norm_iteratedFDeriv_one (𝕜 := ℝ) (x := y) f).symm
  rw [he]
  have h₁ := tensor_L2_le_coordinate_sum hK (hf.continuous_iteratedFDeriv (m := 1) (by norm_num))
  have h₂ := tensor_L2_le_coordinate_sum hK (hf.continuous_iteratedFDeriv (m := 2) (by simp))
  change bochnerL2Norm (volume.restrict K) (iteratedFDeriv ℝ 1 f) ≤
    tensorCoordinateBound d 1*(∑ v : Fin 1 → Fin d, bochnerL2Norm (volume.restrict K) (coordinateDerivative v f)) at h₁
  change bochnerL2Norm (volume.restrict K) (iteratedFDeriv ℝ 2 f) ≤
    tensorCoordinateBound d 2*(∑ v : Fin 2 → Fin d, bochnerL2Norm (volume.restrict K) (coordinateDerivative v f)) at h₂
  nlinarith only [mul_le_mul_of_nonneg_left h₁ hD,mul_le_mul_of_nonneg_left h₂ (by positivity : 0 ≤ 2*D^2)]

end Carleman
