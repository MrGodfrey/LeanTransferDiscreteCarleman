module

public import Carleman.Weights.IntrinsicSmoothClosure
public import Carleman.Spatial.RealL2Integral

/-! Dimension-only comparison between the actual multilinear operator norm
and the full finite coordinate array. These are actual fixed linear maps,
not mesh-dependent finite-dimensional norm equivalences. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman
variable {d k : ℕ}

def tensorCoordinateBound (d k : ℕ) : ℝ := ‖tensorReconstruction (d := d) (k := k)‖+1

theorem tensorCoordinateBound_pos : 0 < tensorCoordinateBound d k := by
  unfold tensorCoordinateBound
  positivity

theorem tensor_norm_sq_le_coordinate_sum (A : SpatialCoordinates d [×k]→L[ℝ] ℝ) :
    ‖A‖^2 ≤ (tensorCoordinateBound d k)^2*
      ∑ v : Fin k → Fin d, (tensorCoordinates A v)^2 := by
  let S := ∑ v : Fin k → Fin d, (tensorCoordinates A v)^2
  have hS : 0 ≤ S := Finset.sum_nonneg fun v _ => sq_nonneg _
  have hc : ‖tensorCoordinates A‖ ≤ Real.sqrt S := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg S)).mpr
    intro v
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg S)).mp
    rw [Real.sq_sqrt hS,Real.norm_eq_abs,sq_abs]
    exact Finset.single_le_sum (fun w _ => sq_nonneg (tensorCoordinates A w)) (Finset.mem_univ v)
  have hR : 0 ≤ ‖tensorReconstruction (d := d) (k := k)‖ :=
    norm_nonneg (tensorReconstruction (d := d) (k := k))
  have he : ‖A‖ ≤ tensorCoordinateBound d k*Real.sqrt S := by
    calc
      _ = ‖tensorReconstruction (tensorCoordinates A)‖ := by rw [tensorReconstruction_coordinates]
      _ ≤ ‖tensorReconstruction (d := d) (k := k)‖*‖tensorCoordinates A‖ := tensorReconstruction.le_opNorm _
      _ ≤ ‖tensorReconstruction (d := d) (k := k)‖*Real.sqrt S := mul_le_mul_of_nonneg_left hc hR
      _ ≤ tensorCoordinateBound d k*Real.sqrt S :=
        mul_le_mul_of_nonneg_right (by dsimp only [tensorCoordinateBound]; linarith) (Real.sqrt_nonneg S)
  have hs := (sq_le_sq₀ (norm_nonneg A)
    (mul_nonneg tensorCoordinateBound_pos.le (Real.sqrt_nonneg S))).mpr he
  simpa only [mul_pow,Real.sq_sqrt hS] using hs

end Carleman
