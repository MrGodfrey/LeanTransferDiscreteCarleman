module

public import Carleman.Spatial.TensorCoordinateL2
public import Carleman.Spatial.StrongL2NormLimit

/-! Actual Hessian energy is controlled by the full finite coordinate array;
strong convergence of every coordinate gives convergence of that energy sum. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Carleman
variable {d : ℕ} {K : Set (SpatialCoordinates d)}

theorem smooth_hessian_integral_le_coordinate_sum (hK : IsCompact K)
    {f : SpatialCoordinates d → ℝ} (hf : ContDiff ℝ 2 f) :
    (∫ x in K, ‖iteratedFDeriv ℝ 2 f x‖^2) ≤
      (tensorCoordinateBound d 2)^2*∑ v : Fin 2 → Fin d, ∫ x in K, (coordinateDerivative v f x)^2 := by
  have hm (v : Fin 2 → Fin d) : MemLp (coordinateDerivative v f) 2 (volume.restrict K) :=
    continuous_memLp_compact hK ((coordinateTensorEval v).continuous.comp
      (hf.continuous_iteratedFDeriv (by simp)))
  have hb : (∫ x in K, ‖iteratedFDeriv ℝ 2 f x‖^2) ≤
      ∫ x in K, (tensorCoordinateBound d 2)^2*∑ v : Fin 2 → Fin d, (coordinateDerivative v f x)^2 := by
    apply integral_mono (((hf.continuous_iteratedFDeriv (by simp)).norm.pow 2).continuousOn.integrableOn_compact
      hK) ((integrable_finsetSum _ (fun v _ => (hm v).integrable_sq)).const_mul _)
    intro x
    exact tensor_norm_sq_le_coordinate_sum (iteratedFDeriv ℝ 2 f x)
  simpa only [integral_const_mul,integral_finsetSum _ (fun v _ => (hm v).integrable_sq)] using hb

theorem hessian_coordinate_energy_tendsto (hK : IsCompact K)
    {F : ℕ → SpatialCoordinates d → ℝ} (hF : ∀ n, ContDiff ℝ 2 (F n))
    {Z : (Fin 2 → Fin d) → SpatialCoordinates d → ℝ}
    (hZ : ∀ v, MemLp (Z v) 2 (volume.restrict K))
    (ht : ∀ v, Tendsto (fun n => bochnerL2Norm (volume.restrict K)
      (fun x => coordinateDerivative v (F n) x-Z v x)) atTop (𝓝 0)) :
    Tendsto (fun n => ∑ v : Fin 2 → Fin d, ∫ x in K, (coordinateDerivative v (F n) x)^2) atTop
      (𝓝 (∑ v : Fin 2 → Fin d, ∫ x in K, (Z v x)^2)) := by
  apply tendsto_finsetSum
  intro v _
  exact l2_square_integral_tendsto_of_error (hZ v)
    (fun n => continuous_memLp_compact hK ((coordinateTensorEval v).continuous.comp
      ((hF n).continuous_iteratedFDeriv (by simp)))) (ht v)

end Carleman
