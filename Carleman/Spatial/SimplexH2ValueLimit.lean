module

public import Carleman.Spatial.SmoothHessianCoordinateEnergy
public import Carleman.Spatial.SmoothH2NodalError

/-! The actual nodal value estimate passes to pointwise limits whose complete
Hessian coordinate array converges strongly in L² on the same simplex. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Carleman
variable {d : ℕ}

theorem simplexNodalInterpolant_tendsto (T : Affine.Simplex ℝ (SpatialCoordinates d) d)
    {f : SpatialCoordinates d → ℝ} {F : ℕ → SpatialCoordinates d → ℝ}
    (h : ∀ i, Tendsto (fun n => F n (T.points i)) atTop (𝓝 (f (T.points i)))) (x : SpatialCoordinates d) :
    Tendsto (fun n => simplexNodalInterpolant T (fun i => F n (T.points i)) x) atTop
      (𝓝 (simplexNodalInterpolant T (fun i => f (T.points i)) x)) := by
  simp only [simplexNodalInterpolant_apply]
  exact tendsto_finsetSum _ (fun i _ => (h i).mul_const _)

theorem simplexNodal_h2_value_integral_of_limit
    (T : Affine.Simplex ℝ (SpatialCoordinates d) d) (hd : d ≤ 3)
    {f : SpatialCoordinates d → ℝ} (hf : ContinuousOn f (simplicialCell T.points))
    {F : ℕ → SpatialCoordinates d → ℝ} (hF : ∀ n, ContDiff ℝ 2 (F n))
    (hl : ∀ x ∈ simplicialCell T.points, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    {Z : (Fin 2 → Fin d) → SpatialCoordinates d → ℝ}
    (hZ : ∀ v, MemLp (Z v) 2 (volume.restrict (simplicialCell T.points)))
    (ht : ∀ v, Tendsto (fun n => bochnerL2Norm (volume.restrict (simplicialCell T.points))
      (fun x => coordinateDerivative v (F n) x-Z v x)) atTop (𝓝 0))
    {D : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ x ∈ simplicialCell T.points, ∀ y ∈ simplicialCell T.points, dist x y ≤ D) :
    (∫ x in simplicialCell T.points, (f x-simplexNodalInterpolant T (fun i => f (T.points i)) x)^2) ≤
      16*D^4*(tensorCoordinateBound d 2)^2*
        ∑ v : Fin 2 → Fin d, ∫ x in simplicialCell T.points, (Z v x)^2 := by
  let K := simplicialCell T.points
  have hK : IsCompact K := simplicialCell_compact T.points
  have hN (g : SpatialCoordinates d → ℝ) : Continuous (simplexNodalInterpolant T (fun i => g (T.points i))) :=
    (simplexNodalInterpolant T _).continuous_of_finiteDimensional
  have hlim : ∀ᵐ x ∂volume.restrict K, Tendsto
      (fun n => F n x-simplexNodalInterpolant T (fun i => F n (T.points i)) x) atTop
      (𝓝 (f x-simplexNodalInterpolant T (fun i => f (T.points i)) x)) := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact (hl x hx).sub (simplexNodalInterpolant_tendsto T
      (fun i => hl _ (subset_convexHull ℝ _ (mem_range_self i))) x)
  apply l2_square_bound_of_ae_of_bound_tendsto
    (continuousOn_memLp_compact hK (hf.sub (hN f).continuousOn))
    (fun n => continuous_memLp_compact hK ((hF n).continuous.sub (hN (F n)))) hlim
    (mul_nonneg (by positivity) (Finset.sum_nonneg fun v _ => integral_nonneg fun x => sq_nonneg _))
    ((hessian_coordinate_energy_tendsto hK hF hZ ht).const_mul (16*D^4*(tensorCoordinateBound d 2)^2))
  intro n
  have hs := simplexNodal_smooth_h2_value_integral T hd (hF n) hD hdiam
  have hb := mul_le_mul_of_nonneg_left (smooth_hessian_integral_le_coordinate_sum hK (hF n))
    (by positivity : 0 ≤ 16*D^4)
  exact hs.trans (hb.trans_eq (by ring))

end Carleman
