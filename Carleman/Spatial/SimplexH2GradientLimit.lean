module

public import Carleman.Spatial.SimplexNodalDerivativeLimit
public import Carleman.Spatial.L2ConstantShiftLimit

/-! Strong convergence of the actual first and second derivatives transfers
the smooth nodal gradient bound to the complete weak coordinate array. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Carleman
variable {d : ℕ}

theorem simplexNodal_h2_gradient_integral_of_limit
    (T : Affine.Simplex ℝ (SpatialCoordinates d) d) (hd : d ≤ 3)
    {f : SpatialCoordinates d → ℝ} {F : ℕ → SpatialCoordinates d → ℝ}
    (hF : ∀ n, ContDiff ℝ 2 (F n))
    (hl : ∀ i, Tendsto (fun n => F n (T.points i)) atTop (𝓝 (f (T.points i))))
    {G : Fin d → SpatialCoordinates d → ℝ}
    (hG : ∀ i, MemLp (G i) 2 (volume.restrict (simplicialCell T.points)))
    (ht₁ : ∀ i, Tendsto (fun n => bochnerL2Norm (volume.restrict (simplicialCell T.points))
      (fun x => fderiv ℝ (F n) x (EuclideanSpace.basisFun (Fin d) ℝ i)-G i x)) atTop (𝓝 0))
    {Z : (Fin 2 → Fin d) → SpatialCoordinates d → ℝ}
    (hZ : ∀ v, MemLp (Z v) 2 (volume.restrict (simplicialCell T.points)))
    (ht₂ : ∀ v, Tendsto (fun n => bochnerL2Norm (volume.restrict (simplicialCell T.points))
      (fun x => coordinateDerivative v (F n) x-Z v x)) atTop (𝓝 0))
    {a : SpatialCoordinates d} {r D κ : ℝ} (hr : 0 < r) (hD : 0 ≤ D)
    (hball : Metric.ball a r ⊆ simplicialCell T.points) (hshape : D ≤ κ*r)
    (hdiam : ∀ x ∈ simplicialCell T.points, ∀ y ∈ simplicialCell T.points, dist x y ≤ D) :
    (∑ i : Fin d, ∫ x in simplicialCell T.points,
      (G i x-affineScalarDerivative (simplexNodalInterpolant T (fun j => f (T.points j)))
        (EuclideanSpace.basisFun (Fin d) ℝ i))^2) ≤
      ((2:ℝ)^d*(d:ℝ)+128*κ^2*‖derivativeOneFiber (d := d)‖^2)*D^2*
        (tensorCoordinateBound d 2)^2*∑ v : Fin 2 → Fin d,
          ∫ x in simplicialCell T.points, (Z v x)^2 := by
  let K := simplicialCell T.points
  have hK : IsCompact K := simplicialCell_compact T.points
  let : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_ne_top.lt_top⟩
  let A := fun n => affineScalarDerivative (simplexNodalInterpolant T (fun i => F n (T.points i)))
  let B := affineScalarDerivative (simplexNodalInterpolant T (fun i => f (T.points i)))
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  let q := ((2:ℝ)^d*(d:ℝ)+128*κ^2*‖derivativeOneFiber (d := d)‖^2)*D^2
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hg (n : ℕ) (i : Fin d) : MemLp (fun x => fderiv ℝ (F n) x (e i)) 2 (volume.restrict K) :=
    continuous_memLp_compact hK (((hF n).continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hA : Tendsto A atTop (𝓝 B) := simplexNodalDerivative_tendsto T hl
  have hE : Tendsto (fun n => ∑ i : Fin d, ∫ x in K, (fderiv ℝ (F n) x (e i)-A n (e i))^2)
      atTop (𝓝 (∑ i : Fin d, ∫ x in K, (G i x-B (e i))^2)) := by
    apply tendsto_finsetSum
    intro i _
    exact l2_square_integral_tendsto_of_error ((hG i).sub (memLp_const _))
      (fun n => (hg n i).sub (memLp_const _))
      (l2_error_sub_constant_tendsto (hG i) (fun n => hg n i) (ht₁ i)
        ((ContinuousLinearMap.apply ℝ ℝ (e i)).continuous.continuousAt.tendsto.comp hA))
  have hH := (hessian_coordinate_energy_tendsto hK hF hZ ht₂).const_mul
    (q*(tensorCoordinateBound d 2)^2)
  apply le_of_tendsto_of_tendsto' hE hH
  intro n
  have hs := simplexNodal_smooth_h2_gradient_integral T hd (hF n) hr hD hball hshape hdiam
  have hid : (∫ x in K, ‖derivativeOneFiber (fderiv ℝ (F n) x-A n)‖^2) =
      ∑ i : Fin d, ∫ x in K, (fderiv ℝ (F n) x (e i)-A n (e i))^2 := by
    simp_rw [derivativeOneFiber_norm_sq,sub_apply]
    exact integral_finsetSum _ (fun i _ => ((hg n i).sub (memLp_const _)).integrable_sq)
  change (∫ x in K, ‖derivativeOneFiber (fderiv ℝ (F n) x-A n)‖^2) ≤
    q*(∫ x in K, ‖iteratedFDeriv ℝ 2 (F n) x‖^2) at hs
  rw [hid] at hs
  exact hs.trans ((mul_le_mul_of_nonneg_left (smooth_hessian_integral_le_coordinate_sum hK (hF n)) hq).trans_eq (by ring))

end Carleman
