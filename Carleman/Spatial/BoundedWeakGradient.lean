module

public import Carleman.Spatial.FullSpaceInterpolation
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.MetricSpace.Lipschitz

/-! Actual bounded weak coordinate derivatives supply a Lipschitz representative,
via genuine smooth convolution, its a.e. limit, and real Lipschitz extension. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Convolution Topology NNReal
namespace Carleman
variable {d : ℕ}

theorem SpatialTest.convolution_ae_norm_bound
    (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hκ : ∀ x, 0 ≤ κ.value x) (hunit : ∫ x, κ.value x = 1)
    (v : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) {B : ℝ}
    (hv : ∀ᵐ x ∂volume, ‖v x‖ ≤ B) (x : SpatialCoordinates d) :
    ‖(v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) x‖ ≤ B := by
  have hk : Integrable (fun y => κ.value (x-y)) volume :=
    (κ.reflected x).smooth.continuous.integrable_of_hasCompactSupport (κ.reflected x).compact
  calc
    _ ≤ ∫ y, κ.value (x-y)*B := by
      apply norm_integral_le_of_norm_le (hk.mul_const B)
      filter_upwards [hv] with y hy
      change ‖v y*κ.value (x-y)‖ ≤ _
      rw [norm_mul,Real.norm_eq_abs (κ.value (x-y)),abs_of_nonneg (hκ (x-y))]
      exact (mul_le_mul_of_nonneg_right hy (hκ (x-y))).trans_eq (mul_comm _ _)
    _ = B := by rw [integral_mul_const,integral_sub_left_eq_self,hunit,one_mul]

theorem spatialLinearMap_norm_of_basis_bound (A : SpatialCoordinates d →L[ℝ] ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ i : Fin d, ‖A (EuclideanSpace.basisFun (Fin d) ℝ i)‖ ≤ B) :
    ‖A‖ ≤ d*B := by
  apply A.opNorm_le_bound (mul_nonneg (Nat.cast_nonneg _) hB)
  intro x
  have he : A x = ∑ i : Fin d, x i*A (EuclideanSpace.basisFun (Fin d) ℝ i) := by
    nth_rw 1 [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x]
    simp only [map_sum,map_smul,EuclideanSpace.basisFun_repr,smul_eq_mul]
  rw [he]
  calc
    _ ≤ ∑ i : Fin d, ‖x i*A (EuclideanSpace.basisFun (Fin d) ℝ i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin d, ‖x‖*B := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul (PiLp.norm_apply_le x i) (hb i) (norm_nonneg _) (norm_nonneg _)
    _ = d*B*‖x‖ := by simp; ring

theorem convolution_lipschitz_of_bounded_weak_derivatives
    (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hκ : ∀ x, 0 ≤ κ.value x) (hunit : ∫ x, κ.value x = 1)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))
    (v : Fin d → Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))
    (hv : ∀ i, IsWeakSpatialDerivative volume univ (EuclideanSpace.basisFun (Fin d) ℝ i) u (v i))
    (B : ℝ≥0) (hb : ∀ i, ∀ᵐ x ∂volume, ‖v i x‖ ≤ B) :
    LipschitzWith (d*B) (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) := by
  apply lipschitzWith_of_nnnorm_fderiv_le ((κ.smooth_convolution u).differentiable (by simp))
  intro x
  change ‖fderiv ℝ (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) x‖ ≤ (d:ℝ)*B
  apply spatialLinearMap_norm_of_basis_bound _ B.property
  intro i
  rw [(hv i).fderiv_convolution]
  exact κ.convolution_ae_norm_bound hκ hunit (v i) (hb i) x

theorem exists_lipschitzRepresentative_of_bounded_weak_derivatives
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))
    (v : Fin d → Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))
    (hv : ∀ i, IsWeakSpatialDerivative volume univ (EuclideanSpace.basisFun (Fin d) ℝ i) u (v i))
    (B : ℝ≥0) (hb : ∀ i, ∀ᵐ x ∂volume, ‖v i x‖ ≤ B) :
    ∃ f : SpatialCoordinates d → ℝ, LipschitzWith (d*B) f ∧ u =ᵐ[volume] f := by
  let F := fun n => u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (spatialMollifier d n).value
  let A := {x | Tendsto (fun n => F n x) atTop (𝓝 (u x))}
  have hA : ∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)), x ∈ A := spatialMollifier_converges u
  have hF (n : ℕ) : LipschitzWith (d*B) (F n) :=
    convolution_lipschitz_of_bounded_weak_derivatives (spatialMollifier d n)
      (spatialMollifier_nonneg n) (spatialMollifier_integral n) u v hv B hb
  have hLip : LipschitzOnWith (d*B) u A := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    exact le_of_tendsto (hx.dist hy) (Filter.Eventually.of_forall (fun n => (hF n).dist_le_mul x y))
  obtain ⟨f,hf,he⟩ := hLip.extend_real
  refine ⟨f,hf,?_⟩
  filter_upwards [hA] with x hx
  exact he hx

end Carleman
