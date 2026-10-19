module

public import Carleman.Spatial.InwardMollifierSequence
public import Carleman.Spatial.InwardApproximationLimit
public import Carleman.Spatial.WeakH2LocalContinuous

/-! The actual smooth inward mollifications, their true derivative identities,
and strong L² convergence for arbitrary original full-space L² inputs. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology Convolution ContDiff
namespace Carleman
variable {d : ℕ}

def inwardMollification (a : SpatialCoordinates d) (φ : ℕ → ℕ)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) (n : ℕ) : SpatialCoordinates d → ℝ :=
  inwardPullback a n (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (spatialMollifier d (φ n)).value)

theorem inwardMollification_smooth (a : SpatialCoordinates d) (φ : ℕ → ℕ)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) (n : ℕ) :
    ContDiff ℝ ∞ (inwardMollification a φ u n) :=
  inwardPullback_contDiff ((spatialMollifier d (φ n)).smooth_convolution u) a n

theorem inwardMollification_scaled_L2_error_tendsto (a : SpatialCoordinates d)
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) (k : ℕ)
    (K : Set (SpatialCoordinates d)) :
    Tendsto (fun n => bochnerL2Norm (volume.restrict K)
      (fun x => (inwardRatio n)^k*inwardMollification a φ u n x-u x)) atTop (𝓝 0) := by
  have hm (n : ℕ) := ((spatialMollifier d (φ n)).convolution_right_memLp_norm_le
    (spatialMollifier_nonneg (φ n)) (spatialMollifier_integral (φ n)) u).1
  have ht := inwardPullback_scaled_L2_error_tendsto a k (Lp.memLp u) hm
    ((spatialMollifier_L2_error_tendsto u).comp hφ)
  apply squeeze_zero (fun n => bochnerL2Norm_nonneg _) _ ht
  intro n
  have hmem := ((inwardPullback_memLp a n (hm n)).const_mul ((inwardRatio n)^k)).sub (Lp.memLp u)
  exact ENNReal.toReal_mono hmem.ne (eLpNorm_mono_measure _ Measure.restrict_le_self)

theorem IsWeakSpatialDerivative.coordinate_one_inwardMollification
    {S : Set (SpatialCoordinates d)}
    {u v : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))} {i : Fin d}
    (huv : IsWeakSpatialDerivative volume S (EuclideanSpace.basisFun (Fin d) ℝ i) u v)
    (a : SpatialCoordinates d) (φ : ℕ → ℕ) (n : ℕ) (x : SpatialCoordinates d)
    (hinside : ∀ y ∈ tsupport (spatialMollifier d (φ n)).value,
      inwardRatio n • x+(1-inwardRatio n) • a-y ∈ S) :
    coordinateDerivative (fun _ : Fin 1 => i) (inwardMollification a φ u n) x =
      inwardRatio n*inwardMollification a φ v n x := by
  change coordinateDerivative (fun _ : Fin 1 => i)
    (inwardPullback a n (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (spatialMollifier d (φ n)).value)) x=_
  rw [coordinateDerivative_inwardPullback ((spatialMollifier d (φ n)).smooth_convolution u |>.of_le (by simp))]
  simp only [pow_one,inwardPullback,coordinateDerivative_one]
  rw [huv.fderiv_convolution_local (spatialMollifier d (φ n)) _ hinside]
  rfl

theorem IsWeakSpatialDerivative.coordinate_two_inwardMollification
    {S : Set (SpatialCoordinates d)}
    {u v z : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))} {i j : Fin d}
    (huv : IsWeakSpatialDerivative volume S (EuclideanSpace.basisFun (Fin d) ℝ i) u v)
    (hvz : IsWeakSpatialDerivative volume S (EuclideanSpace.basisFun (Fin d) ℝ j) v z)
    (a : SpatialCoordinates d) (φ : ℕ → ℕ) (n : ℕ) (x : SpatialCoordinates d)
    (hinside : ∀ y ∈ tsupport (spatialMollifier d (φ n)).value,
      inwardRatio n • x+(1-inwardRatio n) • a-y ∈ S) :
    coordinateDerivative ![i,j] (inwardMollification a φ u n) x =
      (inwardRatio n)^2*inwardMollification a φ z n x := by
  change coordinateDerivative ![i,j]
    (inwardPullback a n (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (spatialMollifier d (φ n)).value)) x=_
  rw [coordinateDerivative_inwardPullback ((spatialMollifier d (φ n)).smooth_convolution u |>.of_le (by simp))]
  simp only [inwardPullback,coordinateDerivative_two,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [huv.second_tensor_convolution_local hvz (spatialMollifier d (φ n)) _ hinside]
  rfl

end Carleman
