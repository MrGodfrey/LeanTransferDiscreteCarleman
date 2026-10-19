module

public import Carleman.Spatial.WeakDerivativeBoundedTest

/-! Uniform L² derivative bounds survive distributional limits. The
integration-by-parts identities need only hold eventually for each test,
so that inner domain exhaustions are covered without extending H² jets. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem exists_weakSpatialDerivative_of_test_limits (hS : IsOpen S)
    (u : Lp ℝ 2 (volume.restrict S)) (U V : ℕ → Lp ℝ 2 (volume.restrict S))
    (i : Fin d) {C : ℝ} (hC : 0 ≤ C)
    (hlim : ∀ φ : SpatialTest S, Tendsto
      (fun n => inner ℝ (U n) (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i)))
      atTop (𝓝 (inner ℝ u (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i)))))
    (hweak : ∀ φ : SpatialTest S, ∀ᶠ n in atTop,
      inner ℝ (U n) (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i)) =
        -inner ℝ (V n) (φ.toLp (volume.restrict S)))
    (hbound : ∀ᶠ n in atTop, ‖V n‖ ≤ C) :
    ∃ v : Lp ℝ 2 (volume.restrict S), ‖v‖ ≤ C ∧
      IsWeakSpatialDerivative (volume.restrict S) S (EuclideanSpace.basisFun (Fin d) ℝ i) u v := by
  apply exists_weakSpatialDerivative_of_test_bound hS u i hC
  intro φ
  apply le_of_tendsto (hlim φ).abs
  filter_upwards [hweak φ,hbound] with n hn hb
  rw [hn,abs_neg]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

theorem exists_weakSpatialDerivative_of_strong_limit_bounded (hS : IsOpen S)
    (u : Lp ℝ 2 (volume.restrict S)) (U V : ℕ → Lp ℝ 2 (volume.restrict S))
    (i : Fin d) {C : ℝ} (hC : 0 ≤ C)
    (hlim : Tendsto U atTop (𝓝 u))
    (hweak : ∀ n, IsWeakSpatialDerivative (volume.restrict S) S
      (EuclideanSpace.basisFun (Fin d) ℝ i) (U n) (V n))
    (hbound : ∀ᶠ n in atTop, ‖V n‖ ≤ C) :
    ∃ v : Lp ℝ 2 (volume.restrict S), ‖v‖ ≤ C ∧
      IsWeakSpatialDerivative (volume.restrict S) S (EuclideanSpace.basisFun (Fin d) ℝ i) u v :=
  exists_weakSpatialDerivative_of_test_limits hS u U V i hC
    (fun _ => hlim.inner tendsto_const_nhds)
    (fun φ => Eventually.of_forall fun n => hweak n φ) hbound

end Carleman
