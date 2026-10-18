module

public import Carleman.Transfer.SpatialConsistency
public import Carleman.Continuous.TimeAdjoint

/-! Section 4's complete periodic duality identity with nonorthogonal mass
transfer. The final three terms are the terms needed for the a₀, a_E² and
stiffness-defect estimates. No approximation or error inequality is assumed. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman
namespace Orientation
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem pairing_difference_opposite (s : Orientation) (g : TimeGrid)
    (u v : g.Sequence H) :
    g.pairing (s.difference g u) v = g.pairing u (s.opposite.difference g v) := by
  cases s
  · exact g.pairing_dPlus u v
  · exact g.pairing_dMinus u v

end Orientation
namespace Reconstruction
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  {V : Submodule ℝ H} (r : Reconstruction V X)

theorem spatial_complete_identity (g : TimeGrid) (s : Orientation)
    (a : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (ha : ∀ v w, a v w = a w v)
    (A : X →ₗ[ℝ] X) (defect : X →ₗ[ℝ] X →ₗ[ℝ] ℝ)
    (hA : ∀ z v, inner ℝ (A z) v = a (r.R z) (r.R v) + defect z v)
    (μ : g.Sequence ℝ) (f k : g.Sequence H) (u Y : g.Sequence V) (z : g.Sequence X)
    (hu : ∀ i v, inner ℝ (s.difference g (fun j => (u j : H)) i) (v : H) +
      spatialForm a (μ i) (u i) v = inner ℝ (f i) (v : H))
    (hz : ∀ i, s.difference g z i + A (z i) + μ i • r.G (z i) = r.J (f i))
    (hY : ∀ i v, inner ℝ (s.opposite.difference g (fun j => (Y j : H)) i) (v : H) +
      spatialForm a (μ i) (Y i) v = inner ℝ (k i) (v : H)) :
    g.pairing (fun i => (u i : H) - r.RH (z i)) k =
      g.dt * ∑ i,
        (inner ℝ (s.difference g (fun j => (u j : H)) i)
          ((Y i - r.Q (Y i : H) : V) : H) +
        spatialForm a (μ i) (u i - r.R (z i)) (Y i - r.Q (Y i : H)) +
        defect (z i) (r.J (Y i : H))) := by
  let e : g.Sequence V := fun i => u i - r.R (z i)
  have hy (i : g.Index) : inner ℝ (e i : H) (k i) =
      inner ℝ (e i : H) (s.opposite.difference g (fun j => (Y j : H)) i) +
      spatialForm a (μ i) (e i) (Y i) := by
    have he := hY i (e i)
    have hs : spatialForm a (μ i) (Y i) (e i) = spatialForm a (μ i) (e i) (Y i) := by
      rw [spatialForm, spatialForm, ha, real_inner_comm (Y i : H)]
    rw [hs, real_inner_comm _ (e i : H), real_inner_comm (k i) (e i : H)] at he
    exact he.symm
  calc
    _ = g.pairing (fun i => (e i : H))
          (s.opposite.difference g (fun i => (Y i : H))) +
        g.dt * ∑ i, spatialForm a (μ i) (e i) (Y i) := by
      change g.pairing (fun i => (e i : H)) k = _
      simp only [TimeGrid.pairing, hy, Finset.sum_add_distrib, mul_add]
    _ = g.pairing (s.difference g (fun i => (e i : H))) (fun i => (Y i : H)) +
        g.dt * ∑ i, spatialForm a (μ i) (e i) (Y i) := by
      rw [s.pairing_difference_opposite]
    _ = _ := by
      rw [TimeGrid.pairing, ← mul_add, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact r.spatial_consistency_identity g s a A defect hA μ f u z hu hz i (Y i)

/-- The actual squared weighted L² norm appears when the dual load is W²e.
For the manuscript, W is multiplication by the allowed spatial weight. -/
theorem spatial_weighted_duality (g : TimeGrid) (s : Orientation)
    (a : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (ha : ∀ v w, a v w = a w v)
    (A : X →ₗ[ℝ] X) (defect : X →ₗ[ℝ] X →ₗ[ℝ] ℝ)
    (hA : ∀ z v, inner ℝ (A z) v = a (r.R z) (r.R v) + defect z v)
    (μ : g.Sequence ℝ) (f : g.Sequence H) (u Y : g.Sequence V) (z : g.Sequence X)
    (W : g.Index → H →ₗ[ℝ] H)
    (hW : ∀ i v w, inner ℝ v (W i w) = inner ℝ (W i v) w)
    (hu : ∀ i v, inner ℝ (s.difference g (fun j => (u j : H)) i) (v : H) +
      spatialForm a (μ i) (u i) v = inner ℝ (f i) (v : H))
    (hz : ∀ i, s.difference g z i + A (z i) + μ i • r.G (z i) = r.J (f i))
    (hY : ∀ i v, inner ℝ (s.opposite.difference g (fun j => (Y j : H)) i) (v : H) +
      spatialForm a (μ i) (Y i) v =
        inner ℝ (W i (W i ((u i : H) - r.RH (z i)))) (v : H)) :
    g.dt * ∑ i, ‖W i ((u i : H) - r.RH (z i))‖^2 =
      g.dt * ∑ i,
        (inner ℝ (s.difference g (fun j => (u j : H)) i)
          ((Y i - r.Q (Y i : H) : V) : H) +
        spatialForm a (μ i) (u i - r.R (z i)) (Y i - r.Q (Y i : H)) +
        defect (z i) (r.J (Y i : H))) := by
  have he := r.spatial_complete_identity g s a ha A defect hA μ f
    (fun i => W i (W i ((u i : H) - r.RH (z i)))) u Y z hu hz hY
  simpa only [TimeGrid.pairing, hW, real_inner_self_eq_norm_sq] using he

end Reconstruction
end Carleman
