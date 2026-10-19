module

public import Carleman.Spatial.WeightedCompactCell
public import Carleman.Spatial.SimplexLoadNorm

/-! Actual weighted local reconstruction and load bounds from a common
positive anchor, with constants independent of the simplex volume. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman

theorem weighted_coefficient_sq_anchor {ι : Type*} [Fintype ι] (c ω : ι → ℝ)
    (W s : ℝ) (hW : 0 < W) (hs : 0 < s) (hω : ∀ i, 0 ≤ ω i)
    (hb : ∀ i, ω i ≤ W*s ∧ s ≤ W*ω i) :
    (∑ i, (ω i*c i)^2) ≤ W^2*s^2*(∑ i, (c i)^2) ∧
    s^2*(∑ i, (c i)^2) ≤ W^2*(∑ i, (ω i*c i)^2) := by
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (hω i) (mul_nonneg hW.le hs.le)).mpr (hb i).1) (sq_nonneg (c i))
    simpa only [mul_pow,mul_assoc] using h
  · simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ hs.le (mul_nonneg hW.le (hω i))).mpr (hb i).2) (sq_nonneg (c i))
    simpa only [mul_pow,mul_assoc] using h

variable {d : ℕ} (T : Affine.Simplex ℝ (SpatialCoordinates d) d)

theorem simplexNodal_sq_lumped_bounds (c : Fin (d+1) → ℝ) :
    (volume.real (simplicialCell T.points)/(d+1:ℝ))*(∑ k, (c k)^2) ≤
      (d+2:ℝ)*(∫ x in simplicialCell T.points, (simplexNodalInterpolant T c x)^2) ∧
    (∫ x in simplicialCell T.points, (simplexNodalInterpolant T c x)^2) ≤
      (volume.real (simplicialCell T.points)/(d+1:ℝ))*(∑ k, (c k)^2) := by
  have h := integral_simplexNodalInterpolant_sq_bounds T c
  have hd1 : (d+1:ℝ) ≠ 0 := by positivity
  have hd2 : (d+2:ℝ) ≠ 0 := by positivity
  constructor
  · calc
      _ = (d+2:ℝ)*(volume.real (simplicialCell T.points)/((d+1:ℝ)*(d+2))*(∑ k, (c k)^2)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h.1 (by positivity)
  · calc
      _ ≤ _ := h.2
      _ = _ := by field_simp

theorem simplex_weighted_reconstruction_bounds
    (w : BoundedMultiplier (volume.restrict (simplicialCell T.points)))
    (c ω : Fin (d+1) → ℝ) (W s : ℝ) (hW : 0 < W) (hs : 0 < s) (hω : ∀ k, 0 ≤ ω k)
    (hb : ∀ k, ω k ≤ W*s ∧ s ≤ W*ω k)
    (hw : ∀ᵐ x ∂volume.restrict (simplicialCell T.points), |w.value x| ≤ W*s ∧ s ≤ W*|w.value x|) :
    (volume.real (simplicialCell T.points)/(d+1:ℝ))*(∑ k, (ω k*c k)^2) ≤
      W^4*(d+2:ℝ)*(∫ x in simplicialCell T.points, |w.value x|^2*(simplexNodalInterpolant T c x)^2) ∧
    (∫ x in simplicialCell T.points, |w.value x|^2*(simplexNodalInterpolant T c x)^2) ≤
      W^4*(volume.real (simplicialCell T.points)/(d+1:ℝ))*(∑ k, (ω k*c k)^2) := by
  let m := volume.real (simplicialCell T.points)/(d+1:ℝ)
  let I := ∫ x in simplicialCell T.points, (simplexNodalInterpolant T c x)^2
  let J := ∫ x in simplicialCell T.points, |w.value x|^2*(simplexNodalInterpolant T c x)^2
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hc := weighted_coefficient_sq_anchor c ω W s hW hs hω hb
  have hi := simplexNodal_sq_lumped_bounds T c
  have hw' := simplex_weighted_sq_anchor T w _ (simplexNodalInterpolant T c).continuous_of_finiteDimensional W s hW hs hw
  constructor
  · calc
      _ ≤ m*(W^2*s^2*(∑ k, (c k)^2)) := mul_le_mul_of_nonneg_left hc.1 hm
      _ = W^2*s^2*(m*(∑ k, (c k)^2)) := by ring
      _ ≤ W^2*s^2*((d+2:ℝ)*I) := mul_le_mul_of_nonneg_left hi.1 (by positivity)
      _ = (W^2*(d+2:ℝ))*(s^2*I) := by ring
      _ ≤ (W^2*(d+2:ℝ))*(W^2*J) := mul_le_mul_of_nonneg_left hw'.2 (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ W^2*s^2*I := hw'.1
      _ ≤ W^2*s^2*(m*(∑ k, (c k)^2)) := mul_le_mul_of_nonneg_left hi.2 (by positivity)
      _ = W^2*m*(s^2*(∑ k, (c k)^2)) := by ring
      _ ≤ W^2*m*(W^2*(∑ k, (ω k*c k)^2)) := mul_le_mul_of_nonneg_left hc.2 (by positivity)
      _ = _ := by ring

theorem simplex_weighted_load_bound
    (w : BoundedMultiplier (volume.restrict (simplicialCell T.points)))
    (c ω : Fin (d+1) → ℝ) (W s : ℝ) (hW : 0 < W) (hs : 0 < s) (hω : ∀ k, 0 ≤ ω k)
    (hb : ∀ k, ω k ≤ W*s ∧ s ≤ W*ω k)
    (hw : ∀ᵐ x ∂volume.restrict (simplicialCell T.points), |w.value x| ≤ W*s ∧ s ≤ W*|w.value x|) :
    (∫ x in simplicialCell T.points, |w.value x|^2*(simplexLoadPolynomial T c x)^2) ≤
      W^4*(d+2:ℝ)*(volume.real (simplicialCell T.points)/(d+1:ℝ))*(∑ k, (ω k*c k)^2) := by
  let m := volume.real (simplicialCell T.points)/(d+1:ℝ)
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hc := (weighted_coefficient_sq_anchor c ω W s hW hs hω hb).2
  have hw' := (simplex_weighted_sq_anchor T w _ (simplexLoadPolynomial_continuous T c) W s hW hs hw).1
  calc
    _ ≤ W^2*s^2*(∫ x in simplicialCell T.points, (simplexLoadPolynomial T c x)^2) := hw'
    _ ≤ W^2*s^2*((d+2:ℝ)*m*(∑ k, (c k)^2)) :=
      mul_le_mul_of_nonneg_left (integral_simplexLoadPolynomial_sq_le T c) (by positivity)
    _ = (W^2*(d+2:ℝ)*m)*(s^2*(∑ k, (c k)^2)) := by ring
    _ ≤ (W^2*(d+2:ℝ)*m)*(W^2*(∑ k, (ω k*c k)^2)) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring

end Carleman
