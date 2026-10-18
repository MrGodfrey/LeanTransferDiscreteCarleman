module

public import Carleman.Spatial.SimplexReferenceMap
public import Carleman.Spatial.MultiplierAlgebra

/-! Uniform local weighted inverse estimates on every physical simplex.
Weight comparability is explicit and all fields are actual L² classes. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman

theorem simplex_weighted_shape_inverse (n : ℕ) (κ W : ℝ) (hκ : 0 < κ) (hW : 0 < W) :
    ∃ C > (0:ℝ),
    ∀ (U : Affine.Simplex ℝ (SpatialCoordinates n) n) (a : SpatialCoordinates n)
      (r h : ℝ), 0 < r → 0 < h → Metric.ball a r ⊆ simplicialCell U.points → h ≤ κ*r →
    ∀ (w : BoundedMultiplier (volume.restrict (simplicialCell U.points))) (s : ℝ), 0 < s →
      (∀ᵐ x ∂volume.restrict (simplicialCell U.points), |w.value x| ≤ W*s ∧ s ≤ W*|w.value x|) →
    ∀ c : Fin (n+1) → ℝ,
      w.seminorm (simplexNodalGradientLp U c) ≤ (C/h)*w.seminorm (simplexNodalLp U c) := by
  obtain ⟨R,hR,hbound⟩ := simplex_shape_inverse n κ hκ
  refine ⟨W^2*R,by positivity,?_⟩
  intro U a r h hr hh hball hshape w s hs hw c
  have hu : w.seminorm (simplexNodalGradientLp U c) ≤ W*s*‖simplexNodalGradientLp U c‖ := by
    have h1 := w.seminorm_le_of_weight_le BoundedMultiplier.one (W*s) (by
      filter_upwards [hw] with x hx
      simpa only [BoundedMultiplier.one,abs_one,mul_one] using hx.1) (simplexNodalGradientLp U c)
    simpa only [BoundedMultiplier.one_seminorm] using h1
  have hl : ‖simplexNodalLp U c‖ ≤ (W/s)*w.seminorm (simplexNodalLp U c) := by
    have h1 := BoundedMultiplier.one.seminorm_le_of_weight_le w (W/s) (by
      filter_upwards [hw] with x hx
      change |(1:ℝ)| ≤ W/s*|w.value x|
      rw [abs_one,div_mul_eq_mul_div]
      exact (le_div_iff₀ hs).mpr (by simpa only [one_mul] using hx.2)) (simplexNodalLp U c)
    simpa only [BoundedMultiplier.one_seminorm] using h1
  calc
    _ ≤ W*s*‖simplexNodalGradientLp U c‖ := hu
    _ ≤ W*s*((R/h)*‖simplexNodalLp U c‖) := by
      exact mul_le_mul_of_nonneg_left (hbound U a r h hr hh hball hshape c) (by positivity)
    _ ≤ W*s*((R/h)*((W/s)*w.seminorm (simplexNodalLp U c))) := by gcongr
    _ = (W^2*R/h)*w.seminorm (simplexNodalLp U c) := by field_simp

theorem simplex_local_weighted_inverse (n : ℕ) (κ W : ℝ) (hκ : 0 < κ) (hW : 0 < W) :
    ∃ C > (0:ℝ),
    ∀ (U : Affine.Simplex ℝ (SpatialCoordinates n) n) (a : SpatialCoordinates n)
      (r h : ℝ), 0 < r → 0 < h → Metric.ball a r ⊆ simplicialCell U.points → h ≤ κ*r →
    ∀ (w : BoundedMultiplier (volume.restrict (simplicialCell U.points))) (s : ℝ), 0 < s →
      (∀ᵐ x ∂volume.restrict (simplicialCell U.points), |w.value x| ≤ W*s ∧ s ≤ W*|w.value x|) →
    ∀ (p : SpatialCoordinates n →ᵃ[ℝ] ℝ)
      (u : Lp ℝ 2 (volume.restrict (simplicialCell U.points)))
      (g : Lp (DerivativeFiber n 1) 2 (volume.restrict (simplicialCell U.points))),
      u =ᵐ[volume.restrict (simplicialCell U.points)] p →
      g =ᵐ[volume.restrict (simplicialCell U.points)] (fun x => derivativeOneFiber (fderiv ℝ p x)) →
      w.seminorm g ≤ (C/h)*w.seminorm u := by
  obtain ⟨C,hC,hbound⟩ := simplex_weighted_shape_inverse n κ W hκ hW
  refine ⟨C,hC,?_⟩
  intro U a r h hr hh hball hshape w s hs hw p u g hu hg
  let c := fun i => p (U.points i)
  have hp : simplexNodalInterpolant U c = p := simplexNodalInterpolant_reproduces U p
  have heu : u = simplexNodalLp U c := by
    apply Lp.ext
    have hn := simplexNodalLp_ae U c
    rw [hp] at hn
    exact hu.trans hn.symm
  have heg : g = simplexNodalGradientLp U c := by
    apply Lp.ext
    have hn := simplexNodalGradientLp_ae U c
    rw [hp] at hn
    exact hg.trans hn.symm
  rw [heu,heg]
  exact hbound U a r h hr hh hball hshape w s hs hw c

theorem simplexNodalLp_weighted_sq {n : ℕ} (U : Affine.Simplex ℝ (SpatialCoordinates n) n)
    (w : BoundedMultiplier (volume.restrict (simplicialCell U.points))) (c : Fin (n+1) → ℝ) :
    (w.seminorm (simplexNodalLp U c))^2 =
      ∫ x in simplicialCell U.points, |w.value x|^2*‖simplexNodalInterpolant U c x‖^2 := by
  rw [w.seminorm_sq_integral]
  apply integral_congr_ae
  filter_upwards [simplexNodalLp_ae U c] with x hx
  rw [hx]

theorem simplexNodalGradientLp_weighted_sq {n : ℕ} (U : Affine.Simplex ℝ (SpatialCoordinates n) n)
    (w : BoundedMultiplier (volume.restrict (simplicialCell U.points))) (c : Fin (n+1) → ℝ) :
    (w.seminorm (simplexNodalGradientLp U c))^2 =
      ∫ x in simplicialCell U.points,
        |w.value x|^2*‖derivativeOneFiber (fderiv ℝ (simplexNodalInterpolant U c) x)‖^2 := by
  rw [w.seminorm_sq_integral]
  apply integral_congr_ae
  filter_upwards [simplexNodalGradientLp_ae U c] with x hx
  rw [hx]

theorem simplex_weighted_inverse_integral (n : ℕ) (κ W : ℝ) (hκ : 0 < κ) (hW : 0 < W) :
    ∃ C > (0:ℝ),
    ∀ (U : Affine.Simplex ℝ (SpatialCoordinates n) n) (a : SpatialCoordinates n)
      (r h : ℝ), 0 < r → 0 < h → Metric.ball a r ⊆ simplicialCell U.points → h ≤ κ*r →
    ∀ (w : BoundedMultiplier (volume.restrict (simplicialCell U.points))) (s : ℝ), 0 < s →
      (∀ᵐ x ∂volume.restrict (simplicialCell U.points), |w.value x| ≤ W*s ∧ s ≤ W*|w.value x|) →
    ∀ p : SpatialCoordinates n →ᵃ[ℝ] ℝ,
      (∫ x in simplicialCell U.points, |w.value x|^2*‖derivativeOneFiber (fderiv ℝ p x)‖^2) ≤
      (C/h)^2 * ∫ x in simplicialCell U.points, |w.value x|^2*‖p x‖^2 := by
  obtain ⟨C,hC,hbound⟩ := simplex_weighted_shape_inverse n κ W hκ hW
  refine ⟨C,hC,?_⟩
  intro U a r h hr hh hball hshape w s hs hw p
  let c := fun i => p (U.points i)
  have hp : simplexNodalInterpolant U c = p := simplexNodalInterpolant_reproduces U p
  have hb := hbound U a r h hr hh hball hshape w s hs hw c
  have hsq := (sq_le_sq₀ (apply_nonneg _ _) (by positivity)).mpr hb
  rw [mul_pow,simplexNodalLp_weighted_sq,simplexNodalGradientLp_weighted_sq,hp] at hsq
  exact hsq

end Carleman
