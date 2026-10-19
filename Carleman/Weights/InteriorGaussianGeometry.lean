module

public import Carleman.Weights.InteriorGaussianWeight
public import Carleman.Weights.ClosureProfile
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-! Actual geometric properties of the paper's interior Gaussian weight.
The supporting-plane sign is pointwise; no boundary integration formula is assumed. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Carleman
variable {d : ℕ}

theorem interiorCarlemanProfile_smoothOnClosure (c : SpatialCoordinates d) (l : ℝ)
    (S : Set (SpatialCoordinates d)) : SmoothOnClosure (interiorCarlemanProfile c l) S :=
  SmoothOnClosure.of_neighborhood isOpen_univ (subset_univ _)
    (interiorCarlemanProfile_contDiff c l).contDiffOn

/-- This profile has the same pointwise values on every measure, with a global bound of two. -/
def interiorSpatialProfile (ν : Measure (SpatialCoordinates d)) (c : SpatialCoordinates d)
    {l : ℝ} (hl : 0 ≤ l) : SpatialProfile ν where
  value := interiorCarlemanProfile c l
  measurable := (interiorCarlemanProfile_contDiff c l).continuous.aestronglyMeasurable
  bound := 2
  bound_nonneg := by norm_num
  bounded := Filter.Eventually.of_forall fun x => by
    obtain ⟨hlo,hhi⟩ := interiorCarlemanProfile_bounds c hl x
    exact abs_le.mpr ⟨hlo.le,by linarith⟩

theorem interiorSpatialProfile_value (ν : Measure (SpatialCoordinates d))
    (c : SpatialCoordinates d) {l : ℝ} (hl : 0 ≤ l) :
    (interiorSpatialProfile ν c hl).value = interiorCarlemanProfile c l := rfl

theorem interiorQuadratic_gradient (c x : SpatialCoordinates d) :
    gradient (interiorQuadratic c) x = (-2:ℝ) • (x-c) := by
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  convert! interiorQuadratic_hasFDerivAt c x using 1
  ext u
  simp only [InnerProductSpace.toDual_apply_apply,real_inner_smul_left,smul_apply,smul_eq_mul,
    innerSL_apply_apply]

theorem interiorQuadratic_gradient_norm_sq (c x : SpatialCoordinates d) :
    ‖gradient (interiorQuadratic c) x‖^2 = 4*‖x-c‖^2 := by
  rw [interiorQuadratic_gradient,norm_smul]
  norm_num
  ring

theorem interiorQuadratic_gradient_outside_ball (c : SpatialCoordinates d)
    {r : ℝ} (hr : 0 ≤ r) {x : SpatialCoordinates d} (hx : x ∉ Metric.ball c r) :
    4*r^2 ≤ ‖gradient (interiorQuadratic c) x‖^2 := by
  have hx' : r ≤ ‖x-c‖ := by simpa only [Metric.mem_ball,dist_eq_norm,not_lt] using hx
  rw [interiorQuadratic_gradient_norm_sq]
  nlinarith [sq_le_sq₀ hr (norm_nonneg (x-c)) |>.2 hx']

theorem exists_interiorGaussian_gradient_threshold (c : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (C : ℝ) :
    ∃ l : ℝ, 1 ≤ l ∧ ∀ x ∉ Metric.ball c r,
      2*C ≤ l*‖gradient (interiorQuadratic c) x‖^2 := by
  refine ⟨max 1 (C/(2*r^2)),le_max_left _ _,?_⟩
  intro x hx
  have hl : 0 ≤ max 1 (C/(2*r^2)) := le_trans (by norm_num) (le_max_left _ _)
  have hb := mul_le_mul_of_nonneg_left (interiorQuadratic_gradient_outside_ball c hr.le hx) hl
  have hdiv := (div_le_iff₀ (show 0 < 2*r^2 by positivity)).mp
    (le_max_right 1 (C/(2*r^2)))
  nlinarith

theorem interiorGaussian_lower_bound (c : SpatialCoordinates d) {l R : ℝ}
    (hl : 0 ≤ l) (hR : 0 ≤ R) {x : SpatialCoordinates d} (hx : ‖x-c‖ ≤ R) :
    Real.exp (-l*R^2) ≤ interiorGaussian c l x := by
  apply Real.exp_le_exp.mpr
  dsimp only [interiorQuadratic]
  have h := mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) hR).mpr hx) hl
  nlinarith

theorem interiorGaussian_supporting_normal (c : SpatialCoordinates d) {l : ℝ}
    (hl : 0 ≤ l) (x n : SpatialCoordinates d) (hn : inner ℝ (c-x) n ≤ 0) :
    fderiv ℝ (interiorGaussian c l) x n ≤ 0 := by
  rw [interiorGaussian_fderiv_apply]
  have hn' : 0 ≤ inner ℝ (x-c) n := by
    have he : c-x=-(x-c) := by abel
    rw [he,inner_neg_left] at hn
    linarith
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by nlinarith) (interiorGaussian_pos c l x).le) hn'

/-- The actual face term in the paper has the correct sign for every normal derivative. -/
theorem interiorGaussian_face_flux_nonpos {S : Set (SpatialCoordinates d)}
    {c : SpatialCoordinates d} (hc : c ∈ S) {l q : ℝ} (hl : 0 ≤ l) (hq : 0 ≤ q)
    (x n : SpatialCoordinates d) (hn : ∀ y ∈ S, inner ℝ (y-x) n ≤ 0) (a : ℝ) :
    2*q*(fderiv ℝ (interiorGaussian c l) x n)*a^2 ≤ 0 := by
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (interiorGaussian_supporting_normal c hl x n (hn c hc))) (sq_nonneg a)

end Carleman
