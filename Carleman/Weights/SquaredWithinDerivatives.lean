module

public import Carleman.Weights.SpatialDerivatives
public import Carleman.Spatial.AffineProductDerivative

/-! Uniform actual first and second derivatives within the closed domain for
the square of the very same allowed exponential weight. -/
@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace Carleman
variable {d : ℕ} {K : Set (SpatialCoordinates d)}

def allowedSquaredWeight (ρ : SpatialCoordinates d → ℝ) (q τ η : ℝ) (x : SpatialCoordinates d) : ℝ :=
  (q^τ*Real.exp (q*(η*ρ x)))^2

theorem allowedSquaredWeight_eq (ρ : SpatialCoordinates d → ℝ) {q : ℝ} (hq : 0 < q)
    (τ η : ℝ) : allowedSquaredWeight ρ q τ η =
      (fun x => q^(2*τ)*Real.exp (q*(η*(2*ρ x)))) := by
  funext x
  have he : q*(η*(2*ρ x)) = q*(η*ρ x)+q*(η*ρ x) := by ring
  have ht : 2*τ=τ+τ := by ring
  simp only [allowedSquaredWeight,he,ht,Real.rpow_add hq,Real.exp_add]
  ring

theorem allowedSquaredWeight_contDiffOn {ρ : SpatialCoordinates d → ℝ}
    (hρ : ContDiffOn ℝ 2 ρ K) (q τ η : ℝ) :
    ContDiffOn ℝ 2 (allowedSquaredWeight ρ q τ η) K := by
  convert (((((hρ.const_smul η).const_smul q).exp).const_smul (q^τ)).pow 2) using 1
  rfl

theorem allowedSquaredWeight_hasFDerivWithinAt {ρ : SpatialCoordinates d → ℝ}
    (hρ : ContDiffOn ℝ 2 ρ K) (q τ η : ℝ) {x : SpatialCoordinates d} (hx : x ∈ K) :
    HasFDerivWithinAt (allowedSquaredWeight ρ q τ η)
      (fderivWithin ℝ (allowedSquaredWeight ρ q τ η) K x) K x :=
  ((allowedSquaredWeight_contDiffOn hρ q τ η).differentiableOn (by norm_num) x hx).hasFDerivWithinAt

theorem allowedSquaredWeight_secondWithin {ρ : SpatialCoordinates d → ℝ}
    (hρ : ContDiffOn ℝ 2 ρ K) (hK : UniqueDiffOn ℝ K) (q τ η : ℝ)
    {x : SpatialCoordinates d} (hx : x ∈ K) :
    HasFDerivWithinAt (fderivWithin ℝ (allowedSquaredWeight ρ q τ η) K)
      (fderivWithin ℝ (fderivWithin ℝ (allowedSquaredWeight ρ q τ η) K) K x) K x :=
  (((allowedSquaredWeight_contDiffOn hρ q τ η).fderivWithin hK (m := 1) (by norm_num)).differentiableOn
    (by norm_num) x hx).hasFDerivWithinAt

theorem allowedSquaredWeight_within_derivatives_uniform {ρ : SpatialCoordinates d → ℝ}
    (hρ : ContDiffOn ℝ 2 ρ K) (hK : UniqueDiffOn ℝ K) (hcompact : IsCompact K) :
    ∃ C > (0:ℝ), ∀ q : ℝ, 1 ≤ q → ∀ τ η : ℝ, |η|=1 → ∀ x ∈ K,
      ‖fderivWithin ℝ (allowedSquaredWeight ρ q τ η) K x‖ ≤ C*q*allowedSquaredWeight ρ q τ η x ∧
      ‖fderivWithin ℝ (fderivWithin ℝ (allowedSquaredWeight ρ q τ η) K) K x‖ ≤
        C*q^2*allowedSquaredWeight ρ q τ η x := by
  obtain ⟨C,hC,hbound⟩ := allowedWeight_spatial_derivatives_uniform (hρ.const_smul (2:ℝ)) hK hcompact
  refine ⟨C,hC,?_⟩
  intro q hq τ η hη x hx
  have he := allowedSquaredWeight_eq ρ (zero_lt_one.trans_le hq) τ η
  have h1 := hbound q hq (2*τ) η hη 1 (by norm_num) x hx
  have h2 := hbound q hq (2*τ) η hη 2 le_rfl x hx
  simp only [smul_eq_mul] at h1 h2
  rw [← he,norm_iteratedFDerivWithin_one _ (hK x hx),pow_one] at h1
  rw [← he] at h2
  have hid : ‖fderivWithin ℝ (fderivWithin ℝ (allowedSquaredWeight ρ q τ η) K) K x‖ =
      ‖iteratedFDerivWithin ℝ 2 (allowedSquaredWeight ρ q τ η) K x‖ := by
    rw [← norm_iteratedFDerivWithin_one _ (hK x hx),norm_iteratedFDerivWithin_fderivWithin hK hx]
  refine ⟨?_,?_⟩
  · simpa only [he] using h1
  · rw [hid]
    simpa only [he] using h2

end Carleman
