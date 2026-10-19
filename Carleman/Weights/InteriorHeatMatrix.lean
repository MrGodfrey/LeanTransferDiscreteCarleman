module

public import Carleman.Weights.InteriorGaussianGeometry
public import Carleman.Spatial.SmoothLaplacianProduct

/-! The genuine Hessian and Laplacian in the spatial matrix of the heat
Carleman identity, specialized to the manuscript's Gaussian profile. -/
@[expose] public noncomputable section
open scoped ContDiff BigOperators
namespace Carleman
variable {d : ℕ}

def interiorHeatPsi (c : SpatialCoordinates d) (l q : ℝ) (x : SpatialCoordinates d) : ℝ :=
  -spatialLaplacian (fun y => q*interiorCarlemanProfile c l y) x-
    8*q*l*interiorGaussian c l x

def interiorHeatMatrix (c : SpatialCoordinates d) (l q : ℝ)
    (x u v : SpatialCoordinates d) : ℝ :=
  2*(fderiv ℝ (fun y => fderiv ℝ (fun z => q*interiorCarlemanProfile c l z) y u) x v)-
    (spatialLaplacian (fun y => q*interiorCarlemanProfile c l y) x+
      interiorHeatPsi c l q x)*inner ℝ v u

theorem interiorCarlemanProfile_scaled_hessian (c : SpatialCoordinates d) (l q : ℝ)
    (x u v : SpatialCoordinates d) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => q*interiorCarlemanProfile c l z) y u) x v =
      q*(4*l^2*interiorGaussian c l x*inner ℝ (x-c) u*inner ℝ (x-c) v-
        2*l*interiorGaussian c l x*inner ℝ v u) := by
  have hd := (interiorCarlemanProfile_contDiff c l).differentiable (by simp)
  have he : (fun y => fderiv ℝ (fun z => q*interiorCarlemanProfile c l z) y u) =
      (fun y => q*(fderiv ℝ (interiorCarlemanProfile c l) y u)) := by
    funext y
    rw [fderiv_const_mul (hd y) q]
    rfl
  rw [he]
  have hd' : ContDiff ℝ ∞ (fun y => fderiv ℝ (interiorCarlemanProfile c l) y u) := ((interiorCarlemanProfile_contDiff c l).fderiv_right (by simp)).clm_apply
    (contDiff_const (c := u))
  rw [fderiv_const_mul (hd'.differentiable (by simp) x) q]
  change q*(fderiv ℝ (fun y => fderiv ℝ (interiorCarlemanProfile c l) y u) x v) = _
  rw [interiorCarlemanProfile_hessian]

theorem interiorHeatMatrix_formula (c : SpatialCoordinates d) (l q : ℝ)
    (x u v : SpatialCoordinates d) :
    interiorHeatMatrix c l q x u v =
      4*q*l*interiorGaussian c l x*inner ℝ v u+
        2*q*l^2*interiorGaussian c l x*
          inner ℝ (gradient (interiorQuadratic c) x) u*
          inner ℝ (gradient (interiorQuadratic c) x) v := by
  simp only [interiorHeatMatrix,interiorHeatPsi,interiorCarlemanProfile_scaled_hessian,
    interiorQuadratic_gradient,real_inner_smul_left]
  ring

theorem interiorHeatMatrix_coercive (c : SpatialCoordinates d) {l q : ℝ}
    (hq : 0 ≤ q) (x u : SpatialCoordinates d) :
    4*q*l*interiorGaussian c l x*‖u‖^2 ≤ interiorHeatMatrix c l q x u u := by
  rw [interiorHeatMatrix_formula,real_inner_self_eq_norm_sq]
  have h : 0 ≤ 2*q*l^2*interiorGaussian c l x*
      (inner ℝ (gradient (interiorQuadratic c) x) u)^2 := by
    positivity [interiorGaussian_pos c l x]
  nlinarith

theorem interiorHeatMatrix_uniform_coercive (c : SpatialCoordinates d) {l R : ℝ}
    (hl : 0 < l) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 < K ∧ ∀ q : ℝ, 0 ≤ q → ∀ x : SpatialCoordinates d, ‖x-c‖ ≤ R →
      ∀ u : SpatialCoordinates d, K*q*‖u‖^2 ≤ interiorHeatMatrix c l q x u u := by
  refine ⟨4*l*Real.exp (-l*R^2),by positivity,?_⟩
  intro q hq x hx u
  have he := interiorGaussian_lower_bound c hl.le hR hx
  have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ 4*q*l*‖u‖^2 by positivity)
  have hm := interiorHeatMatrix_coercive c (l := l) hq x u
  nlinarith

/-- All spatial choices are made before the temporal parameter and test vectors. -/
theorem exists_interior_heat_weight {S W : Set (SpatialCoordinates d)}
    (hS : Bornology.IsBounded S) (hW : IsOpen W) (hne : W.Nonempty)
    (hWS : W ⊆ S) (C : ℝ) :
    ∃ (c : SpatialCoordinates d) (r l κ K : ℝ), c ∈ W ∧ 0 < r ∧ 1 ≤ l ∧
      0 < κ ∧ 0 < K ∧ Metric.closedBall c r ⊆ W ∧
      SmoothOnClosure (interiorCarlemanProfile c l) S ∧
      (∀ x, -2 < interiorCarlemanProfile c l x ∧ interiorCarlemanProfile c l x ≤ -1) ∧
      (∀ x ∈ S, κ ≤ interiorGaussian c l x) ∧
      (∀ x ∉ Metric.ball c r, 2*C ≤ l*‖gradient (interiorQuadratic c) x‖^2) ∧
      (∀ q : ℝ, 0 ≤ q → ∀ x ∈ S, ∀ u : SpatialCoordinates d,
        K*q*‖u‖^2 ≤ interiorHeatMatrix c l q x u u) ∧
      (∀ q : ℝ, 0 ≤ q → ∀ x n : SpatialCoordinates d,
        (∀ y ∈ S, inner ℝ (y-x) n ≤ 0) → ∀ a : ℝ,
          2*q*(fderiv ℝ (interiorGaussian c l) x n)*a^2 ≤ 0) := by
  obtain ⟨c,hc⟩ := hne
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hW c hc
  have hr : 0 < ε/2 := by positivity
  obtain ⟨l,hl,hgrad⟩ := exists_interiorGaussian_gradient_threshold c hr C
  have hl' : 0 < l := lt_of_lt_of_le (by norm_num) hl
  obtain ⟨R,hR,hbound⟩ := hS.exists_pos_norm_le
  have hRc : 0 ≤ R+‖c‖ := by positivity
  have hdist : ∀ x ∈ S, ‖x-c‖ ≤ R+‖c‖ := fun x hx =>
    (norm_sub_le x c).trans (add_le_add (hbound x hx) le_rfl)
  obtain ⟨K,hK,hcoerc⟩ := interiorHeatMatrix_uniform_coercive c hl' hRc
  refine ⟨c,ε/2,l,Real.exp (-l*(R+‖c‖)^2),K,hc,hr,hl,Real.exp_pos _,hK,
    ?_,interiorCarlemanProfile_smoothOnClosure c l S,
    interiorCarlemanProfile_bounds c hl'.le,?_,hgrad,?_,?_⟩
  · exact (Metric.closedBall_subset_ball (by linarith)).trans hball
  · intro x hx
    exact interiorGaussian_lower_bound c hl'.le hRc (hdist x hx)
  · intro q hq x hx u
    exact hcoerc q hq x (hdist x hx) u
  · intro q hq x n hn a
    exact interiorGaussian_face_flux_nonpos (hWS hc) hl'.le hq x n hn a

end Carleman
