module
public import Carleman.Spatial.HalfspaceHeatBoundary
public import Carleman.Geometry.ConvexBoundaryFlux
/-! Actual heat flux on the curved boundaries of the smooth inner domains. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff BigOperators
namespace Carleman
variable {d : ℕ}

theorem pointwiseHeatFlux_unnormalized_eq (l k p z : (ℝ × SpatialCoordinates d) → ℝ)
    (t : ℝ) (x n : SpatialCoordinates d) (a : ℝ)
    (hz : z (t,x)=0) (ht : smoothD (1,0) z (t,x)=0)
    (hg : ∀ i : Fin d, smoothD (spaceTimeSpatialDirection i) z (t,x)=a*(n i)) :
    (∑ i, pointwiseHeatFlux spaceTimeSpatialDirection (1,0) l k p z i (t,x)*(n i)) =
      2*smoothD (0,n) l (t,x)*a^2*‖n‖^2 := by
  have henergy : directionalEnergy spaceTimeSpatialDirection z (t,x)=a^2*‖n‖^2 := by
    simp only [directionalEnergy,hg,mul_pow,← Finset.mul_sum,EuclideanSpace.real_norm_sq_eq]
  have hpair : directionalPair spaceTimeSpatialDirection l z (t,x)=
      a*smoothD (0,n) l (t,x) := by
    rw [← spacetime_directional_normal_sum l t x n]
    simp only [directionalPair,hg,Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have he i : pointwiseHeatFlux spaceTimeSpatialDirection (1,0) l k p z i (t,x)*(n i) =
      (4*a^2*smoothD (0,n) l (t,x))*(n i)^2-
        (2*a^2*‖n‖^2)*(smoothD (spaceTimeSpatialDirection i) l (t,x)*(n i)) := by
    simp only [pointwiseHeatFlux,hz,ht,hg,henergy,hpair]
    ring
  simp only [he,Finset.sum_sub_distrib,← Finset.mul_sum,
    ← EuclideanSpace.real_norm_sq_eq,spacetime_directional_normal_sum]
  ring

theorem spacetime_level_zero_derivatives (g : SpatialCoordinates d → ℝ)
    (hg : ContDiff ℝ ω g) {z : (ℝ × SpatialCoordinates d) → ℝ}
    (hz : ContDiff ℝ ∞ z) (t : ℝ) (x : SpatialCoordinates d)
    (hr : fderiv ℝ g x ≠ 0) (hzero : ∀ s y, g y=g x → z (s,y)=0) :
    z (t,x)=0 ∧ smoothD (1,0) z (t,x)=0 ∧
      ∃ a : ℝ, ∀ i : Fin d, smoothD (spaceTimeSpatialDirection i) z (t,x)=
        a*(graphSlopeVector g x i) := by
  refine ⟨hzero t x rfl,?_,?_⟩
  · rw [spaceTime_timeD hz]
    have he : (fun s => z (s,x))=fun _ => (0:ℝ) := funext fun s => hzero s x rfl
    rw [he,deriv_const]
  · have hs : ContDiff ℝ ∞ (fun y => z (t,y)) := hz.comp (contDiff_const.prodMk contDiff_id)
    obtain ⟨a,ha,_⟩ := regular_level_zero_gradient_hessian g (fun y => z (t,y)) hg hs x hr (hzero t)
    refine ⟨a,fun i => ?_⟩
    rw [spaceTimeSpatialDirection,spaceTime_spatialD hz,ha]
    simp only [smul_apply,smul_eq_mul,graphSlopeVector_apply]

theorem gaussian_level_heat_flux_nonpos (g : SpatialCoordinates d → ℝ)
    (hg : ContDiff ℝ ω g) (c x : SpatialCoordinates d)
    (hr : fderiv ℝ g x ≠ 0)
    (hsupport : inner ℝ (c-x) (graphSlopeVector g x) ≤ 0)
    {l : ℝ} (hl : 0 ≤ l) {q : ℝ → ℝ}
    {L u : (ℝ × SpatialCoordinates d) → ℝ} (hL : ContDiff ℝ ∞ L) (hu : ContDiff ℝ ∞ u)
    (hformula : ∀ s y, L (s,y)=q s*interiorCarlemanProfile c l y)
    (hzero : ∀ s y, g y=g x → u (s,y)=0)
    (k p : (ℝ × SpatialCoordinates d) → ℝ) (t : ℝ) (hq : 0 ≤ q t) :
    let z := fun y => Real.exp (L y)*u y
    (∑ i, pointwiseHeatFlux spaceTimeSpatialDirection (1,0) L k p z i (t,x)*
      graphSlopeVector g x i) ≤ 0 := by
  let z := fun y => Real.exp (L y)*u y
  have hz : ContDiff ℝ ∞ z := hL.exp.mul hu
  obtain ⟨h0,ht,a,ha⟩ := spacetime_level_zero_derivatives g hg hz t x hr
    (fun s y hy => by dsimp only [z];rw [hzero s y hy,mul_zero])
  dsimp only
  rw [pointwiseHeatFlux_unnormalized_eq L k p z t x (graphSlopeVector g x) a h0 ht ha,
    spaceTime_spatialD hL]
  have he : (fun y => L (t,y))=(fun y => q t*interiorCarlemanProfile c l y) := funext (hformula t)
  rw [he,fderiv_const_mul ((interiorCarlemanProfile_contDiff c l).differentiable (by simp) x)]
  change 2*(q t*fderiv ℝ (interiorCarlemanProfile c l) x (graphSlopeVector g x))*a^2*
    ‖graphSlopeVector g x‖^2 ≤ 0
  rw [interiorCarlemanProfile_fderiv_apply]
  have hsign := interiorGaussian_supporting_normal c hl x (graphSlopeVector g x) hsupport
  rw [interiorGaussian_fderiv_apply] at hsign
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      (mul_nonpos_of_nonneg_of_nonpos hq hsign)) (sq_nonneg _)) (sq_nonneg _)

theorem halfspaceSmoothInner_gaussian_heat_flux_nonpos {ι : Type*} [Fintype ι]
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ) (n : ℕ)
    (c : SpatialCoordinates d) (hc : c ∈ halfspaceSmoothInner ℓ b n)
    {l : ℝ} (hl : 0 ≤ l) {q : ℝ → ℝ}
    {L u : (ℝ × SpatialCoordinates d) → ℝ} (hL : ContDiff ℝ ∞ L) (hu : ContDiff ℝ ∞ u)
    (hformula : ∀ s y, L (s,y)=q s*interiorCarlemanProfile c l y)
    (hboundary : ∀ s y, y ∈ frontier (halfspaceSmoothInner ℓ b n) → u (s,y)=0)
    (k p : (ℝ × SpatialCoordinates d) → ℝ) (t : ℝ) (hq : 0 ≤ q t)
    (x : SpatialCoordinates d) (hx : x ∈ frontier (halfspaceSmoothInner ℓ b n)) :
    let z := fun y => Real.exp (L y)*u y
    (∑ i, pointwiseHeatFlux spaceTimeSpatialDirection (1,0) L k p z i (t,x)*
      graphSlopeVector (halfspaceExpSum ℓ b n) x i) ≤ 0 := by
  obtain ⟨he,hr⟩ := halfspaceSmoothInner_boundary_regular ℓ b n hc hx
  apply gaussian_level_heat_flux_nonpos (halfspaceExpSum ℓ b n) (halfspaceExpSum_analytic ℓ b n)
    c x hr ?_ hl hL hu hformula ?_ k p t hq
  · rw [real_inner_comm,graphSlopeVector_inner]
    have hs := halfspaceExpSum_support ℓ b n x c
    have hc' : halfspaceExpSum ℓ b n c < 1/2 := hc
    rw [he] at hs
    linarith
  · intro s y hy
    exact hboundary s y (halfspaceSmoothInner_frontier_of_level ℓ b n hc (hy.trans he))

end Carleman
