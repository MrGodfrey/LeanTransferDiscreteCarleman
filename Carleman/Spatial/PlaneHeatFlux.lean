module

public import Carleman.Spatial.SmoothPlaneBoundary
public import Carleman.Weights.InteriorGaussianGeometry

/-! Identification of the true pointwise heat flux on a flat Dirichlet face. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1600000
open scoped ContDiff BigOperators
namespace Carleman
variable {d : ℕ}

theorem spacetime_directional_normal_sum (f : (ℝ × SpatialCoordinates d) → ℝ)
    (t : ℝ) (x n : SpatialCoordinates d) :
    (∑ i, smoothD (spaceTimeSpatialDirection i) f (t,x)*(n i)) =
      smoothD (0,n) f (t,x) := by
  have he : (∑ i : Fin d, (n i) • spaceTimeSpatialDirection i) = (0,n) := by
    apply Prod.ext
    · simp only [Prod.fst_sum,Prod.smul_fst,spaceTimeSpatialDirection,smul_eq_mul,
        mul_zero,Finset.sum_const_zero]
    · simpa only [Prod.snd_sum,Prod.smul_snd,spaceTimeSpatialDirection,EuclideanSpace.basisFun_repr]
        using (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr n
  have h := congrArg (fderiv ℝ f (t,x)) he
  rw [map_sum] at h
  simp only [map_smul,smul_eq_mul] at h
  calc
    _ = ∑ i, (n i)*smoothD (spaceTimeSpatialDirection i) f (t,x) :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    _ = _ := h

theorem pointwiseHeatFlux_normal_eq (l k p z : (ℝ × SpatialCoordinates d) → ℝ)
    (t : ℝ) (x n : SpatialCoordinates d) (hn : ‖n‖=1) (a : ℝ)
    (hz : z (t,x)=0) (ht : smoothD (1,0) z (t,x)=0)
    (hg : ∀ i : Fin d, smoothD (spaceTimeSpatialDirection i) z (t,x)=a*(n i)) :
    (∑ i, pointwiseHeatFlux spaceTimeSpatialDirection (1,0) l k p z i (t,x)*(n i)) =
      2*smoothD (0,n) l (t,x)*a^2 := by
  have hnorm : (∑ i : Fin d, (n i)^2)=1 := by
    rw [← EuclideanSpace.real_norm_sq_eq,hn,one_pow]
  have henergy : directionalEnergy spaceTimeSpatialDirection z (t,x)=a^2 := by
    simp only [directionalEnergy,hg,mul_pow,← Finset.mul_sum,hnorm,mul_one]
  have hpair : directionalPair spaceTimeSpatialDirection l z (t,x)=
      a*smoothD (0,n) l (t,x) := by
    rw [← spacetime_directional_normal_sum l t x n]
    simp only [directionalPair,hg,Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have he i : pointwiseHeatFlux spaceTimeSpatialDirection (1,0) l k p z i (t,x)*(n i) =
      (4*a^2*smoothD (0,n) l (t,x))*(n i)^2-
        (2*a^2)*(smoothD (spaceTimeSpatialDirection i) l (t,x)*(n i)) := by
    simp only [pointwiseHeatFlux,hz,ht,hg,henergy,hpair]
    ring
  simp only [he,Finset.sum_sub_distrib,← Finset.mul_sum,hnorm,
    spacetime_directional_normal_sum]
  ring

theorem smooth_plane_heat_flux {z : (ℝ × SpatialCoordinates d) → ℝ}
    (hz : ContDiff ℝ ∞ z) (l k p : (ℝ × SpatialCoordinates d) → ℝ)
    (t : ℝ) (x n : SpatialCoordinates d) (hn : ‖n‖=1) {r : ℝ} (hr : 0 < r)
    (hzero : ∀ s : ℝ, ∀ y, ‖y-x‖ < r → inner ℝ (y-x) n=0 → z (s,y)=0) :
    (∑ i, pointwiseHeatFlux spaceTimeSpatialDirection (1,0) l k p z i (t,x)*(n i)) =
      2*smoothD (0,n) l (t,x)*(fderiv ℝ (fun y => z (t,y)) x n)^2 := by
  obtain ⟨h0,ht,hg⟩ := spacetime_plane_zero_derivatives hz t x n hn hr hzero
  exact pointwiseHeatFlux_normal_eq l k p z t x n hn _ h0 ht hg

theorem gaussian_plane_heat_flux_nonpos {S : Set (SpatialCoordinates d)}
    {c : SpatialCoordinates d} (hc : c ∈ S) {l : ℝ} (hl : 0 ≤ l)
    {q : ℝ → ℝ} {L z : (ℝ × SpatialCoordinates d) → ℝ}
    (hL : ContDiff ℝ ∞ L) (hz : ContDiff ℝ ∞ z)
    (hformula : ∀ s y, L (s,y)=q s*interiorCarlemanProfile c l y)
    (k p : (ℝ × SpatialCoordinates d) → ℝ) (t : ℝ) (hq : 0 ≤ q t)
    (x n : SpatialCoordinates d) (hn : ‖n‖=1)
    (hsupport : ∀ y ∈ S, inner ℝ (y-x) n ≤ 0) {r : ℝ} (hr : 0 < r)
    (hzero : ∀ s : ℝ, ∀ y, ‖y-x‖ < r → inner ℝ (y-x) n=0 → z (s,y)=0) :
    (∑ i, pointwiseHeatFlux spaceTimeSpatialDirection (1,0) L k p z i (t,x)*(n i)) ≤ 0 := by
  rw [smooth_plane_heat_flux hz L k p t x n hn hr hzero,spaceTime_spatialD hL]
  have he : (fun y => L (t,y))=(fun y => q t*interiorCarlemanProfile c l y) :=
    funext (hformula t)
  rw [he,fderiv_const_mul ((interiorCarlemanProfile_contDiff c l).differentiable (by simp) x)]
  change 2*(q t*fderiv ℝ (interiorCarlemanProfile c l) x n)*_ ≤ 0
  rw [interiorCarlemanProfile_fderiv_apply]
  have hsign := interiorGaussian_supporting_normal c hl x n (hsupport c hc)
  rw [interiorGaussian_fderiv_apply] at hsign
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      (mul_nonpos_of_nonneg_of_nonpos hq hsign)) (sq_nonneg _)

end Carleman
