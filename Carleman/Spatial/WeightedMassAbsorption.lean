module

public import Carleman.Spatial.NodalWeightedNorm

/-! Weighted Cauchy--Schwarz and scalar cancellation for the actual mass estimates. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman

theorem BoundedMultiplier.inner_le_weighted_pair {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (w ξ : BoundedMultiplier ν) (h : ∀ᵐ x ∂ν, w.value x*ξ.value x=1)
    (u v : Lp ℝ 2 ν) : inner ℝ u v ≤ w.seminorm u*ξ.seminorm v := by
  have he : inner ℝ u v = inner ℝ (w.map u) (ξ.map v) := by
    rw [L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [w.map_ae u,ξ.map_ae v,h] with x hu hv hx
    simp only [hu,hv,smul_eq_mul,RCLike.inner_apply,conj_trivial]
    calc
      _ = (w.value x*ξ.value x)*(v x*u x) := by rw [hx,one_mul]
      _ = _ := by ring
  rw [he]
  exact real_inner_le_norm _ _

theorem weighted_mass_norm_absorption {Z U T E μ θ D : ℝ}
    (hZ : 0 ≤ Z) (hU : 0 ≤ U) (hT : 0 ≤ T) (hE : 0 ≤ E)
    (hμ : 0 < μ) (hθ : 0 < θ) (hD : 0 < D)
    (hpair : μ*E ≤ U*T) (hstate : Z^2 ≤ θ^4*D*E) (htest : T^2 ≤ θ^2*D*E) :
    Z ≤ (θ^3*D/μ)*U := by
  by_cases he : E=0
  · rw [he,mul_zero] at hstate
    have hz : Z=0 := by nlinarith [sq_nonneg Z]
    rw [hz]
    positivity
  · have hepos : 0 < E := lt_of_le_of_ne hE (Ne.symm he)
    have hs := (sq_le_sq₀ (mul_nonneg hμ.le hE) (mul_nonneg hU hT)).mpr hpair
    have hs' : (μ^2*E)*E ≤ (U^2*θ^2*D)*E := by
      have hh := mul_le_mul_of_nonneg_left htest (sq_nonneg U)
      nlinarith
    have hc : μ^2*E ≤ U^2*θ^2*D := le_of_mul_le_mul_right hs' hepos
    have hz : (μ*Z)^2 ≤ (θ^3*D*U)^2 := by
      calc
        _ = μ^2*Z^2 := mul_pow _ _ _
        _ ≤ μ^2*(θ^4*D*E) := mul_le_mul_of_nonneg_left hstate (sq_nonneg μ)
        _ = θ^4*D*(μ^2*E) := by ring
        _ ≤ θ^4*D*(U^2*θ^2*D) := mul_le_mul_of_nonneg_left hc (by positivity)
        _ = _ := by ring
    have hz' : μ*Z ≤ θ^3*D*U :=
      (sq_le_sq₀ (mul_nonneg hμ.le hZ) (by positivity)).mp hz
    calc
      Z ≤ (θ^3*D*U)/μ := (le_div_iff₀ hμ).mpr (by simpa only [mul_comm μ] using hz')
      _ = _ := by ring

end Carleman
