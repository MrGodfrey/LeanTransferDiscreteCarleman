module

public import Carleman.Spatial.SpacetimeHeatIdentity
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Local zero data on an actual plane force the true tangential derivative
to vanish. Normal derivative representations are derived, not assumed. -/
@[expose] public noncomputable section
open Filter
open scoped ContDiff Topology
namespace Carleman
variable {d : ℕ}

theorem smooth_plane_tangent_derivative {f : SpatialCoordinates d → ℝ}
    (hf : ContDiff ℝ ∞ f) (x n v : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hzero : ∀ y, ‖y-x‖ < r → inner ℝ (y-x) n=0 → f y=0)
    (hv : inner ℝ v n=0) : fderiv ℝ f x v=0 := by
  have hp : Continuous (fun s : ℝ => x+s • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hs : ∀ᶠ s : ℝ in 𝓝 0, ‖(x+s • v)-x‖ < r := by
    have h := (hp.sub continuous_const).norm.continuousAt.eventually
      (gt_mem_nhds (show ‖(x+(0:ℝ) • v)-x‖ < r by simpa using hr))
    exact h
  have he : (fun s : ℝ => f (x+s • v)) =ᶠ[𝓝 0] (fun _ => (0:ℝ)) := by
    filter_upwards [hs] with s hs
    apply hzero _ hs
    simp only [add_sub_cancel_left,real_inner_smul_left,hv,mul_zero]
  have hpath : HasDerivAt (fun s : ℝ => x+s • v) v 0 := by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x using 1
    simp only [one_smul]
  have h := (hf.differentiable (by simp) x).hasFDerivAt.comp_hasDerivAt_of_eq 0 hpath
    (by simp)
  have hd := he.deriv_eq
  rw [deriv_const] at hd
  exact h.deriv.symm.trans hd

theorem smooth_plane_normal_derivative {f : SpatialCoordinates d → ℝ}
    (hf : ContDiff ℝ ∞ f) (x n v : SpatialCoordinates d) (hn : ‖n‖=1)
    {r : ℝ} (hr : 0 < r)
    (hzero : ∀ y, ‖y-x‖ < r → inner ℝ (y-x) n=0 → f y=0) :
    fderiv ℝ f x v = fderiv ℝ f x n*inner ℝ v n := by
  have hnn : inner ℝ n n=1 := by rw [real_inner_self_eq_norm_sq,hn,one_pow]
  have ht : inner ℝ (v-(inner ℝ v n) • n) n=0 := by
    simp only [inner_sub_left,real_inner_smul_left,hnn,mul_one,sub_self]
  have h := smooth_plane_tangent_derivative hf x n (v-(inner ℝ v n) • n) hr hzero ht
  rw [map_sub,map_smul,smul_eq_mul] at h
  nlinarith

theorem spacetime_plane_zero_derivatives {z : (ℝ × SpatialCoordinates d) → ℝ}
    (hz : ContDiff ℝ ∞ z) (t : ℝ) (x n : SpatialCoordinates d) (hn : ‖n‖=1)
    {r : ℝ} (hr : 0 < r)
    (hzero : ∀ s : ℝ, ∀ y, ‖y-x‖ < r → inner ℝ (y-x) n=0 → z (s,y)=0) :
    z (t,x)=0 ∧ smoothD (1,0) z (t,x)=0 ∧
      ∀ i : Fin d, smoothD (spaceTimeSpatialDirection i) z (t,x)=
        (fderiv ℝ (fun y => z (t,y)) x n)*(n i) := by
  have hz0 (s : ℝ) : z (s,x)=0 := hzero s x (by simpa using hr) (by simp)
  refine ⟨hz0 t,?_,?_⟩
  · rw [spaceTime_timeD hz]
    have he : (fun s => z (s,x))=fun _ => (0:ℝ) := funext hz0
    rw [he,deriv_const]
  · intro i
    rw [spaceTimeSpatialDirection,spaceTime_spatialD hz]
    have hs : ContDiff ℝ ∞ (fun y => z (t,y)) :=
      hz.comp (contDiff_const.prodMk contDiff_id)
    simpa only [EuclideanSpace.basisFun_inner] using
      smooth_plane_normal_derivative hs x n (EuclideanSpace.basisFun (Fin d) ℝ i) hn hr (hzero t)

end Carleman
