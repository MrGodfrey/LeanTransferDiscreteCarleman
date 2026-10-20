module
public import Carleman.Geometry.SmoothGraphHeightExtension
public import Carleman.Spatial.SmoothLaplacianProduct
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
/-! Original zero data on a regular level force the true normal gradient
and tangential Hessian relations. The original exponential sum has positive
semidefinite actual Hessian, and its level is the true frontier. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology BigOperators ContDiff
namespace Carleman
variable {d : ℕ}

theorem smooth_directional_fderiv_eq (f : SpatialCoordinates d → ℝ)
    (hf : ContDiff ℝ ∞ f) (x v w : SpatialCoordinates d) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x w=fderiv ℝ (fderiv ℝ f) x w v := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  rw [fderiv_clm_apply (hD.differentiable (by simp) x)
    (differentiableAt_const v)]
  simp

theorem second_fderiv_comp_zero_of_tangent (h : SpatialCoordinates d → ℝ)
    (hh : ContDiff ℝ ∞ h) (G : SpatialCoordinates d → SpatialCoordinates d)
    (hG : ContDiff ℝ ∞ G) (c v : SpatialCoordinates d)
    (hGc : G c=c) (hDv : fderiv ℝ G c v=v) (hDh : fderiv ℝ h c=0)
    {a : ℝ} (hconst : (h ∘ G) =ᶠ[𝓝 c] (fun _ => a)) :
    fderiv ℝ (fderiv ℝ h) c v v=0 := by
  have hd := hconst.fderiv (𝕜 := ℝ)
  have he : (fun x => fderiv ℝ h (G x) (fderiv ℝ G x v)) =ᶠ[𝓝 c] (fun _ => (0 : ℝ)) := by
    filter_upwards [hd] with x hx
    rw [fderiv_comp x (hh.differentiable (by simp) _) (hG.differentiable (by simp) x),fderiv_const_apply] at hx
    exact congrArg (fun L : SpatialCoordinates d →L[ℝ] ℝ => L v) hx
  have heD := he.fderiv_eq (𝕜 := ℝ)
  have hDhsm : ContDiff ℝ ∞ (fderiv ℝ h) := hh.fderiv_right (by simp)
  have hDGsm : ContDiff ℝ ∞ (fun x => fderiv ℝ G x v) := (hG.fderiv_right (by simp)).clm_apply contDiff_const
  have hDA : DifferentiableAt ℝ (fun y => fderiv ℝ h (G y)) c := (hDhsm.comp hG).differentiable (by simp) c
  rw [fderiv_clm_apply hDA
    (hDGsm.differentiable (by simp) c),fderiv_const_apply] at heD
  have hval := congrArg (fun L : SpatialCoordinates d →L[ℝ] ℝ => L v) heD
  rw [fderiv_fun_comp c (hDhsm.differentiable (by simp) _) (hG.differentiable (by simp) c)] at hval
  simpa only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,hGc,hDh,
    hDv,zero_apply,zero_add] using hval

theorem coordinateLevelMap_const_composition_derivative (r : Fin d)
    (ψ f : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hf : ContDiff ℝ ∞ f)
    (c : SpatialCoordinates d) (hc : ψ c=c r) {a : ℝ}
    (hconst : (f ∘ coordinateLevelMap r ψ) =ᶠ[𝓝 c] (fun _ => a)) (v : SpatialCoordinates d) :
    fderiv ℝ f c v+(fderiv ℝ ψ c v-v r)*fderiv ℝ f c (EuclideanSpace.basisFun (Fin d) ℝ r)=0 := by
  have hfix : coordinateLevelMap r ψ c=c := by simp [coordinateLevelMap,hc]
  have hd := hconst.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp c (hf.differentiable (by simp) _) ((coordinateLevelMap_contDiff r ψ hψ).differentiable (by simp) c),
    (coordinateLevelMap_hasFDerivAt r ψ (hψ.differentiable (by simp) c)).fderiv,fderiv_const_apply] at hd
  have hh := congrArg (fun L : SpatialCoordinates d →L[ℝ] ℝ => L v) hd
  simpa only [ContinuousLinearMap.comp_apply,add_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.smulRight_apply,
    sub_apply,map_add,map_smul,smul_eq_mul,hfix,zero_apply,EuclideanSpace.coe_proj] using hh

theorem level_graph_gradient_multiple (r : Fin d) (g u ψ : SpatialCoordinates d → ℝ)
    (hg : ContDiff ℝ ∞ g) (hu : ContDiff ℝ ∞ u) (hψ : ContDiff ℝ ∞ ψ)
    (c : SpatialCoordinates d) (hψc : ψ c=c r)
    (hr : fderiv ℝ g c (EuclideanSpace.basisFun (Fin d) ℝ r) ≠ 0)
    {a : ℝ} (hgconst : (g ∘ coordinateLevelMap r ψ) =ᶠ[𝓝 c] (fun _ => a))
    (huconst : (u ∘ coordinateLevelMap r ψ) =ᶠ[𝓝 c] (fun _ => (0 : ℝ))) :
    fderiv ℝ u c=(fderiv ℝ u c (EuclideanSpace.basisFun (Fin d) ℝ r)/
      fderiv ℝ g c (EuclideanSpace.basisFun (Fin d) ℝ r)) • fderiv ℝ g c := by
  ext v
  have h1 := coordinateLevelMap_const_composition_derivative r ψ g hψ hg c hψc hgconst v
  have h2 := coordinateLevelMap_const_composition_derivative r ψ u hψ hu c hψc huconst v
  simp only [smul_apply,smul_eq_mul]
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hr).mpr
  exact (show fderiv ℝ u c v*fderiv ℝ g c (EuclideanSpace.basisFun (Fin d) ℝ r)=
      fderiv ℝ u c (EuclideanSpace.basisFun (Fin d) ℝ r)*fderiv ℝ g c v by
        linear_combination (fderiv ℝ g c (EuclideanSpace.basisFun (Fin d) ℝ r))*h2-
          (fderiv ℝ u c (EuclideanSpace.basisFun (Fin d) ℝ r))*h1)

theorem second_fderiv_sub_smul (u g : SpatialCoordinates d → ℝ)
    (hu : ContDiff ℝ ∞ u) (hg : ContDiff ℝ ∞ g) (q : ℝ) (c v w : SpatialCoordinates d) :
    fderiv ℝ (fderiv ℝ (u-q • g)) c v w=
      fderiv ℝ (fderiv ℝ u) c v w-q*fderiv ℝ (fderiv ℝ g) c v w := by
  have he : fderiv ℝ (u-q • g)=fderiv ℝ u-q • fderiv ℝ g := by
    funext x
    exact ((hu.differentiable (by simp) x).hasFDerivAt.sub
      ((hg.differentiable (by simp) x).hasFDerivAt.const_smul q)).fderiv
  have hDu : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hDg : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
  rw [he,((hDu.differentiable (by simp) c).hasFDerivAt.sub
    ((hDg.differentiable (by simp) c).hasFDerivAt.const_smul q)).fderiv]
  simp only [sub_apply,smul_apply,smul_eq_mul]

theorem level_graph_tangent_hessian_multiple (r : Fin d) (g u ψ : SpatialCoordinates d → ℝ)
    (hg : ContDiff ℝ ∞ g) (hu : ContDiff ℝ ∞ u) (hψ : ContDiff ℝ ∞ ψ)
    (c : SpatialCoordinates d) (hψc : ψ c=c r)
    (hr : fderiv ℝ g c (EuclideanSpace.basisFun (Fin d) ℝ r) ≠ 0)
    {a : ℝ} (hgconst : (g ∘ coordinateLevelMap r ψ) =ᶠ[𝓝 c] (fun _ => a))
    (huconst : (u ∘ coordinateLevelMap r ψ) =ᶠ[𝓝 c] (fun _ => (0 : ℝ)))
    (v : SpatialCoordinates d) (hv : fderiv ℝ g c v=0) :
    fderiv ℝ (fderiv ℝ u) c v v=
      (fderiv ℝ u c (EuclideanSpace.basisFun (Fin d) ℝ r)/fderiv ℝ g c (EuclideanSpace.basisFun (Fin d) ℝ r))*
        fderiv ℝ (fderiv ℝ g) c v v := by
  let q := fderiv ℝ u c (EuclideanSpace.basisFun (Fin d) ℝ r)/fderiv ℝ g c (EuclideanSpace.basisFun (Fin d) ℝ r)
  let h := u-q • g
  have hh : ContDiff ℝ ∞ h := hu.sub (hg.const_smul q)
  have hgrad : fderiv ℝ u c=q • fderiv ℝ g c := level_graph_gradient_multiple r g u ψ hg hu hψ c hψc hr hgconst huconst
  have hDh : fderiv ℝ h c=0 := by
    rw [((hu.differentiable (by simp) c).hasFDerivAt.sub
      ((hg.differentiable (by simp) c).hasFDerivAt.const_smul q)).fderiv,hgrad,sub_self]
  have hGc : coordinateLevelMap r ψ c=c := by simp [coordinateLevelMap,hψc]
  have hvψ : fderiv ℝ ψ c v-v r=0 := by
    have he := coordinateLevelMap_const_composition_derivative r ψ g hψ hg c hψc hgconst v
    rw [hv,zero_add] at he
    exact (mul_eq_zero.mp he).resolve_right hr
  have hDv : fderiv ℝ (coordinateLevelMap r ψ) c v=v := by
    rw [(coordinateLevelMap_hasFDerivAt r ψ (hψ.differentiable (by simp) c)).fderiv]
    change v+(fderiv ℝ ψ c v-v r) • EuclideanSpace.basisFun (Fin d) ℝ r=v
    rw [hvψ,zero_smul,add_zero]
  have hconst : (h ∘ coordinateLevelMap r ψ) =ᶠ[𝓝 c] (fun _ => -q*a) := by
    filter_upwards [hgconst,huconst] with x hx hy
    change u (coordinateLevelMap r ψ x)-q*g (coordinateLevelMap r ψ x)= -q*a
    change g (coordinateLevelMap r ψ x)=a at hx
    change u (coordinateLevelMap r ψ x)=0 at hy
    rw [hx,hy]
    ring
  have he := second_fderiv_comp_zero_of_tangent h hh (coordinateLevelMap r ψ)
    (coordinateLevelMap_contDiff r ψ hψ) c v hGc hDv hDh hconst
  change fderiv ℝ (fderiv ℝ (u-q • g)) c v v=0 at he
  rw [second_fderiv_sub_smul u g hu hg q] at he
  exact sub_eq_zero.mp he

theorem regular_level_zero_gradient_hessian (g u : SpatialCoordinates d → ℝ)
    (hg : ContDiff ℝ ω g) (hu : ContDiff ℝ ∞ u) (c : SpatialCoordinates d)
    (hreg : fderiv ℝ g c ≠ 0) (hzero : ∀ x, g x=g c → u x=0) :
    ∃ q : ℝ, fderiv ℝ u c=q • fderiv ℝ g c ∧
      ∀ v : SpatialCoordinates d, fderiv ℝ g c v=0 →
        fderiv ℝ (fderiv ℝ u) c v v=q*fderiv ℝ (fderiv ℝ g) c v v := by
  obtain ⟨r,ψ,C,B,N,hN,hcN,hψ,_,_,_,hψc,hr,hgraph,_⟩ :=
    exists_bounded_smooth_coordinate_level_height g hg c hreg
  have hgconst : (g ∘ coordinateLevelMap r ψ) =ᶠ[𝓝 c] (fun _ => g c) := by
    filter_upwards [hN.mem_nhds hcN] with x hx
    exact hgraph x hx
  have huconst : (u ∘ coordinateLevelMap r ψ) =ᶠ[𝓝 c] (fun _ => (0 : ℝ)) := by
    filter_upwards [hN.mem_nhds hcN] with x hx
    exact hzero _ (hgraph x hx)
  exact ⟨_,level_graph_gradient_multiple r g u ψ (hg.of_le le_top) hu hψ c hψc hr hgconst huconst,
    fun v hv => level_graph_tangent_hessian_multiple r g u ψ (hg.of_le le_top) hu hψ c hψc hr hgconst huconst v hv⟩

theorem halfspaceSmoothInner_frontier_of_level {ι : Type*} [Fintype ι]
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ) (n : ℕ)
    {z : SpatialCoordinates d} (hz : z ∈ halfspaceSmoothInner ℓ b n)
    {c : SpatialCoordinates d} (hc : halfspaceExpSum ℓ b n c=1/2) :
    c ∈ frontier (halfspaceSmoothInner ℓ b n) := by
  have hseg : openSegment ℝ z c ⊆ halfspaceSmoothInner ℓ b n := by
    rintro y ⟨α,β,hα,hβ,hsum,rfl⟩
    have hh := (halfspaceExpSum_convex ℓ b n).2 (mem_univ z) (mem_univ c) hα.le hβ.le hsum
    change halfspaceExpSum ℓ b n (α • z+β • c)<1/2
    simp only [smul_eq_mul,hc] at hh
    have hz' : halfspaceExpSum ℓ b n z<1/2 := hz
    nlinarith [mul_pos hα (sub_pos.mpr hz')]
  rw [(halfspaceSmoothInner_open ℓ b n).frontier_eq]
  refine ⟨closure_mono hseg (segment_subset_closure_openSegment (right_mem_segment ℝ z c)),?_⟩
  change ¬halfspaceExpSum ℓ b n c<1/2
  rw [hc]
  exact lt_irrefl _

theorem halfspaceSmoothInner_zero_gradient_hessian {ι : Type*} [Fintype ι]
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ) (n : ℕ)
    {z : SpatialCoordinates d} (hz : z ∈ halfspaceSmoothInner ℓ b n)
    (u : SpatialCoordinates d → ℝ) (hu : ContDiff ℝ ∞ u)
    (hzero : ∀ x ∈ frontier (halfspaceSmoothInner ℓ b n), u x=0)
    {c : SpatialCoordinates d} (hc : c ∈ frontier (halfspaceSmoothInner ℓ b n)) :
    ∃ q : ℝ, fderiv ℝ u c=q • fderiv ℝ (halfspaceExpSum ℓ b n) c ∧
      ∀ v : SpatialCoordinates d, fderiv ℝ (halfspaceExpSum ℓ b n) c v=0 →
        fderiv ℝ (fderiv ℝ u) c v v=q*fderiv ℝ (fderiv ℝ (halfspaceExpSum ℓ b n)) c v v := by
  obtain ⟨he,hr⟩ := halfspaceSmoothInner_boundary_regular ℓ b n hz hc
  exact regular_level_zero_gradient_hessian (halfspaceExpSum ℓ b n) u (halfspaceExpSum_analytic ℓ b n) hu c hr
    (fun x hx => hzero x (halfspaceSmoothInner_frontier_of_level ℓ b n hz (hx.trans he)))

theorem halfspaceExpSum_second_directional {ι : Type*} [Fintype ι]
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ) (n : ℕ) (x v : SpatialCoordinates d) :
    fderiv ℝ (fderiv ℝ (halfspaceExpSum ℓ b n)) x v v=
      ∑ i, Real.exp (((n+1:ℕ):ℝ)*(b i-ℓ i x))*(((n+1:ℕ):ℝ)*(ℓ i v))^2 := by
  let k : ℝ := (n+1:ℕ)
  have hfirst : (fun y => fderiv ℝ (halfspaceExpSum ℓ b n) y v)=
      fun y => ∑ i, Real.exp (k*(b i-ℓ i y))*(-k*ℓ i v) := by
    funext y
    rw [(halfspaceExpSum_hasFDerivAt ℓ b n y).fderiv]
    simp only [sum_apply,smul_apply,smul_eq_mul,k]
  have he (i) : HasFDerivAt (fun y => Real.exp (k*(b i-ℓ i y)))
      (Real.exp (k*(b i-ℓ i x)) • (-k • ℓ i)) x := by
    convert (((ℓ i).hasFDerivAt.const_sub (b i)).const_mul k).exp using 1
    ext w
    simp only [smul_apply,smul_eq_mul,neg_apply]
    ring
  rw [← smooth_directional_fderiv_eq (halfspaceExpSum ℓ b n) (halfspaceExpSum_contDiff ℓ b n),hfirst,
    (HasFDerivAt.fun_sum (fun i _ => (he i).mul_const (-k*ℓ i v))).fderiv]
  simp only [sum_apply,smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [k]
  ring

theorem halfspaceExpSum_hessian_nonneg {ι : Type*} [Fintype ι]
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ) (n : ℕ) (x v : SpatialCoordinates d) :
    0 ≤ fderiv ℝ (fderiv ℝ (halfspaceExpSum ℓ b n)) x v v := by
  rw [halfspaceExpSum_second_directional]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)

end Carleman
