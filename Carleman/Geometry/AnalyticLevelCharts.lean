module

public import Carleman.Geometry.HalfspaceSmoothExhaustion
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.LinearAlgebra.Dual.Lemmas
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology
@[expose] public noncomputable section
namespace Carleman
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_analytic_level_chart {g : E → ℝ} (hg : ContDiff ℝ ω g)
    (c : E) (hc : fderiv ℝ g c ≠ 0) :
    ∃ e : OpenPartialHomeomorph E (ℝ × (fderiv ℝ g c).ker),
      c ∈ e.source ∧ e c=(g c,0) ∧
      ContDiff ℝ ω (e : E → ℝ × (fderiv ℝ g c).ker) ∧
      ContDiffOn ℝ ω e.symm e.target ∧
      (∀ x, (e x).1=g x) ∧
      (∀ y ∈ e.target, g (e.symm y)=y.1) := by
  let L := fderiv ℝ g c
  have hL : L.range=⊤ := Module.Dual.range_eq_top_of_ne_zero (by
    intro h
    apply hc
    ext v
    exact LinearMap.congr_fun h v)
  have hk := L.ker_closedComplemented_of_finiteDimensional_range
  let P : E →L[ℝ] L.ker := Classical.choose hk
  let φ : ImplicitFunctionData ℝ E ℝ L.ker :=
    { leftFun := g
      leftDeriv := L
      rightFun := fun x => P (x-c)
      rightDeriv := P
      pt := c
      hasStrictFDerivAt_leftFun := hg.contDiffAt.hasStrictFDerivAt (by simp)
      hasStrictFDerivAt_rightFun := P.hasStrictFDerivAt.comp c ((hasStrictFDerivAt_id c).sub_const c)
      range_leftDeriv := hL
      range_rightDeriv := LinearMap.range_eq_of_proj (Classical.choose_spec hk)
      isCompl_ker := LinearMap.isCompl_of_proj (Classical.choose_spec hk) }
  let e₀ := φ.toOpenPartialHomeomorph
  have hefun : (e₀ : E → ℝ × L.ker)=(fun x => (g x,P (x-c))) := by
    funext x
    exact φ.toOpenPartialHomeomorph_apply x
  have hright : ContDiff ℝ ω (fun x => P (x-c)) := P.contDiff.comp (contDiff_id.sub contDiff_const)
  have hforward : ContDiff ℝ ω (e₀ : E → ℝ × L.ker) := by
    rw [hefun]
    exact hg.prodMk hright
  have hec : e₀ c=(g c,0) := by rw [hefun]; simp only [sub_self,map_zero]
  have hc0 : c ∈ e₀.source := φ.pt_mem_toOpenPartialHomeomorph_source
  have hFd : HasFDerivAt e₀
      (φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv φ.range_leftDeriv
        φ.range_rightDeriv φ.isCompl_ker : E →L[ℝ] ℝ × L.ker) c := by
    rw [show (e₀ : E → ℝ × L.ker)=φ.prodFun from φ.toOpenPartialHomeomorph_coe]
    exact φ.hasStrictFDerivAt.hasFDerivAt
  have hcinv : ContDiffAt ℝ ω e₀.symm (e₀ c) := by
    apply e₀.contDiffAt_symm (e₀.map_source hc0)
    · rw [e₀.left_inv hc0]
      exact hFd
    · rw [e₀.left_inv hc0]
      exact hforward.contDiffAt
  obtain ⟨W,hWsub,hWopen,hWc⟩ := mem_nhds_iff.mp (hcinv.eventually (by simp))
  let e := (e₀.symm.restrOpen W hWopen).symm
  have hce : c ∈ e.source := ⟨hc0,hWc⟩
  refine ⟨e,hce,hec,hforward,?_,(fun x => congrArg Prod.fst (congrFun hefun x)),?_⟩
  · intro y hy
    have hy' : ContDiffAt ℝ ω e₀.symm y := hWsub hy.2
    exact hy'.contDiffWithinAt
  · intro y hy
    have hid := e.right_inv hy
    change g (e₀.symm y)=y.1
    have hid' : (e₀ (e₀.symm y)).1=y.1 := congrArg Prod.fst hid
    rw [hefun] at hid'
    exact hid'

omit [CompleteSpace E] in
theorem analytic_chart_derivative_inverse
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : OpenPartialHomeomorph E F)
    (hf : ContDiffOn ℝ ω e e.source) (hi : ContDiffOn ℝ ω e.symm e.target)
    {x : E} (hx : x ∈ e.source) :
    (fderiv ℝ e x).IsInvertible ∧
      (fderiv ℝ e x).inverse=fderiv ℝ e.symm (e x) := by
  have hfx := (hf.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp)
  have hix := (hi.contDiffAt (e.open_target.mem_nhds (e.map_source hx))).differentiableAt (by simp)
  have hl : (fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x)=ContinuousLinearMap.id ℝ E := by
    rw [← fderiv_comp x hix hfx]
    have heq : (e.symm ∘ e) =ᶠ[𝓝 x] id := e.eventually_left_inverse hx
    exact heq.fderiv_eq.trans fderiv_id
  have hr : (fderiv ℝ e x).comp (fderiv ℝ e.symm (e x))=ContinuousLinearMap.id ℝ F := by
    have hfx' : DifferentiableAt ℝ e (e.symm (e x)) := by rwa [e.left_inv hx]
    have hc := fderiv_comp (e x) hfx' hix
    rw [e.left_inv hx] at hc
    rw [← hc]
    have heq : (e ∘ e.symm) =ᶠ[𝓝 (e x)] id := e.eventually_right_inverse (e.map_source hx)
    exact heq.fderiv_eq.trans fderiv_id
  exact ⟨ContinuousLinearMap.IsInvertible.of_inverse hr hl,ContinuousLinearMap.inverse_eq hr hl⟩

omit [CompleteSpace E] in
theorem level_chart_image_sublevel {g : E → ℝ} {c : E}
    (e : OpenPartialHomeomorph E (ℝ × (fderiv ℝ g c).ker))
    (he : ∀ x, (e x).1=g x) (a : ℝ) :
    e '' (e.source ∩ {x | g x<a})=e.target ∩ {y | y.1<a} := by
  ext y
  constructor
  · rintro ⟨x,⟨hxs,hgx⟩,rfl⟩
    exact ⟨e.map_source hxs,by change (e x).1<a; rwa [he]⟩
  · rintro ⟨hyt,hy⟩
    refine ⟨e.symm y,⟨e.map_target hyt,?_⟩,e.right_inv hyt⟩
    change g (e.symm y)<a
    rwa [← he,e.right_inv hyt]

omit [CompleteSpace E] in
theorem level_chart_frontier_iff {g : E → ℝ} {c : E}
    (e : OpenPartialHomeomorph E (ℝ × (fderiv ℝ g c).ker))
    (he : ∀ x, (e x).1=g x) (a : ℝ) {x : E} (hx : x ∈ e.source) :
    x ∈ frontier {z | g z<a} ↔ g x=a := by
  have hi : e.IsImage {z | g z<a} (Iio a ×ˢ univ) := by
    intro z _
    simp only [mem_prod,mem_Iio,mem_univ,and_true,he,mem_ofPred_eq]
  have hf := hi.frontier hx
  simpa only [frontier_prod_univ_eq,frontier_Iio,mem_prod,mem_singleton_iff,
    mem_univ,and_true,he] using hf.symm

omit [CompleteSpace E] in
theorem halfspaceExpSum_analytic {ι : Type*} [Fintype ι]
    (ℓ : ι → E →L[ℝ] ℝ) (b : ι → ℝ) (n : ℕ) :
    ContDiff ℝ ω (halfspaceExpSum ℓ b n) :=
  ContDiff.sum fun i _ => (contDiff_const.mul (contDiff_const.sub (ℓ i).contDiff)).exp

theorem halfspaceSmoothInner_analytic_chart {ι : Type*} [Fintype ι]
    (ℓ : ι → E →L[ℝ] ℝ) (b : ι → ℝ) (n : ℕ)
    {c : E} (hc : c ∈ halfspaceSmoothInner ℓ b n)
    {x : E} (hx : x ∈ frontier (halfspaceSmoothInner ℓ b n)) :
    ∃ e : OpenPartialHomeomorph E (ℝ × (fderiv ℝ (halfspaceExpSum ℓ b n) x).ker),
      x ∈ e.source ∧ e x=(1/2,0) ∧
      ContDiff ℝ ω (e : E → ℝ × (fderiv ℝ (halfspaceExpSum ℓ b n) x).ker) ∧
      ContDiffOn ℝ ω e.symm e.target ∧
      (∀ y, (e y).1=halfspaceExpSum ℓ b n y) ∧
      (∀ y ∈ e.source, y ∈ frontier (halfspaceSmoothInner ℓ b n) ↔ (e y).1=1/2) ∧
      e '' (e.source ∩ halfspaceSmoothInner ℓ b n)=e.target ∩ {y | y.1<1/2} := by
  obtain ⟨he,hreg⟩ := halfspaceSmoothInner_boundary_regular ℓ b n hc hx
  obtain ⟨e,hex,heval,hf,hi,hfst,_⟩ := exists_analytic_level_chart (halfspaceExpSum_analytic ℓ b n) x hreg
  refine ⟨e,hex,by simpa only [he] using heval,hf,hi,hfst,?_,level_chart_image_sublevel e hfst (1/2)⟩
  intro y hy
  rw [hfst]
  exact level_chart_frontier_iff e hfst (1/2) hy

end Carleman
