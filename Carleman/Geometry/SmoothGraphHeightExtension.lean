module
public import Carleman.Geometry.CoordinateLevelGraph
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.MeanValue
/-! Actual local graph heights admit globally smooth normal-invariant extensions
with internally proved height and slope Lipschitz constants. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped Topology BigOperators ContDiff
namespace Carleman
variable {d : ℕ}

theorem exists_compact_smooth_extension_near (ψ : SpatialCoordinates d → ℝ)
    {V : Set (SpatialCoordinates d)} (hV : IsOpen V) {c : SpatialCoordinates d}
    (hc : c ∈ V) (hψ : ContDiffOn ℝ ∞ ψ V) :
    ∃ h : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧
      h =ᶠ[𝓝 c] ψ := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hc)
  let β : ContDiffBump c := ⟨ε/4,ε/2,by positivity,by linarith⟩
  have hsupp : tsupport β ⊆ V := by
    rw [β.tsupport_eq]
    exact (closedBall_subset_ball (by dsimp [β]; linarith)).trans hball
  refine ⟨fun x => β x*ψ x,?_,β.hasCompactSupport.mul_right,?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ V
    · exact β.contDiffAt.mul (hψ.contDiffAt (hV.mem_nhds hx))
    · have hzero : β =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun hh => hx (hsupp hh))
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hzero] with y hy
      simp [hy]
  · filter_upwards [β.eventuallyEq_one] with x hx
    simp only [hx,Pi.one_apply,one_mul]

theorem exists_lipschitzWith_of_smooth_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∃ C : NNReal, LipschitzWith C f := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.mp hf).2
  obtain ⟨M,hM⟩ := (hc.fderiv ℝ).exists_bound_of_continuous hD.continuous
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine ⟨⟨M,hM0⟩,lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by simp)) ?_⟩
  intro x
  exact hM x

def coordinateTangentProjection (r : Fin d) : SpatialCoordinates d →L[ℝ] SpatialCoordinates d :=
  ContinuousLinearMap.id ℝ _-(EuclideanSpace.proj r).smulRight (EuclideanSpace.basisFun (Fin d) ℝ r)

theorem coordinateLevelMap_constant_affine (r : Fin d) (a : ℝ) (x : SpatialCoordinates d) :
    coordinateLevelMap r (fun _ => a) x=coordinateTangentProjection r x+a • EuclideanSpace.basisFun (Fin d) ℝ r := by
  simp only [coordinateLevelMap,coordinateTangentProjection,sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,sub_smul]
  abel

theorem coordinateLevelMap_constant_lipschitz (r : Fin d) (a : ℝ) :
    LipschitzWith ‖coordinateTangentProjection r‖₊ (coordinateLevelMap r (fun _ => a)) := by
  intro x y
  simpa only [coordinateLevelMap_constant_affine,edist_add_right] using
    (coordinateTangentProjection r).lipschitzWith x y

theorem coordinateLevelMap_constant_hasFDerivAt (r : Fin d) (a : ℝ) (x : SpatialCoordinates d) :
    HasFDerivAt (coordinateLevelMap r (fun _ => a)) (coordinateTangentProjection r) x := by
  have he : coordinateLevelMap r (fun _ : SpatialCoordinates d => a)=
      (fun y => coordinateTangentProjection r y+a • EuclideanSpace.basisFun (Fin d) ℝ r) :=
    funext (coordinateLevelMap_constant_affine r a)
  rw [he]
  exact (coordinateTangentProjection r).hasFDerivAt.add_const (a • EuclideanSpace.basisFun (Fin d) ℝ r)

theorem exists_smooth_normal_invariant_extension (r : Fin d) (ψ : SpatialCoordinates d → ℝ)
    {V : Set (SpatialCoordinates d)} (hV : IsOpen V) {c : SpatialCoordinates d}
    (hc : c ∈ V) (hψ : ContDiffOn ℝ ∞ ψ V)
    (hinv : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x) :
    ∃ (Ψ : SpatialCoordinates d → ℝ) (C : NNReal) (B : Fin d → NNReal),
      ContDiff ℝ ∞ Ψ ∧ LipschitzWith C Ψ ∧
      (∀ i : Fin d, LipschitzWith (B i) (fun x => fderiv ℝ Ψ x (EuclideanSpace.basisFun (Fin d) ℝ i))) ∧
      (∀ (x : SpatialCoordinates d) (t : ℝ), Ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=Ψ x) ∧
      Ψ =ᶠ[𝓝 c] ψ := by
  obtain ⟨h,hh,hcompact,heq⟩ := exists_compact_smooth_extension_near ψ hV hc hψ
  let Q := coordinateLevelMap r (fun _ : SpatialCoordinates d => c r)
  let P := coordinateTangentProjection r
  let Ψ := h ∘ Q
  have hQ : ContDiff ℝ ∞ Q := coordinateLevelMap_contDiff r _ contDiff_const
  have hQc : Q c=c := by simp [Q,coordinateLevelMap]
  have hQL : LipschitzWith ‖P‖₊ Q := coordinateLevelMap_constant_lipschitz r (c r)
  obtain ⟨C,hC⟩ := exists_lipschitzWith_of_smooth_compact h hh hcompact
  have hsmooth (i : Fin d) : ContDiff ℝ ∞ (fun z => fderiv ℝ h z (P (EuclideanSpace.basisFun (Fin d) ℝ i))) :=
    (contDiff_infty_iff_fderiv.mp hh).2.clm_apply contDiff_const
  choose B hB using fun i => exists_lipschitzWith_of_smooth_compact _ (hsmooth i)
    (hcompact.fderiv_apply ℝ (P (EuclideanSpace.basisFun (Fin d) ℝ i)))
  have hD (x : SpatialCoordinates d) (i : Fin d) :
      fderiv ℝ Ψ x (EuclideanSpace.basisFun (Fin d) ℝ i)=
        fderiv ℝ h (Q x) (P (EuclideanSpace.basisFun (Fin d) ℝ i)) := by
    have hd := ((hh.differentiable (by simp) (Q x)).hasFDerivAt.comp x
      (coordinateLevelMap_constant_hasFDerivAt r (c r) x)).fderiv
    exact congrArg (fun L : SpatialCoordinates d →L[ℝ] ℝ => L (EuclideanSpace.basisFun (Fin d) ℝ i)) hd
  refine ⟨Ψ,C*‖P‖₊,fun i => B i*‖P‖₊,hh.comp hQ,hC.comp hQL,?_,?_,?_⟩
  · intro i
    simp_rw [hD]
    exact (hB i).comp hQL
  · intro x t
    exact congrArg h (coordinateLevelMap_constant_normal_invariant r (c r) x t)
  · have ht : Tendsto Q (𝓝 c) (𝓝 c) := by
      have ht := hQ.continuous.continuousAt (x := c)
      rw [ContinuousAt,hQc] at ht
      exact ht
    filter_upwards [heq.comp_tendsto ht] with x hx
    exact hx.trans (hinv x (c r-x r))

theorem exists_bounded_smooth_coordinate_level_height (g : SpatialCoordinates d → ℝ)
    (hg : ContDiff ℝ ω g) (c : SpatialCoordinates d) (hc : fderiv ℝ g c ≠ 0) :
    ∃ (r : Fin d) (Ψ : SpatialCoordinates d → ℝ) (C : NNReal) (B : Fin d → NNReal)
      (N : Set (SpatialCoordinates d)),
      IsOpen N ∧ c ∈ N ∧ ContDiff ℝ ∞ Ψ ∧ LipschitzWith C Ψ ∧
      (∀ i : Fin d, LipschitzWith (B i) (fun x => fderiv ℝ Ψ x (EuclideanSpace.basisFun (Fin d) ℝ i))) ∧
      (∀ (x : SpatialCoordinates d) (t : ℝ), Ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=Ψ x) ∧
      Ψ c=c r ∧ fderiv ℝ g c (EuclideanSpace.basisFun (Fin d) ℝ r) ≠ 0 ∧
      (∀ x ∈ N, g (coordinateLevelMap r Ψ x)=g c) ∧
      (∀ x ∈ N, g x=g c ↔ x r=Ψ x) := by
  obtain ⟨r,hr⟩ := exists_nonzero_coordinate_derivative g c hc
  obtain ⟨ψ,V,W,hV,hcV,hW,hcW,hψ,hψc,hinv,hgraph,hlevel⟩ :=
    exists_local_coordinate_level_height r g hg c hr
  obtain ⟨Ψ,C,B,hΨ,hC,hB,hΨinv,heq⟩ :=
    exists_smooth_normal_invariant_extension r ψ hV hcV (hψ.of_le le_top) hinv
  obtain ⟨N,hNsub,hN,hcN⟩ := _root_.mem_nhds_iff.mp
    (inter_mem (inter_mem (hV.mem_nhds hcV) (hW.mem_nhds hcW)) heq)
  refine ⟨r,Ψ,C,B,N,hN,hcN,hΨ,hC,hB,hΨinv,heq.eq_of_nhds.trans hψc,hr,?_,?_⟩
  · intro x hx
    have he : coordinateLevelMap r Ψ x=coordinateLevelMap r ψ x := by
      dsimp only [coordinateLevelMap]
      rw [(hNsub hx).2]
    rw [he]
    exact hgraph x (hNsub hx).1.1
  · intro x hx
    rw [(hNsub hx).2]
    exact hlevel x (hNsub hx).1

theorem halfspaceSmoothInner_bounded_coordinate_level_height {ι : Type*} [Fintype ι]
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ) (n : ℕ)
    {z : SpatialCoordinates d} (hz : z ∈ halfspaceSmoothInner ℓ b n)
    {c : SpatialCoordinates d} (hc : c ∈ frontier (halfspaceSmoothInner ℓ b n)) :
    ∃ (r : Fin d) (Ψ : SpatialCoordinates d → ℝ) (C : NNReal) (B : Fin d → NNReal)
      (N : Set (SpatialCoordinates d)),
      IsOpen N ∧ c ∈ N ∧ ContDiff ℝ ∞ Ψ ∧ LipschitzWith C Ψ ∧
      (∀ i : Fin d, LipschitzWith (B i) (fun x => fderiv ℝ Ψ x (EuclideanSpace.basisFun (Fin d) ℝ i))) ∧
      (∀ (x : SpatialCoordinates d) (t : ℝ), Ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=Ψ x) ∧
      Ψ c=c r ∧ fderiv ℝ (halfspaceExpSum ℓ b n) c (EuclideanSpace.basisFun (Fin d) ℝ r) ≠ 0 ∧
      (∀ x ∈ N, halfspaceExpSum ℓ b n (coordinateLevelMap r Ψ x)=1/2) ∧
      (∀ x ∈ N, halfspaceExpSum ℓ b n x=1/2 ↔ x r=Ψ x) := by
  obtain ⟨he,hr⟩ := halfspaceSmoothInner_boundary_regular ℓ b n hz hc
  have hh := exists_bounded_smooth_coordinate_level_height (halfspaceExpSum ℓ b n)
    (halfspaceExpSum_analytic ℓ b n) c hr
  simpa only [he] using hh

end Carleman
