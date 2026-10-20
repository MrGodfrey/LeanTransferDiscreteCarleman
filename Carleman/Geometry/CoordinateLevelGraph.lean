module
public import Carleman.Geometry.AnalyticLevelCharts
public import Carleman.Spatial.NonlinearGraphShear
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
/-! Nondegenerate original levels give actual coordinate-preserving inverse
charts and locally analytic height functions invariant in the normal coordinate. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology BigOperators ContDiff
namespace Carleman
variable {d : ℕ}

def coordinateLevelMap (r : Fin d) (g : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d) : SpatialCoordinates d :=
  x+(g x-x r) • EuclideanSpace.basisFun (Fin d) ℝ r

theorem coordinateLevelMap_normal (r : Fin d) (g : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d) :
    coordinateLevelMap r g x r=g x := by
  simp only [coordinateLevelMap,PiLp.add_apply,PiLp.smul_apply,EuclideanSpace.basisFun_apply,PiLp.single_apply,ite_true,smul_eq_mul,mul_one]
  ring

theorem coordinateLevelMap_tangent (r : Fin d) (g : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d)
    (i : Fin d) (hi : i ≠ r) : coordinateLevelMap r g x i=x i := by
  simp [coordinateLevelMap,PiLp.add_apply,PiLp.smul_apply,EuclideanSpace.basisFun_apply,Ne.symm hi]

theorem coordinateLevelMap_contDiff (r : Fin d) (g : SpatialCoordinates d → ℝ) {n : WithTop ℕ∞}
    (hg : ContDiff ℝ n g) : ContDiff ℝ n (coordinateLevelMap r g) :=
  contDiff_id.add ((hg.sub (EuclideanSpace.proj r).contDiff).smul contDiff_const)

theorem coordinateLevelMap_hasFDerivAt (r : Fin d) (g : SpatialCoordinates d → ℝ)
    {x : SpatialCoordinates d} (hg : DifferentiableAt ℝ g x) :
    HasFDerivAt (coordinateLevelMap r g)
      ((ContinuousLinearMap.id ℝ (SpatialCoordinates d))+
        (fderiv ℝ g x-EuclideanSpace.proj r).smulRight (EuclideanSpace.basisFun (Fin d) ℝ r)) x :=
  (hasFDerivAt_id x).add ((hg.hasFDerivAt.sub (EuclideanSpace.proj r).hasFDerivAt).smul_const _)

theorem coordinateLevelMap_det (r : Fin d) (g : SpatialCoordinates d → ℝ)
    {x : SpatialCoordinates d} (hg : DifferentiableAt ℝ g x) :
    (fderiv ℝ (coordinateLevelMap r g) x).det=fderiv ℝ g x (EuclideanSpace.basisFun (Fin d) ℝ r) := by
  classical
  rw [(coordinateLevelMap_hasFDerivAt r g hg).fderiv]
  let b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  let L := fderiv ℝ g x-EuclideanSpace.proj r
  let v : Fin d → ℝ := fun j => L (EuclideanSpace.basisFun (Fin d) ℝ j)
  let e : Fin d → ℝ := fun i => if i=r then 1 else 0
  have hm : LinearMap.toMatrix b b
      ((ContinuousLinearMap.id ℝ (SpatialCoordinates d))+L.smulRight (EuclideanSpace.basisFun (Fin d) ℝ r)).toLinearMap =
      1+Matrix.replicateCol Unit e * Matrix.replicateRow Unit v := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    simp [b,v,e,EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,Matrix.mul_apply,Matrix.one_apply]
  change LinearMap.det (((ContinuousLinearMap.id ℝ (SpatialCoordinates d))+L.smulRight (EuclideanSpace.basisFun (Fin d) ℝ r)).toLinearMap)=_
  rw [← LinearMap.det_toMatrix b,hm,Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct,e,v,L,EuclideanSpace.basisFun_apply]

theorem exists_nonzero_coordinate_derivative (g : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d)
    (hx : fderiv ℝ g x ≠ 0) : ∃ r : Fin d, fderiv ℝ g x (EuclideanSpace.basisFun (Fin d) ℝ r) ≠ 0 := by
  by_contra hn
  push Not at hn
  apply hx
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.ext
  intro r
  exact hn r

theorem exists_coordinate_level_chart (r : Fin d) (g : SpatialCoordinates d → ℝ)
    (hg : ContDiff ℝ ω g) (c : SpatialCoordinates d)
    (hc : fderiv ℝ g c (EuclideanSpace.basisFun (Fin d) ℝ r) ≠ 0) :
    ∃ e : OpenPartialHomeomorph (SpatialCoordinates d) (SpatialCoordinates d),
      c ∈ e.source ∧ (∀ x, e x=coordinateLevelMap r g x) ∧
      ContDiffOn ℝ ω e.symm e.target ∧
      (∀ y ∈ e.target, g (e.symm y)=y r) ∧
      (∀ y ∈ e.target, ∀ i : Fin d, i ≠ r → e.symm y i=y i) := by
  let F := coordinateLevelMap r g
  have hF := coordinateLevelMap_contDiff r g hg
  let A := fderiv ℝ F c
  have hdet : A.det ≠ 0 := by rwa [coordinateLevelMap_det r g (hg.differentiable (by simp) c)]
  let L := A.toContinuousLinearEquivOfDetNeZero hdet
  have hd : HasFDerivAt F (L : SpatialCoordinates d →L[ℝ] SpatialCoordinates d) c := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact (hF.differentiable (by simp) c).hasFDerivAt
  let e₀ := hF.contDiffAt.toOpenPartialHomeomorph F hd (by simp)
  have hefun : (e₀ : SpatialCoordinates d → SpatialCoordinates d)=F := rfl
  have hc0 : c ∈ e₀.source := hF.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hcinv : ContDiffAt ℝ ω e₀.symm (e₀ c) := by
    apply e₀.contDiffAt_symm (e₀.map_source hc0)
    · rw [e₀.left_inv hc0]
      exact hd
    · rw [e₀.left_inv hc0]
      exact hF.contDiffAt
  obtain ⟨W,hWsub,hWopen,hWc⟩ := mem_nhds_iff.mp (hcinv.eventually (by simp))
  let e := (e₀.symm.restrOpen W hWopen).symm
  refine ⟨e,⟨hc0,hWc⟩,(fun _ => rfl),?_,?_,?_⟩
  · intro y hy
    have hy' : ContDiffAt ℝ ω e₀.symm y := hWsub hy.2
    exact hy'.contDiffWithinAt
  · intro y hy
    have he := congrArg (fun x : SpatialCoordinates d => x r) (e.right_inv hy)
    change coordinateLevelMap r g (e.symm y) r=y r at he
    rwa [coordinateLevelMap_normal] at he
  · intro y hy i hi
    have he := congrArg (fun x : SpatialCoordinates d => x i) (e.right_inv hy)
    change coordinateLevelMap r g (e.symm y) i=y i at he
    rwa [coordinateLevelMap_tangent r g _ i hi] at he

theorem coordinateLevelMap_constant_normal_invariant (r : Fin d) (a : ℝ)
    (x : SpatialCoordinates d) (t : ℝ) :
    coordinateLevelMap r (fun _ => a) (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=
      coordinateLevelMap r (fun _ => a) x := by
  ext i
  by_cases hi : i=r
  · subst i
    rw [coordinateLevelMap_normal,coordinateLevelMap_normal]
  · rw [coordinateLevelMap_tangent r _ _ i hi,coordinateLevelMap_tangent r _ _ i hi]
    simp [PiLp.add_apply,PiLp.smul_apply,EuclideanSpace.basisFun_apply,Ne.symm hi]

theorem exists_local_coordinate_level_height (r : Fin d) (g : SpatialCoordinates d → ℝ)
    (hg : ContDiff ℝ ω g) (c : SpatialCoordinates d)
    (hc : fderiv ℝ g c (EuclideanSpace.basisFun (Fin d) ℝ r) ≠ 0) :
    ∃ (ψ : SpatialCoordinates d → ℝ) (V W : Set (SpatialCoordinates d)),
      IsOpen V ∧ c ∈ V ∧ IsOpen W ∧ c ∈ W ∧
      ContDiffOn ℝ ω ψ V ∧ ψ c=c r ∧
      (∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x) ∧
      (∀ x ∈ V, g (coordinateLevelMap r ψ x)=g c) ∧
      (∀ x ∈ V ∩ W, g x=g c ↔ x r=ψ x) := by
  obtain ⟨e,hec,he,hie,hlevel,htangent⟩ := exists_coordinate_level_chart r g hg c hc
  let Q := coordinateLevelMap r (fun _ => g c)
  have hQ : ContDiff ℝ ω Q := coordinateLevelMap_contDiff r _ contDiff_const
  let V := Q ⁻¹' e.target
  have hV : IsOpen V := e.open_target.preimage hQ.continuous
  have hQc : Q c=e c := (he c).symm
  have hcV : c ∈ V := by change Q c ∈ e.target; rw [hQc]; exact e.map_source hec
  let ψ := fun x => e.symm (Q x) r
  have hψ : ContDiffOn ℝ ω ψ V := by
    intro x hx
    have hh := hie.contDiffAt (e.open_target.mem_nhds hx)
    exact ((EuclideanSpace.proj r).contDiff.contDiffAt.comp x (hh.comp x hQ.contDiffAt)).contDiffWithinAt
  have hgraph (x) (hx : x ∈ V) : coordinateLevelMap r ψ x=e.symm (Q x) := by
    ext i
    by_cases hi : i=r
    · subst i
      exact coordinateLevelMap_normal r ψ x
    · rw [coordinateLevelMap_tangent r ψ x i hi,htangent (Q x) hx i hi]
      exact (coordinateLevelMap_tangent r (fun _ => g c) x i hi).symm
  refine ⟨ψ,V,e.source,hV,hcV,e.open_source,hec,hψ,?_,?_,?_,?_⟩
  · change e.symm (Q c) r=c r
    rw [hQc,e.left_inv hec]
  · intro x t
    change e.symm (Q (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)) r=e.symm (Q x) r
    exact congrArg (fun y => e.symm y r) (coordinateLevelMap_constant_normal_invariant r (g c) x t)
  · intro x hx
    rw [hgraph x hx,hlevel (Q x) hx]
    exact coordinateLevelMap_normal r (fun _ => g c) x
  · intro x hx
    constructor
    · intro hgx
      have heQ : e x=Q x := by rw [he]; dsimp only [Q,coordinateLevelMap]; rw [hgx]
      change x r=e.symm (Q x) r
      rw [← heQ,e.left_inv hx.2]
    · intro hxr
      have hfix : coordinateLevelMap r ψ x=x := by
        simp only [coordinateLevelMap,← hxr,sub_self,zero_smul,add_zero]
      rw [← hfix,hgraph x hx.1,hlevel (Q x) hx.1]
      exact coordinateLevelMap_normal r (fun _ => g c) x

theorem exists_local_coordinate_level_height_of_regular (g : SpatialCoordinates d → ℝ)
    (hg : ContDiff ℝ ω g) (c : SpatialCoordinates d)
    (hc : fderiv ℝ g c ≠ 0) :
    ∃ (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (V W : Set (SpatialCoordinates d)),
      IsOpen V ∧ c ∈ V ∧ IsOpen W ∧ c ∈ W ∧
      ContDiffOn ℝ ω ψ V ∧ ψ c=c r ∧
      (∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x) ∧
      (∀ x ∈ V, g (coordinateLevelMap r ψ x)=g c) ∧
      (∀ x ∈ V ∩ W, g x=g c ↔ x r=ψ x) := by
  obtain ⟨r,hr⟩ := exists_nonzero_coordinate_derivative g c hc
  exact ⟨r,exists_local_coordinate_level_height r g hg c hr⟩

theorem halfspaceSmoothInner_coordinate_level_height {ι : Type*} [Fintype ι]
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ) (n : ℕ)
    {z : SpatialCoordinates d} (hz : z ∈ halfspaceSmoothInner ℓ b n)
    {c : SpatialCoordinates d} (hc : c ∈ frontier (halfspaceSmoothInner ℓ b n)) :
    ∃ (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (V W : Set (SpatialCoordinates d)),
      IsOpen V ∧ c ∈ V ∧ IsOpen W ∧ c ∈ W ∧
      ContDiffOn ℝ ω ψ V ∧ ψ c=c r ∧
      (∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x) ∧
      (∀ x ∈ V, halfspaceExpSum ℓ b n (coordinateLevelMap r ψ x)=1/2) ∧
      (∀ x ∈ V ∩ W, halfspaceExpSum ℓ b n x=1/2 ↔ x r=ψ x) := by
  obtain ⟨he,hr⟩ := halfspaceSmoothInner_boundary_regular ℓ b n hz hc
  have hh := exists_local_coordinate_level_height_of_regular (halfspaceExpSum ℓ b n)
    (halfspaceExpSum_analytic ℓ b n) c hr
  simpa only [he] using hh

end Carleman

