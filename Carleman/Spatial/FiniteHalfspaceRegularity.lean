module
public import Carleman.Spatial.WeakConvexHessian
public import Carleman.Spatial.DirichletExhaustionLimit
/-! Genuine smooth inner solutions and a uniform Hessian bound yield full
Dirichlet H² regularity and the original operator domain on finite half-space domains. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem IsWeakNegativeLaplacian.unique_dirichlet (hS : IsOpen S) (hd : 0<d) (hb : Bornology.IsBounded S)
    {u v : WeakSobolevJet d 1 (volume.restrict S) S}
    (hu : u∈dirichletJetSpace S) (hv : v∈dirichletJetSpace S)
    {f : Lp ℝ 2 (volume.restrict S)} (huf : IsWeakNegativeLaplacian u f) (hvf : IsWeakNegativeLaplacian v f) : u=v := by
  let a := boundedDirichletOriginalForm hS hd hb
  obtain ⟨z,hz,hzf⟩ := (dirichlet_operator_graph_iff hS hd hb (WeakSobolevJet.value u) f).mpr ⟨u,rfl,hu,huf⟩
  obtain ⟨w,hw,hwf⟩ := (dirichlet_operator_graph_iff hS hd hb (WeakSobolevJet.value v) f).mpr ⟨v,rfl,hv,hvf⟩
  have hzw : z=w := by
    exact (a.model.resolvent_unique 0 le_rfl f (by simpa only [zero_smul,add_zero] using hzf)).trans
      (a.model.resolvent_unique 0 le_rfl f (by simpa only [zero_smul,add_zero] using hwf)).symm
  apply WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)
  exact hz.symm.trans ((congrArg Subtype.val hzw).trans hw)

theorem finite_halfspace_isOpen {ι : Type*} [Fintype ι]
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ) : IsOpen {x | ∀ i, b i<ℓ i x} := by
  have he : {x | ∀ i, b i<ℓ i x}=⋂ i, {x | b i<ℓ i x} := by ext x; simp
  rw [he]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (ℓ i).continuous

theorem exists_finite_halfspace_dirichlet_H2_solution {ι : Type*} [Fintype ι] (hd : 0<d)
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ)
    (hb : Bornology.IsBounded {x | ∀ i, b i<ℓ i x}) {c : SpatialCoordinates d} (hc : ∀ i, b i<ℓ i c)
    (f : Lp ℝ 2 (volume.restrict {x | ∀ i, b i<ℓ i x})) :
    ∃ v : WeakSobolevJet d 2 (volume.restrict {x | ∀ i, b i<ℓ i x}) {x | ∀ i, b i<ℓ i x},
      WeakSobolevJet.value v∈dirichletSubspace {x | ∀ i, b i<ℓ i x} ∧ negativeLaplacian v=f ∧
      ‖WeakSobolevJet.field 2 v‖^2≤(Fintype.card (Sym (Fin d) 2) : ℝ)^2*‖f‖^2 := by
  let S := {x | ∀ i, b i<ℓ i x}
  have hS : IsOpen S := finite_halfspace_isOpen ℓ b
  obtain ⟨N,hN⟩ := (halfspaceSmoothInner_eventually_mem ℓ b hc).exists
  let T (n : ℕ) := halfspaceSmoothInner ℓ b (N+n)
  have hT (n : ℕ) : IsOpen (T n) := halfspaceSmoothInner_open ℓ b (N+n)
  have hTS (n : ℕ) : T n⊆S := subset_closure.trans (halfspaceSmoothInner_closure_subset ℓ b (N+n))
  have hcT (n : ℕ) : c∈T n := halfspaceSmoothInner_mono ℓ b (Nat.le_add_right N n) hN
  have hm : Monotone T := fun n m hnm => halfspaceSmoothInner_mono ℓ b (Nat.add_le_add_left hnm N)
  have hcover : S⊆⋃ n, T n := by
    intro x hx
    obtain ⟨n,hn⟩ := (halfspaceSmoothInner_eventually_mem ℓ b hx).exists
    exact mem_iUnion.mpr ⟨n,halfspaceSmoothInner_mono ℓ b (Nat.le_add_left n N) hn⟩
  have hsol (n : ℕ) : ∃ U : WeakSobolevJet d 2 (volume.restrict (T n)) (T n),
      WeakSobolevJet.truncate (by decide : 1≤2) U∈dirichletJetSpace (T n) ∧
      negativeLaplacian U=subdomainLp (hTS n) f ∧
      ‖WeakSobolevJet.field 2 U‖≤Real.sqrt (Fintype.card (Sym (Fin d) 2) : ℝ)*‖f‖ := by
    obtain ⟨u,hu,huf⟩ := exists_dirichlet_weak_solution (hT n) hd (hb.subset (hTS n)) (subdomainLp (hTS n) f)
    obtain ⟨U,hU,hUf⟩ := halfspaceSmoothInner_dirichlet_H2 ℓ b (N+n) hb (hcT n) u hu _ huf
    have hUD : WeakSobolevJet.truncate (by decide : 1≤2) U∈dirichletJetSpace (T n) := by rwa [hU]
    refine ⟨U,hUD,hUf,?_⟩
    have hbound := halfspaceSmoothInner_weak_hessian_norm_bound hd ℓ b (N+n) hb (hcT n) ⟨U,hUD⟩
    rw [hUf] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_left (subdomainLp_norm_le (hTS n) f) (Real.sqrt_nonneg _))
  choose U hU hUf hbound using hsol
  obtain ⟨v,hv,hvf,hvn⟩ := exists_dirichlet_H2_of_exhaustion hS hd hb f T hT hTS hm hcover U hU hUf
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) hbound
  refine ⟨v,hv,hvf,?_⟩
  rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)] at hvn
  nlinarith

theorem finite_halfspace_dirichlet_H2_regular {ι : Type*} [Fintype ι] (hd : 0<d)
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ)
    (hb : Bornology.IsBounded {x | ∀ i, b i<ℓ i x}) {c : SpatialCoordinates d} (hc : ∀ i, b i<ℓ i c)
    (u : WeakSobolevJet d 1 (volume.restrict {x | ∀ i, b i<ℓ i x}) {x | ∀ i, b i<ℓ i x})
    (hu : u∈dirichletJetSpace {x | ∀ i, b i<ℓ i x})
    (f : Lp ℝ 2 (volume.restrict {x | ∀ i, b i<ℓ i x})) (hf : IsWeakNegativeLaplacian u f) :
    ∃ v : WeakSobolevJet d 2 (volume.restrict {x | ∀ i, b i<ℓ i x}) {x | ∀ i, b i<ℓ i x},
      WeakSobolevJet.truncate (by decide : 1≤2) v=u ∧ negativeLaplacian v=f ∧
      ‖WeakSobolevJet.field 2 v‖≤(Fintype.card (Sym (Fin d) 2) : ℝ)*‖f‖ := by
  have hS := finite_halfspace_isOpen ℓ b
  obtain ⟨v,hv,hvf,hvn⟩ := exists_finite_halfspace_dirichlet_H2_solution hd ℓ b hb hc f
  have hD : WeakSobolevJet.truncate (by decide : 1≤2) v∈dirichletJetSpace {x | ∀ i, b i<ℓ i x} :=
    (mem_dirichletJetSpace_iff _ hS _).mpr hv
  have hw := negativeLaplacian_isWeak v
  rw [hvf] at hw
  refine ⟨v,hw.unique_dirichlet hS hd hb hD hu hf,hvf,?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))).mp
  rwa [mul_pow]

theorem exists_finite_halfspace_dirichlet_H2_estimate {ι : Type*} [Fintype ι] (hd : 0<d)
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ)
    (hb : Bornology.IsBounded {x | ∀ i, b i<ℓ i x}) {c : SpatialCoordinates d} (hc : ∀ i, b i<ℓ i c) :
    ∃ K : ℝ, 0≤K ∧
      ∀ (u : WeakSobolevJet d 1 (volume.restrict {x | ∀ i, b i<ℓ i x}) {x | ∀ i, b i<ℓ i x}),
        u∈dirichletJetSpace {x | ∀ i, b i<ℓ i x} →
      ∀ f : Lp ℝ 2 (volume.restrict {x | ∀ i, b i<ℓ i x}), IsWeakNegativeLaplacian u f →
      ∃ v : WeakSobolevJet d 2 (volume.restrict {x | ∀ i, b i<ℓ i x}) {x | ∀ i, b i<ℓ i x},
        WeakSobolevJet.truncate (by decide : 1≤2) v=u ∧ negativeLaplacian v=f ∧ ‖v‖≤K*‖f‖ := by
  have hS := finite_halfspace_isOpen ℓ b
  obtain ⟨R,hR0,hR⟩ := hb.exists_pos_norm_le
  let i : Fin d := ⟨0,hd⟩
  have hr : ∀ x∈{x | ∀ i, b i<ℓ i x}, |x i|≤R := fun x hx =>
    (show |x i|≤‖x‖ by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i).trans (hR x hx)
  refine ⟨(2*R)^2+2*R+(Fintype.card (Sym (Fin d) 2) : ℝ),by positivity,?_⟩
  intro u hu f hf
  obtain ⟨v,hv,hvf,hH⟩ := finite_halfspace_dirichlet_H2_regular hd ℓ b hb hc u hu f hf
  have hG := dirichlet_weak_solution_gradient_bound hS i hR0.le hr u hu f hf
  have hV := (dirichlet_poincare hS i hR0.le hr u hu).trans
    (mul_le_mul_of_nonneg_left hG (by positivity : 0≤2*R))
  have h0 : WeakSobolevJet.field 0 v=WeakSobolevJet.field 0 u :=
    congrArg (fun w => WeakSobolevJet.field (0 : Fin 2) w) hv
  have h1 : WeakSobolevJet.field 1 v=WeakSobolevJet.field 1 u :=
    congrArg (fun w => WeakSobolevJet.field (1 : Fin 2) w) hv
  refine ⟨v,hv,hvf,?_⟩
  have hh := WeakSobolevJet.norm_le_sum_fields v
  rw [Fin.sum_univ_three,h0,WeakSobolevJet.norm_zero_field,h1] at hh
  nlinarith

theorem finite_halfspace_dirichlet_domain_le_h2 {ι : Type*} [Fintype ι] (hd : 0<d)
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ)
    (hb : Bornology.IsBounded {x | ∀ i, b i<ℓ i x}) {c : SpatialCoordinates d} (hc : ∀ i, b i<ℓ i c) :
    (boundedDirichletOriginalForm (finite_halfspace_isOpen ℓ b) hd hb).model.domain≤
      sobolevSubspace d 2 (volume.restrict {x | ∀ i, b i<ℓ i x}) {x | ∀ i, b i<ℓ i x} := by
  intro z hz
  let a := boundedDirichletOriginalForm (finite_halfspace_isOpen ℓ b) hd hb
  let f := a.model.operator ⟨z,hz⟩
  obtain ⟨u,huz,hu,huf⟩ := (dirichlet_operator_graph_iff (finite_halfspace_isOpen ℓ b) hd hb z f).mp
    ⟨⟨z,hz⟩,rfl,rfl⟩
  obtain ⟨v,hv,_,_⟩ := finite_halfspace_dirichlet_H2_regular hd ℓ b hb hc u hu f huf
  exact ⟨v,(congrArg WeakSobolevJet.value hv).trans huz⟩

theorem finite_halfspace_dirichlet_domain_eq_h2 {ι : Type*} [Fintype ι] (hd : 0<d)
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ)
    (hb : Bornology.IsBounded {x | ∀ i, b i<ℓ i x}) {c : SpatialCoordinates d} (hc : ∀ i, b i<ℓ i c) :
    (boundedDirichletOriginalForm (finite_halfspace_isOpen ℓ b) hd hb).model.domain=
      sobolevSubspace d 2 (volume.restrict {x | ∀ i, b i<ℓ i x}) {x | ∀ i, b i<ℓ i x} ⊓
        dirichletSubspace {x | ∀ i, b i<ℓ i x} :=
  le_antisymm (le_inf (finite_halfspace_dirichlet_domain_le_h2 hd ℓ b hb hc)
    (boundedDirichletOriginalForm (finite_halfspace_isOpen ℓ b) hd hb).domain_le)
    (h2_dirichlet_le_domain (finite_halfspace_isOpen ℓ b) hd hb)

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 2000000 in
theorem dirichlet_graph_estimate_of_weak_estimate
    (hS : IsOpen S) (hd : 0<d) (hb : Bornology.IsBounded S)
    (hD : (boundedDirichletOriginalForm hS hd hb).model.domain≤sobolevSubspace d 2 (volume.restrict S) S)
    (hreg : ∃ K : ℝ, 0≤K ∧ ∀ (u : WeakSobolevJet d 1 (volume.restrict S) S),
      u∈dirichletJetSpace S → ∀ f : Lp ℝ 2 (volume.restrict S), IsWeakNegativeLaplacian u f →
      ∃ v : WeakSobolevJet d 2 (volume.restrict S) S,
        WeakSobolevJet.truncate (by decide : 1≤2) v=u ∧ negativeLaplacian v=f ∧ ‖v‖≤K*‖f‖) :
    ∃ Creg > (0:ℝ), ∀ z : (boundedDirichletOriginalForm hS hd hb).model.domain,
      ‖domainSobolevJet hS (ae_restrict_mem hS.measurableSet) hD z‖≤
        Creg*‖(boundedDirichletOriginalForm hS hd hb).model.operator z‖ := by
  obtain ⟨K,_,hreg⟩ := hreg
  refine ⟨max 1 K,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro z
  let a := boundedDirichletOriginalForm hS hd hb
  obtain ⟨u,huz,hu,huf⟩ := (dirichlet_operator_graph_iff hS hd hb
    (z : Lp ℝ 2 (volume.restrict S)) (a.model.operator z)).mp ⟨z,rfl,rfl⟩
  obtain ⟨v,hv,_,hvn⟩ := hreg u hu (a.model.operator z) huf
  have he : v=domainSobolevJet hS (ae_restrict_mem hS.measurableSet) hD z := by
    apply WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)
    rw [domainSobolevJet_value]
    exact (congrArg WeakSobolevJet.value hv).trans huz
  calc
    _ = ‖v‖ := congrArg norm he.symm
    _ ≤ max 1 K*‖a.model.operator z‖ :=
      hvn.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

theorem finite_halfspace_dirichlet_graph_estimate {ι : Type*} [Fintype ι] (hd : 0<d)
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ)
    (hb : Bornology.IsBounded {x | ∀ i, b i<ℓ i x}) {c : SpatialCoordinates d} (hc : ∀ i, b i<ℓ i c) :
    let hS := finite_halfspace_isOpen ℓ b
    let a := boundedDirichletOriginalForm hS hd hb
    let hD := finite_halfspace_dirichlet_domain_le_h2 hd ℓ b hb hc
    ∃ Creg > (0:ℝ), ∀ z : a.model.domain,
      ‖domainSobolevJet hS (ae_restrict_mem hS.measurableSet) hD z‖≤Creg*‖a.model.operator z‖ :=
  dirichlet_graph_estimate_of_weak_estimate (finite_halfspace_isOpen ℓ b) hd hb
    (finite_halfspace_dirichlet_domain_le_h2 hd ℓ b hb hc)
    (exists_finite_halfspace_dirichlet_H2_estimate hd ℓ b hb hc)

end Carleman
