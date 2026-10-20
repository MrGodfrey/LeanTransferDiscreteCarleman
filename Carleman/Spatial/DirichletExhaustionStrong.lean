module
public import Carleman.Spatial.DirichletSubdomainSolve
public import Carleman.Spatial.SpatialTestExhaustion
public import Carleman.Spatial.FiniteHalfspaceRegularity
/-! Strong H¹ convergence of actual inner-domain Poisson solves to the same original solution. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman
variable {d : ℕ} {S T : Set (SpatialCoordinates d)}

theorem WeakSobolevJet.extendDirichlet_pairing_extend (hT : IsOpen T) (hTS : T⊆S)
    (u v : WeakSobolevJet d 1 (volume.restrict T) T)
    (hu : u∈dirichletJetSpace T) (hv : v∈dirichletJetSpace T) :
    weakGradientPairing (WeakSobolevJet.extendDirichlet S hT u hu) (WeakSobolevJet.extendDirichlet S hT v hv)=weakGradientPairing u v := by
  rw [weakGradientPairing_apply,weakGradientPairing_apply]
  change inner ℝ (subdomainZeroExtend S hT.measurableSet (WeakSobolevJet.field 1 u))
    (subdomainZeroExtend S hT.measurableSet (WeakSobolevJet.field 1 v))=_
  rw [subdomainZeroExtend_inner hT.measurableSet hTS,subdomainLp_zeroExtend hT.measurableSet hTS]

theorem IsWeakNegativeLaplacian.subdomain_orthogonal (hS : IsOpen S) (hT : IsOpen T) (hTS : T⊆S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S)
    (f : Lp ℝ 2 (volume.restrict S)) (huf : IsWeakNegativeLaplacian u f)
    (v : WeakSobolevJet d 1 (volume.restrict T) T) (hv : v∈dirichletJetSpace T)
    (hvf : IsWeakNegativeLaplacian v (subdomainLp hTS f))
    (w : WeakSobolevJet d 1 (volume.restrict T) T) (hw : w∈dirichletJetSpace T) :
    inner ℝ (WeakSobolevJet.field 1 (u-WeakSobolevJet.extendDirichlet S hT v hv))
      (WeakSobolevJet.field 1 (WeakSobolevJet.extendDirichlet S hT w hw))=0 := by
  have hE := WeakSobolevJet.extendDirichlet_mem hS hT hTS w hw
  have h1 := (isWeakNegativeLaplacian_iff_dirichlet hS u f).mp huf _ hE
  have h2 := (isWeakNegativeLaplacian_iff_dirichlet hT v _).mp hvf w hw
  have hload : inner ℝ f (WeakSobolevJet.value (WeakSobolevJet.extendDirichlet S hT w hw))=
      inner ℝ (subdomainLp hTS f) (WeakSobolevJet.value w) := by
    rw [WeakSobolevJet.extendDirichlet_value]
    calc
      _ = inner ℝ (subdomainZeroExtend S hT.measurableSet (WeakSobolevJet.value w)) f := real_inner_comm _ _
      _ = _ := (subdomainZeroExtend_inner hT.measurableSet hTS (WeakSobolevJet.value w) f).trans
        (real_inner_comm _ _)
  change inner ℝ (WeakSobolevJet.field 1 u-WeakSobolevJet.field 1 (WeakSobolevJet.extendDirichlet S hT v hv))
    (WeakSobolevJet.field 1 (WeakSobolevJet.extendDirichlet S hT w hw))=0
  rw [inner_sub_left]
  change weakGradientPairing u (WeakSobolevJet.extendDirichlet S hT w hw)-
    weakGradientPairing (WeakSobolevJet.extendDirichlet S hT v hv) (WeakSobolevJet.extendDirichlet S hT w hw)=0
  rw [h1,WeakSobolevJet.extendDirichlet_pairing_extend hT hTS,h2,hload,sub_self]

theorem dirichlet_subdomain_gradient_best_test (hS : IsOpen S) (hT : IsOpen T) (hTS : T⊆S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S)
    (f : Lp ℝ 2 (volume.restrict S)) (huf : IsWeakNegativeLaplacian u f)
    (v : WeakSobolevJet d 1 (volume.restrict T) T) (hv : v∈dirichletJetSpace T)
    (hvf : IsWeakNegativeLaplacian v (subdomainLp hTS f))
    (φ : SpatialTest S) (hφ : tsupport φ.value⊆T) :
    ‖WeakSobolevJet.field 1 (u-WeakSobolevJet.extendDirichlet S hT v hv)‖≤
      ‖WeakSobolevJet.field 1 (u-φ.sobolevJet)‖ := by
  let ψ : SpatialTest T := ⟨φ.value,φ.smooth,φ.compact,hφ⟩
  have heψ : WeakSobolevJet.extendDirichlet S hT ψ.sobolevJet (test_mem_dirichletJetSpace T ψ)=φ.sobolevJet := by
    rw [WeakSobolevJet.extendDirichlet_test hS hT hTS]
  have ho := IsWeakNegativeLaplacian.subdomain_orthogonal hS hT hTS u f huf v hv hvf v hv
  have hp := IsWeakNegativeLaplacian.subdomain_orthogonal hS hT hTS u f huf v hv hvf ψ.sobolevJet (test_mem_dirichletJetSpace T ψ)
  rw [heψ] at hp
  let e := WeakSobolevJet.field 1 (u-WeakSobolevJet.extendDirichlet S hT v hv)
  have hid : ‖e‖^2=inner ℝ e (WeakSobolevJet.field 1 (u-φ.sobolevJet)) := by
    rw [← real_inner_self_eq_norm_sq]
    change inner ℝ e (WeakSobolevJet.field 1 u-WeakSobolevJet.field 1 (WeakSobolevJet.extendDirichlet S hT v hv))=
      inner ℝ e (WeakSobolevJet.field 1 u-WeakSobolevJet.field 1 φ.sobolevJet)
    rw [inner_sub_right,inner_sub_right,ho,hp]
  have hc := real_inner_le_norm e (WeakSobolevJet.field 1 (u-φ.sobolevJet))
  rw [← hid] at hc
  by_contra hn
  have hepos : 0<‖e‖ := lt_of_le_of_lt (norm_nonneg _) (lt_of_not_ge hn)
  nlinarith

theorem dirichlet_subdomain_norm_best_test (hS : IsOpen S) (hT : IsOpen T) (hTS : T⊆S)
    (i : Fin d) {R : ℝ} (hR0 : 0≤R) (hR : ∀ x∈S, |x i|≤R)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u∈dirichletJetSpace S)
    (f : Lp ℝ 2 (volume.restrict S)) (huf : IsWeakNegativeLaplacian u f)
    (v : WeakSobolevJet d 1 (volume.restrict T) T) (hv : v∈dirichletJetSpace T)
    (hvf : IsWeakNegativeLaplacian v (subdomainLp hTS f))
    (φ : SpatialTest S) (hφ : tsupport φ.value⊆T) :
    ‖u-WeakSobolevJet.extendDirichlet S hT v hv‖≤(2*R+1)*‖u-φ.sobolevJet‖ := by
  let e := u-WeakSobolevJet.extendDirichlet S hT v hv
  have heD : e∈dirichletJetSpace S :=
    (dirichletJetSpace S).sub_mem hu (WeakSobolevJet.extendDirichlet_mem hS hT hTS v hv)
  have hp := dirichlet_poincare hS i hR0 hR e heD
  have hn := WeakSobolevJet.norm_le_sum_fields e
  rw [Fin.sum_univ_two,WeakSobolevJet.norm_zero_field] at hn
  have he : ‖e‖≤(2*R+1)*‖WeakSobolevJet.field 1 e‖ := by nlinarith
  exact he.trans (mul_le_mul_of_nonneg_left
    ((dirichlet_subdomain_gradient_best_test hS hT hTS u f huf v hv hvf φ hφ).trans
      (WeakSobolevJet.norm_field_le 1 (u-φ.sobolevJet))) (by positivity))

theorem dirichlet_exhaustion_strong_H1 (hS : IsOpen S) (hd : 0<d) (hb : Bornology.IsBounded S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u∈dirichletJetSpace S)
    (f : Lp ℝ 2 (volume.restrict S)) (huf : IsWeakNegativeLaplacian u f)
    (T : ℕ → Set (SpatialCoordinates d)) (hT : ∀ n, IsOpen (T n)) (hTS : ∀ n, T n⊆S)
    (hm : Monotone T) (hcover : S⊆⋃ n, T n)
    (v : ∀ n, WeakSobolevJet d 1 (volume.restrict (T n)) (T n))
    (hv : ∀ n, v n∈dirichletJetSpace (T n))
    (hvf : ∀ n, IsWeakNegativeLaplacian (v n) (subdomainLp (hTS n) f)) :
    Tendsto (fun n => WeakSobolevJet.extendDirichlet S (hT n) (v n) (hv n)) atTop (𝓝 u) := by
  obtain ⟨R,hR0,hR⟩ := hb.exists_pos_norm_le
  let i : Fin d := ⟨0,hd⟩
  have hr : ∀ x∈S, |x i|≤R := fun x hx =>
    (show |x i|≤‖x‖ by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i).trans (hR x hx)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨w,hw,hew⟩ := Metric.mem_closure_iff.mp hu (ε/(2*R+1)) (by positivity)
  obtain ⟨φ,rfl⟩ := exists_test_of_mem_test_span hS hw
  obtain ⟨N,hN⟩ := eventually_atTop.mp (φ.eventually_support_subset T hT hm hcover)
  refine ⟨N,fun n hn => ?_⟩
  rw [dist_comm,dist_eq_norm]
  have he := dirichlet_subdomain_norm_best_test hS (hT n) (hTS n) i hR0.le hr u hu f huf
    (v n) (hv n) (hvf n) φ (hN n hn)
  have hnear : ‖u-φ.sobolevJet‖<ε/(2*R+1) := by simpa only [dist_eq_norm] using hew
  exact he.trans_lt ((mul_lt_mul_of_pos_left hnear (by positivity : 0<2*R+1)).trans_eq
    (mul_div_cancel₀ ε (by positivity : (2*R+1)≠0)))

end Carleman
