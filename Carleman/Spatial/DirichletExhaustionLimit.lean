module

public import Carleman.Spatial.DirichletH2ApproximationLimit
public import Carleman.Spatial.DirichletExtensionHessianTest
public import Carleman.Spatial.DirichletSubdomainSolve
public import Carleman.Spatial.SpatialTestExhaustion

/-! The actual domain-exhaustion passage for Dirichlet regularity.
Given genuine H² solutions on an increasing open exhaustion and a uniform
Hessian bound, all global approximation identities and H¹ bounds are
proved internally. Smooth inner-domain regularity is not assumed proved. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem exists_dirichlet_H2_of_exhaustion (hS : IsOpen S) (hd : 0 < d)
    (hb : Bornology.IsBounded S) (f : Lp ℝ 2 (volume.restrict S))
    (T : ℕ → Set (SpatialCoordinates d)) (hT : ∀ n, IsOpen (T n)) (hTS : ∀ n, T n ⊆ S)
    (hm : Monotone T) (hc : S ⊆ ⋃ n, T n)
    (u : ∀ n, WeakSobolevJet d 2 (volume.restrict (T n)) (T n))
    (hu : ∀ n, WeakSobolevJet.truncate (by decide : 1 ≤ 2) (u n) ∈ dirichletJetSpace (T n))
    (hf : ∀ n, negativeLaplacian (u n) = subdomainLp (hTS n) f)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ n, ‖WeakSobolevJet.field 2 (u n)‖ ≤ C) :
    ∃ v : WeakSobolevJet d 2 (volume.restrict S) S,
      WeakSobolevJet.value v ∈ dirichletSubspace S ∧ negativeLaplacian v = f ∧
      ‖WeakSobolevJet.field 2 v‖^2 ≤ (Fintype.card (Sym (Fin d) 2) : ℝ)*C^2 := by
  let U := fun n => WeakSobolevJet.extendDirichlet S (hT n)
    (WeakSobolevJet.truncate (by decide : 1 ≤ 2) (u n)) (hu n)
  let A := fun n i j => subdomainZeroExtend S (hT n).measurableSet
    (derivativeComponent (Sym.cons j (Sym.cons i Sym.nil)) (WeakSobolevJet.field 2 (u n)))
  have huf (n : ℕ) : IsWeakNegativeLaplacian
      (WeakSobolevJet.truncate (by decide : 1 ≤ 2) (u n)) (subdomainLp (hTS n) f) := by
    rw [← hf n]
    exact negativeLaplacian_isWeak (u n)
  obtain ⟨R,hR0,hR⟩ := hb.exists_pos_norm_le
  let i : Fin d := ⟨0,hd⟩
  have hr : ∀ x ∈ S, |x i| ≤ R := fun x hx =>
    (show |x i| ≤ ‖x‖ by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i).trans (hR x hx)
  obtain ⟨v,hv,hvf,hvn,_⟩ := exists_dirichlet_H2_of_bounded_approximants hS f U
    (fun n => WeakSobolevJet.extendDirichlet_mem hS (hT n) (hTS n) _ (hu n))
    (C₁ := ((2*R)^2+2*R)*‖f‖) (by positivity) hC
    (fun n => dirichlet_subdomain_energy_bound (hT n) (hTS n) i hR0.le hr _ (hu n) f (huf n))
    A (fun i j => Eventually.of_forall fun n => by
      change ‖subdomainZeroExtend S (hT n).measurableSet _‖ ≤ C
      rw [subdomainZeroExtend_norm (hT n).measurableSet (hTS n)]
      exact (derivativeComponent_norm_le _ _).trans (hbound n)) (by
    intro i j φ
    filter_upwards [φ.eventually_support_subset T hT hm hc] with n hn
    let ψ : SpatialTest (T n) := ⟨φ.value,φ.smooth,φ.compact,hn⟩
    have he : ψ.monoDomain (hTS n) = φ := by cases φ; rfl
    have hid := WeakSobolevJet.extendDirichlet_hessian_test (hT n) (hTS n) (u n) (hu n) i j ψ
    rw [he] at hid
    exact hid) (by
    intro φ
    filter_upwards [φ.eventually_support_subset T hT hm hc] with n hn
    let ψ : SpatialTest (T n) := ⟨φ.value,φ.smooth,φ.compact,hn⟩
    have he : ψ.monoDomain (hTS n) = φ := by cases φ; rfl
    have hid := WeakSobolevJet.extendDirichlet_poisson_test hS (hT n) (hTS n) _ (hu n) f (huf n) ψ
    rw [he] at hid
    exact hid)
  exact ⟨v,hv,hvf,hvn⟩

end Carleman
