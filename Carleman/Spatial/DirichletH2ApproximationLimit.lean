module

public import Carleman.Spatial.DirichletWeakSubsequence
public import Carleman.Spatial.WeakH2BoundedLimit
public import Carleman.Spatial.WeakLaplacianLimit

/-! The domain-exhaustion limit step for Dirichlet regularity: H¹₀
approximants, uniformly bounded candidate Hessians, and eventual local
identities produce an actual H² Dirichlet solution of the original equation.
The construction of the approximants and their bounds remains separate. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem exists_dirichlet_H2_of_bounded_approximants (hS : IsOpen S)
    (f : Lp ℝ 2 (volume.restrict S))
    (U : ℕ → WeakSobolevJet d 1 (volume.restrict S) S)
    (hU : ∀ n, U n ∈ dirichletJetSpace S) {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hb : ∀ n, ‖WeakSobolevJet.field 0 (U n)‖^2 + ‖WeakSobolevJet.field 1 (U n)‖^2 ≤ C₁^2)
    (A : ℕ → Fin d → Fin d → Lp ℝ 2 (volume.restrict S))
    (hA : ∀ i j : Fin d, ∀ᶠ n in atTop, ‖A n i j‖ ≤ C₂)
    (hid : ∀ (i j : Fin d) (φ : SpatialTest S), ∀ᶠ n in atTop,
      inner ℝ (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 (U n)))
        (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ j)) =
      -inner ℝ (A n i j) (φ.toLp (volume.restrict S)))
    (hpde : ∀ φ : SpatialTest S, ∀ᶠ n in atTop,
      weakGradientPairing (U n) φ.sobolevJet = inner ℝ f (φ.toLp (volume.restrict S))) :
    ∃ v : WeakSobolevJet d 2 (volume.restrict S) S,
      WeakSobolevJet.value v ∈ dirichletSubspace S ∧ negativeLaplacian v=f ∧
      ‖WeakSobolevJet.field 2 v‖^2 ≤ (Fintype.card (Sym (Fin d) 2) : ℝ)*C₂^2 ∧
      ‖WeakSobolevJet.field 0 v‖^2 + ‖WeakSobolevJet.field 1 v‖^2 ≤ C₁^2 := by
  obtain ⟨u,hu,hun,φ,hφ,ht⟩ := exists_dirichlet_weak_subsequence U hU hC₁ hb
  let G := fun n i => derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 (U (φ n)))
  obtain ⟨v,hv,hvn⟩ := exists_weakH2_of_gradient_test_limits hS u G (fun n => A (φ n)) hC₂
    (fun i j ψ => hilbert_weak_tendsto_map (ht 1) (derivativeComponentCLM (Sym.cons i Sym.nil))
      (ψ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ j)))
    (fun i j ψ => hφ.tendsto_atTop.eventually (hid i j ψ))
    (fun i j => hφ.tendsto_atTop.eventually (hA i j))
  have huf : IsWeakNegativeLaplacian u f :=
    IsWeakNegativeLaplacian.of_weak_gradient_limit u (fun n => U (φ n)) f (ht 1)
      (fun ψ => hφ.tendsto_atTop.eventually (hpde ψ))
  have hvf := negativeLaplacian_isWeak v
  rw [hv] at hvf
  refine ⟨v,?_,hvf.unique_rhs hS huf,hvn,?_⟩
  · have he := congrArg WeakSobolevJet.value hv
    rw [WeakSobolevJet.truncate_value] at he
    rw [he]
    exact ⟨u,hu,rfl⟩
  · have h0 := congrArg (WeakSobolevJet.field 0) hv
    have h1 := congrArg (WeakSobolevJet.field 1) hv
    change WeakSobolevJet.field 0 v = WeakSobolevJet.field 0 u at h0
    change WeakSobolevJet.field 1 v = WeakSobolevJet.field 1 u at h1
    rw [h0,h1]
    exact hun

end Carleman
