module

public import Carleman.Control.FiniteResolvent
public import Mathlib.Algebra.BigOperators.Fin

/-! Initial and terminal value problems on N+1 physical nodes. The step
index i : Fin N corresponds to manuscript n=i+1, with no periodic wrap. -/
@[expose] public noncomputable section
namespace Carleman.Physical
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  {N : ℕ} (dt : ℝ) (L : Fin N → X →ₗ[ℝ] X)

/-- The actual implicit forward equations, multiplied by dt. -/
def Forward (f : Fin N → X) (y : Fin (N+1) → X) : Prop :=
  ∀ i, step dt (L i) (y i.succ) = y i.castSucc+dt • f i

/-- The actual backward adjoint equations for a self-adjoint spatial family. -/
def Adjoint (p : Fin (N+1) → X) : Prop :=
  ∀ i, step dt (L i) (p i.castSucc) = p i.succ

theorem existsUnique_forward [FiniteDimensional ℝ X]
    (M : ℝ) (hdt : 0 ≤ dt) (hsmall : dt*M ≤ 1/2)
    (hL : ∀ i x, -M*‖x‖^2 ≤ inner ℝ (L i x) x) (y0 : X) (f : Fin N → X) :
    ∃! y : Fin (N+1) → X, y 0 = y0 ∧ Forward dt L f y := by
  let E (i : Fin N) := LinearEquiv.ofBijective (step dt (L i))
    (step_bijective dt M hdt hsmall (L i) (hL i))
  let y : Fin (N+1) → X := Fin.induction y0 (fun i v => (E i).symm (v+dt • f i))
  have hy0 : y 0 = y0 := Fin.induction_zero ..
  have hy : Forward dt L f y := by
    intro i
    change E i (y i.succ) = y i.castSucc+dt • f i
    dsimp only [y]
    rw [Fin.induction_succ,LinearEquiv.apply_symm_apply]
  refine ⟨y,⟨hy0,hy⟩,?_⟩
  intro z hz
  funext n
  induction n using Fin.induction with
  | zero => exact hz.1.trans hy0.symm
  | succ i ih =>
    apply (E i).injective
    change step dt (L i) (z i.succ) = step dt (L i) (y i.succ)
    rw [hz.2 i,hy i,ih]

theorem existsUnique_adjoint [FiniteDimensional ℝ X]
    (M : ℝ) (hdt : 0 ≤ dt) (hsmall : dt*M ≤ 1/2)
    (hL : ∀ i x, -M*‖x‖^2 ≤ inner ℝ (L i x) x) (pT : X) :
    ∃! p : Fin (N+1) → X, p (Fin.last N) = pT ∧ Adjoint dt L p := by
  let E (i : Fin N) := LinearEquiv.ofBijective (step dt (L i))
    (step_bijective dt M hdt hsmall (L i) (hL i))
  let p : Fin (N+1) → X := Fin.reverseInduction pT (fun i v => (E i).symm v)
  have hpT : p (Fin.last N) = pT := Fin.reverseInduction_last
  have hp : Adjoint dt L p := by
    intro i
    change E i (p i.castSucc) = p i.succ
    dsimp only [p]
    rw [Fin.reverseInduction_castSucc,LinearEquiv.apply_symm_apply]
  refine ⟨p,⟨hpT,hp⟩,?_⟩
  intro z hz
  funext n
  induction n using Fin.reverseInduction with
  | last => exact hz.1.trans hpT.symm
  | cast i ih =>
    apply (E i).injective
    change step dt (L i) (z i.castSucc) = step dt (L i) (p i.castSucc)
    rw [hz.2 i,hp i,ih]

end Carleman.Physical
