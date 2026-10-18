module

public import Carleman.Control.PhysicalSolutions
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Exact physical-time duality, with observation at p^(n-1). -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman.Physical
variable {X U : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {N : ℕ} (dt : ℝ) (L : Fin N → X →ₗ[ℝ] X)

theorem duality_increment (hL : ∀ i, (L i).IsSymmetric)
    (f : Fin N → X) (y p : Fin (N+1) → X)
    (hy : Forward dt L f y) (hp : Adjoint dt L p) (i : Fin N) :
    inner ℝ (y i.succ) (p i.succ)-inner ℝ (y i.castSucc) (p i.castSucc) =
      dt*inner ℝ (f i) (p i.castSucc) := by
  have he := congrArg (fun x => inner ℝ x (p i.castSucc)) (hy i)
  simp only [step_apply,inner_add_left,real_inner_smul_left] at he
  rw [← hp i,step_apply,inner_add_right,real_inner_smul_right,← hL i]
  linarith only [he]

theorem physical_duality (hL : ∀ i, (L i).IsSymmetric)
    (f : Fin N → X) (y p : Fin (N+1) → X)
    (hy : Forward dt L f y) (hp : Adjoint dt L p) :
    inner ℝ (y (Fin.last N)) (p (Fin.last N))-inner ℝ (y 0) (p 0) =
      dt*∑ i, inner ℝ (f i) (p i.castSucc) := by
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => duality_increment dt L hL f y p hy hp i)
  rw [Finset.sum_sub_distrib,← Finset.mul_sum] at hsum
  have h0 := Fin.sum_univ_succ (fun i => inner ℝ (y i) (p i))
  have hN := Fin.sum_univ_castSucc (fun i => inner ℝ (y i) (p i))
  linarith only [hsum,h0,hN]

theorem control_duality [CompleteSpace X] [CompleteSpace U]
    (hL : ∀ i, (L i).IsSymmetric) (B : U →L[ℝ] X)
    (u : Fin N → U) (y p : Fin (N+1) → X)
    (hy : Forward dt L (fun i => B (u i)) y) (hp : Adjoint dt L p) :
    inner ℝ (y (Fin.last N)) (p (Fin.last N))-inner ℝ (y 0) (p 0) =
      dt*∑ i, inner ℝ (u i) (B.adjoint (p i.castSucc)) := by
  rw [physical_duality dt L hL (fun i => B (u i)) y p hy hp]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (B.adjoint_inner_right (u i) (p i.castSucc)).symm

end Carleman.Physical
