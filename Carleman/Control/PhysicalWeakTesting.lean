module

public import Carleman.Control.PhysicalEquations

/-! Exact summation by parts for arbitrary tests of the original physical forward equation. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace Carleman.Physical
variable {X U : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] {N : ℕ}

theorem physical_summation_by_parts (y φ : Fin (N+1) → X) :
    (∑ i : Fin N, inner ℝ (y i.succ-y i.castSucc) (φ i.castSucc)) =
      inner ℝ (y (Fin.last N)) (φ (Fin.last N))-inner ℝ (y 0) (φ 0)-
        ∑ i : Fin N, inner ℝ (y i.succ) (φ i.succ-φ i.castSucc) := by
  have hpoint (i : Fin N) :
      inner ℝ (y i.succ-y i.castSucc) (φ i.castSucc)+
        inner ℝ (y i.succ) (φ i.succ-φ i.castSucc)=
      inner ℝ (y i.succ) (φ i.succ)-inner ℝ (y i.castSucc) (φ i.castSucc) := by
    simp only [inner_sub_left,inner_sub_right]
    ring
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i _ => hpoint i)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib] at hs
  have h0 := Fin.sum_univ_succ (fun i => inner ℝ (y i) (φ i))
  have hN := Fin.sum_univ_castSucc (fun i => inner ℝ (y i) (φ i))
  linarith only [hs,h0,hN]

theorem forward_equation_weak_identity {dt : ℝ} (hdt : dt ≠ 0)
    (L : Fin N → X →L[ℝ] X) (B : U →L[ℝ] X)
    (u : Fin N → U) (y φ : Fin (N+1) → X) (hy : ForwardEquation dt L B u y) :
    -(∑ i : Fin N, inner ℝ (y i.succ) (φ i.succ-φ i.castSucc))+
      dt*(∑ i : Fin N, inner ℝ (L i (y i.succ)) (φ i.castSucc))=
      dt*(∑ i : Fin N, inner ℝ (B (u i)) (φ i.castSucc))+
        inner ℝ (y 0) (φ 0)-inner ℝ (y (Fin.last N)) (φ (Fin.last N)) := by
  have hpoint (i : Fin N) := congrArg (fun x => dt*inner ℝ x (φ i.castSucc)) (hy i)
  simp only [inner_add_left,real_inner_smul_left,mul_add,← mul_assoc,mul_inv_cancel₀ hdt,one_mul] at hpoint
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i _ => hpoint i)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hs
  have ht := physical_summation_by_parts y φ
  linarith only [hs,ht]

end Carleman.Physical
