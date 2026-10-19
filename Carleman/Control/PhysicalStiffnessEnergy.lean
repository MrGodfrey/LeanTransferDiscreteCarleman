module

public import Carleman.Control.PhysicalEquations

/-! The actual implicit state equation controls the full accumulated stiffness energy. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman.Physical
variable {X U : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] {N : ℕ}

theorem forward_energy_increment (dt : ℝ) (L : Fin N → X →ₗ[ℝ] X)
    (f : Fin N → X) (y : Fin (N+1) → X) (hy : Forward dt L f y) (i : Fin N) :
    ‖y i.succ‖^2-‖y i.castSucc‖^2+‖y i.succ-y i.castSucc‖^2+
      2*dt*inner ℝ (L i (y i.succ)) (y i.succ)=2*dt*inner ℝ (f i) (y i.succ) := by
  have he := congrArg (fun x => inner ℝ x (y i.succ)) (hy i)
  simp only [step_apply,inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq] at he
  rw [norm_sub_sq_real,real_inner_comm (y i.castSucc) (y i.succ)]
  linarith only [he]

theorem forward_energy_balance (dt : ℝ) (L : Fin N → X →ₗ[ℝ] X)
    (f : Fin N → X) (y : Fin (N+1) → X) (hy : Forward dt L f y) :
    ‖y (Fin.last N)‖^2-‖y 0‖^2+(∑ i : Fin N, ‖y i.succ-y i.castSucc‖^2)+
      2*dt*(∑ i : Fin N, inner ℝ (L i (y i.succ)) (y i.succ))=
        2*dt*∑ i : Fin N, inner ℝ (f i) (y i.succ) := by
  have hh := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => forward_energy_increment dt L f y hy i)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum] at hh
  have h0 := Fin.sum_univ_succ (fun i => ‖y i‖^2)
  have hN := Fin.sum_univ_castSucc (fun i => ‖y i‖^2)
  linarith only [hh,h0,hN]

theorem forward_stiffness_budget_of_state_bound
    (dt M Y : ℝ) (hdt : 0 ≤ dt) (hM : 0 ≤ M) (hY : 0 ≤ Y)
    (A : X →ₗ[ℝ] X) (V : Fin N → X →ₗ[ℝ] X)
    (hV : ∀ i x, ‖V i x‖ ≤ M*‖x‖)
    (B : U →L[ℝ] X) (hB : ‖B‖ ≤ 1) (u : Fin N → U) (y : Fin (N+1) → X)
    (hy : Forward dt (fun i => A+V i) (fun i => B (u i)) y)
    (hb : ∀ n, ‖y n‖ ≤ Y) :
    2*dt*(∑ i : Fin N, inner ℝ (A (y i.succ)) (y i.succ)) ≤
      ‖y 0‖^2+(controlNorm dt u)^2+(1+2*M)*((N:ℝ)*dt)*Y^2 := by
  have hpoint (i : Fin N) :
      2*inner ℝ (B (u i)) (y i.succ)-2*inner ℝ (V i (y i.succ)) (y i.succ) ≤
        ‖u i‖^2+(1+2*M)*Y^2 := by
    have hBu : ‖B (u i)‖ ≤ ‖u i‖ := (B.le_opNorm _).trans (by nlinarith [norm_nonneg (u i)])
    have hf := (abs_le.mp (abs_real_inner_le_norm (B (u i)) (y i.succ))).2
    have hpot := (abs_le.mp (abs_real_inner_le_norm (V i (y i.succ)) (y i.succ))).1
    have hf' := mul_le_mul_of_nonneg_right hBu (norm_nonneg (y i.succ))
    have hp' := mul_le_mul_of_nonneg_right (hV i (y i.succ)) (norm_nonneg (y i.succ))
    have hs := (sq_le_sq₀ (norm_nonneg (y i.succ)) hY).mpr (hb i.succ)
    have hms := mul_le_mul_of_nonneg_left hs (show 0 ≤ 1+2*M by positivity)
    nlinarith [sq_nonneg (‖u i‖-‖y i.succ‖)]
  have hsum := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)) hdt
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_add_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  have he := forward_energy_balance dt (fun i => A+V i) (fun i => B (u i)) y hy
  simp only [LinearMap.add_apply,inner_add_left,Finset.sum_add_distrib] at he
  have hn : 0 ≤ ∑ i : Fin N, ‖y i.succ-y i.castSucc‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hu : (controlNorm dt u)^2=dt*∑ i : Fin N, ‖u i‖^2 :=
    Real.sq_sqrt (mul_nonneg hdt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  rw [hu]
  nlinarith [sq_nonneg ‖y (Fin.last N)‖]

theorem forward_stiffness_budget (dt M : ℝ) (hdt : 0 ≤ dt) (hM : 0 ≤ M) (hsmall : dt*M ≤ 1/2)
    (A : X →ₗ[ℝ] X) (hA : ∀ x, 0 ≤ inner ℝ (A x) x)
    (V : Fin N → X →ₗ[ℝ] X) (hV : ∀ i x, ‖V i x‖ ≤ M*‖x‖)
    (B : U →L[ℝ] X) (hB : ‖B‖ ≤ 1) (u : Fin N → U) (y : Fin (N+1) → X)
    (hy : Forward dt (fun i => A+V i) (fun i => B (u i)) y) :
    2*dt*(∑ i : Fin N, inner ℝ (A (y i.succ)) (y i.succ)) ≤
      ‖y 0‖^2+(controlNorm dt u)^2+(1+2*M)*((N:ℝ)*dt)*
        (energyConstant ((N:ℝ)*dt) M*(‖y 0‖+controlNorm dt u))^2 := by
  apply forward_stiffness_budget_of_state_bound dt M _ hdt hM
    (mul_nonneg (energyConstant_pos _ _).le (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)))
    A V hV B hB u y hy
  exact forward_energy dt M hdt hM hsmall (fun i => A+V i)
    (fun i => stiffness_potential_lower A (V i) M hA (hV i)) B hB u y hy

end Carleman.Physical
