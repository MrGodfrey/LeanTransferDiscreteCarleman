module

public import Carleman.Control.PositiveResolvent

/-! Time iteration for the original reverse estimate, with no invariant
subspace assumption on the stiffness or the time-dependent potential. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1200000
namespace Carleman.Physical
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  {N : ℕ}

theorem adjoint_nonzero (dt : ℝ) (L : Fin N → X →ₗ[ℝ] X) (p : Fin (N+1) → X)
    (hp : Adjoint dt L p) (hT : p (Fin.last N) ≠ 0) : ∀ i, p i ≠ 0 := by
  intro i
  induction i using Fin.reverseInduction with
  | last => exact hT
  | cast i ih =>
    intro hz
    have hh := hp i
    rw [hz,map_zero] at hh
    exact ih hh.symm

theorem exponential_recurrence (a F : Fin (N+1) → ℝ) (hF0 : F 0 = 0)
    (hstep : ∀ i : Fin N, a i.succ ≤ Real.exp (F i.succ-F i.castSucc)*a i.castSucc) :
    ∀ n, a n ≤ Real.exp (F n)*a 0 := by
  intro n
  induction n using Fin.induction with
  | zero => simp only [hF0,Real.exp_zero,one_mul,le_refl]
  | succ i ih =>
    have hh := (hstep i).trans (mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le)
    have he : Real.exp (F i.succ-F i.castSucc)*Real.exp (F i.castSucc) = Real.exp (F i.succ) := by
      rw [← Real.exp_add,sub_add_cancel]
    simpa only [← mul_assoc,he] using hh

theorem adjoint_rayleigh_bound (dt M : ℝ) (hdt : 0 ≤ dt) (hM : 0 ≤ M) (hsmall : dt*M ≤ 1/2)
    (A : X →ₗ[ℝ] X) (hAs : A.IsSymmetric) (hA : ∀ x, 0 ≤ inner ℝ (A x) x)
    (V : Fin N → X →ₗ[ℝ] X) (hV : ∀ i x, ‖V i x‖ ≤ M*‖x‖)
    (p : Fin (N+1) → X) (hp : Adjoint dt (fun i => A+V i) p)
    (hT : p (Fin.last N) ≠ 0) (n : Fin (N+1)) :
    rayleigh A (p n) ≤ rayleigh A (p (Fin.last N))+((N:ℝ)-n.val)*dt*M^2 := by
  have hn := adjoint_nonzero dt (fun i => A+V i) p hp hT
  have hmono : Monotone (fun n : Fin (N+1) => rayleigh A (p n)+(n.val:ℝ)*dt*M^2) := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    have hh := rayleigh_step dt M hdt hM hsmall A (V i) hAs hA (hV i) (p i.castSucc) (hn _)
    rw [hp i] at hh
    simp only [Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one]
    nlinarith only [hh]
  have hh := hmono (Fin.le_last n)
  simp only [Fin.val_last] at hh
  nlinarith only [hh]

/-- The exact terminal Rayleigh quotient controls the full norm ratio. -/
theorem adjoint_reverse_rayleigh [FiniteDimensional ℝ X]
    (dt M : ℝ) (hdt : 0 ≤ dt) (hM : 0 ≤ M) (hsmall : dt*M ≤ 1/2)
    (A : X →ₗ[ℝ] X) (hAs : A.IsSymmetric) (hA : ∀ x, 0 ≤ inner ℝ (A x) x)
    (V : Fin N → X →ₗ[ℝ] X) (hV : ∀ i x, ‖V i x‖ ≤ M*‖x‖)
    (p : Fin (N+1) → X) (hp : Adjoint dt (fun i => A+V i) p) :
    ‖p (Fin.last N)‖ ≤ Real.exp (((N:ℝ)*dt)*rayleigh A (p (Fin.last N))+
      M*((N:ℝ)*dt)+M^2*((N:ℝ)*dt)^2/2)*‖p 0‖ := by
  by_cases hT : p (Fin.last N) = 0
  · rw [hT,norm_zero]
    exact mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have hn := adjoint_nonzero dt (fun i => A+V i) p hp hT
  let R := rayleigh A (p (Fin.last N))
  let F (n : Fin (N+1)) : ℝ := dt*(M+R)*n.val+dt^2*M^2/2*(n.val*(2*(N:ℝ)-n.val-1))
  have hF0 : F 0 = 0 := by simp [F]
  have hFstep (i : Fin N) : F i.succ-F i.castSucc =
      dt*M+dt*(R+((N:ℝ)-i.succ.val)*dt*M^2) := by
    simp only [F,Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one]
    ring
  have hs (i : Fin N) : ‖p i.succ‖ ≤ Real.exp (F i.succ-F i.castSucc)*‖p i.castSucc‖ := by
    have hh := perturbed_resolvent_lower dt M hdt hM A (V i) hAs hA (hV i)
      (p i.succ) (p i.castSucc) (hn _) (hp i)
    have hr := rayleigh_nonneg A hA (p i.succ)
    have hm : 1+dt*M ≤ Real.exp (dt*M) := by simpa only [add_comm] using Real.add_one_le_exp (dt*M)
    have he : 1+dt*rayleigh A (p i.succ) ≤ Real.exp (dt*rayleigh A (p i.succ)) := by
      simpa only [add_comm] using Real.add_one_le_exp (dt*rayleigh A (p i.succ))
    have hprod := mul_le_mul hm he (by positivity : 0 ≤ 1+dt*rayleigh A (p i.succ)) (Real.exp_pos _).le
    have h1 := hh.trans (mul_le_mul_of_nonneg_right hprod (norm_nonneg _))
    rw [← Real.exp_add] at h1
    have hq := adjoint_rayleigh_bound dt M hdt hM hsmall A hAs hA V hV p hp hT i.succ
    have he2 : dt*M+dt*rayleigh A (p i.succ) ≤ F i.succ-F i.castSucc := by
      rw [hFstep]
      have hm := mul_le_mul_of_nonneg_left hq hdt
      change dt*M+dt*rayleigh A (p i.succ) ≤ dt*M+dt*(rayleigh A (p (Fin.last N))+((N:ℝ)-i.succ.val)*dt*M^2)
      linarith only [hm]
    exact h1.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he2) (norm_nonneg _))
  have hh := exponential_recurrence (fun n => ‖p n‖) F hF0 hs (Fin.last N)
  have hf : F (Fin.last N) ≤ ((N:ℝ)*dt)*R+M*((N:ℝ)*dt)+M^2*((N:ℝ)*dt)^2/2 := by
    dsimp [F]
    nlinarith [mul_nonneg (sq_nonneg (dt*M)) (Nat.cast_nonneg N : (0:ℝ) ≤ N)]
  exact hh.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hf) (norm_nonneg _))

end Carleman.Physical
