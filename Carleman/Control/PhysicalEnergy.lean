module

public import Carleman.Control.PhysicalDuality
public import Mathlib.Order.Fin.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Real.Sqrt

/-! Physical-time energy bounds uniform in the number of nodes and the
spatial dimension. No periodic endpoint condition is used. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman.Physical
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  {N : ℕ}

theorem adjoint_energy (dt M : ℝ) (hdt : 0 ≤ dt) (hM : 0 ≤ M) (hsmall : dt*M ≤ 1/2)
    (L : Fin N → X →ₗ[ℝ] X) (hL : ∀ i x, -M*‖x‖^2 ≤ inner ℝ (L i x) x)
    (p : Fin (N+1) → X) (hp : Adjoint dt L p) (j ell : Fin (N+1)) (hj : j ≤ ell) :
    ‖p j‖ ≤ Real.exp (2*M*((ell.val:ℝ)*dt-(j.val:ℝ)*dt))*‖p ell‖ := by
  let r := 2*dt*M
  have hmono : Monotone (fun n : Fin (N+1) => Real.exp (r*n.val)*‖p n‖) := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    have hh := step_inverse_bound dt M hdt hM hsmall (L i) (hL i) (p i.castSucc)
    rw [hp i] at hh
    have hm := mul_le_mul_of_nonneg_left hh (Real.exp_pos (r*i.val)).le
    have he : Real.exp (r*(i.succ.val:ℝ)) = Real.exp (r*i.val)*Real.exp r := by
      rw [Fin.val_succ,Nat.cast_add,Nat.cast_one,mul_add,mul_one,Real.exp_add]
    change Real.exp (r*i.val)*‖p i.castSucc‖ ≤ Real.exp (r*(i.succ.val:ℝ))*‖p i.succ‖
    rw [he]
    simpa only [r,mul_assoc] using hm
  have hh := mul_le_mul_of_nonneg_left (hmono hj) (Real.exp_pos (-r*j.val)).le
  have he : Real.exp (-r*j.val)*Real.exp (r*j.val) = 1 := by rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have he' : Real.exp (-r*j.val)*Real.exp (r*ell.val) =
      Real.exp (2*M*((ell.val:ℝ)*dt-(j.val:ℝ)*dt)) := by rw [← Real.exp_add]; congr 1; dsimp [r]; ring
  simpa only [← mul_assoc,he,he',one_mul] using hh

def partialSum (b : Fin N → ℝ) (n : Fin (N+1)) : ℝ := ∑ i, if i.val < n.val then b i else 0

theorem partialSum_zero (b : Fin N → ℝ) : partialSum b 0 = 0 := by simp [partialSum]

theorem partialSum_succ (b : Fin N → ℝ) (k : Fin N) :
    partialSum b k.succ = partialSum b k.castSucc+b k := by
  have hh (i : Fin N) : (if i.val < k.val+1 then b i else 0) =
      (if i.val < k.val then b i else 0)+(if i=k then b i else 0) := by
    by_cases hik : i=k
    · subst i; simp
    · by_cases hlt : i.val < k.val
      · simp [hlt,hik,show i.val < k.val+1 by omega]
      · have hne : i.val ≠ k.val := fun he => hik (Fin.ext he)
        simp [hlt,hik,show ¬i.val < k.val+1 by omega]
  simp only [partialSum,Fin.val_succ,Fin.val_castSucc,hh,Finset.sum_add_distrib]
  simp

theorem partialSum_le_sum (b : Fin N → ℝ) (hb : ∀ i, 0 ≤ b i) (n : Fin (N+1)) :
    partialSum b n ≤ ∑ i, b i := by
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_rfl
  · exact hb i

/-- Scalar recurrence with the complete l1 forcing budget. -/
theorem forward_recurrence_bound (dt r : ℝ) (hdt : 0 ≤ dt) (hr : 0 ≤ r)
    (a : Fin (N+1) → ℝ) (b : Fin N → ℝ) (ha : ∀ n, 0 ≤ a n) (hb : ∀ i, 0 ≤ b i)
    (hstep : ∀ i, a i.succ ≤ Real.exp r*(a i.castSucc+dt*b i)) (n : Fin (N+1)) :
    a n ≤ Real.exp (r*N)*(a 0+dt*∑ i, b i) := by
  have hanti : Antitone (fun n : Fin (N+1) => Real.exp (-r*n.val)*a n-dt*partialSum b n) := by
    apply Fin.antitone_iff_succ_le.mpr
    intro i
    have hh := mul_le_mul_of_nonneg_left (hstep i) (Real.exp_pos (-r*i.succ.val)).le
    have he : Real.exp (-r*i.succ.val)*Real.exp r = Real.exp (-r*i.val) := by
      rw [← Real.exp_add]; congr 1; simp only [Fin.val_succ,Nat.cast_add,Nat.cast_one]; ring
    rw [← mul_assoc,he,mul_add] at hh
    have he1 : Real.exp (-r*i.val) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hr) (Nat.cast_nonneg _))
    have hb' := mul_le_mul_of_nonneg_right he1 (mul_nonneg hdt (hb i))
    simp only [Fin.val_castSucc,partialSum_succ]
    nlinarith only [hh,hb']
  have hh := hanti (show (0:Fin (N+1)) ≤ n by exact Fin.zero_le n)
  simp only [Fin.val_zero,Nat.cast_zero,mul_zero,Real.exp_zero,one_mul,partialSum_zero,sub_zero] at hh
  have hb' := mul_le_mul_of_nonneg_left (partialSum_le_sum b hb n) hdt
  have hn : (n.val:ℝ) ≤ N := by exact_mod_cast Nat.le_of_lt_succ n.isLt
  have he1 := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn hr)
  have he : Real.exp (r*n.val)*Real.exp (-r*n.val) = 1 := by rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have h1 : Real.exp (-r*n.val)*a n ≤ a 0+dt*∑ i, b i := by linarith only [hh,hb']
  have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (r*n.val)).le
  rw [← mul_assoc,he,one_mul] at h2
  exact h2.trans (mul_le_mul_of_nonneg_right he1 (add_nonneg (ha 0) (mul_nonneg hdt (Finset.sum_nonneg fun i _ => hb i))))

/-- Physical control norm on the N time steps, not on the N+1 state nodes. -/
def controlNorm (dt : ℝ) {U : Type*} [NormedAddCommGroup U] (u : Fin N → U) : ℝ :=
  Real.sqrt (dt*∑ i, ‖u i‖^2)

theorem time_l1_le_l2 (dt : ℝ) (hdt : 0 ≤ dt)
    {U : Type*} [NormedAddCommGroup U] (u : Fin N → U) :
    dt*∑ i, ‖u i‖ ≤ Real.sqrt ((N:ℝ)*dt)*controlNorm dt u := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin N => (1:ℝ)) (fun i => ‖u i‖)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hc
  have hT : 0 ≤ (N:ℝ)*dt := mul_nonneg (Nat.cast_nonneg _) hdt
  have hsum : 0 ≤ dt*∑ i, ‖u i‖^2 := mul_nonneg hdt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hsT := Real.sq_sqrt hT
  have hsU := Real.sq_sqrt hsum
  have hm := mul_le_mul_of_nonneg_left hc (sq_nonneg dt)
  have hprod : (Real.sqrt ((N:ℝ)*dt)*controlNorm dt u)^2 =
      (N:ℝ)*dt*(dt*∑ i, ‖u i‖^2) := by
    rw [mul_pow,hsT,controlNorm,hsU]
  have hsq : (dt*∑ i, ‖u i‖)^2 ≤ (Real.sqrt ((N:ℝ)*dt)*controlNorm dt u)^2 := by
    rw [hprod,mul_pow]; nlinarith only [hm]
  exact (sq_le_sq₀ (mul_nonneg hdt (Finset.sum_nonneg fun _ _ => norm_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp hsq

/-- Uniform C(T,M), independent of the discretization and operator norm. -/
def energyConstant (T M : ℝ) : ℝ := Real.exp (2*M*T)*(1+Real.sqrt T)

theorem energyConstant_pos (T M : ℝ) : 0 < energyConstant T M := by
  unfold energyConstant
  exact mul_pos (Real.exp_pos _) (by positivity)

theorem forward_energy (dt M : ℝ) (hdt : 0 ≤ dt) (hM : 0 ≤ M) (hsmall : dt*M ≤ 1/2)
    (L : Fin N → X →ₗ[ℝ] X) (hL : ∀ i x, -M*‖x‖^2 ≤ inner ℝ (L i x) x)
    {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (B : U →L[ℝ] X) (hB : ‖B‖ ≤ 1) (u : Fin N → U) (y : Fin (N+1) → X)
    (hy : Forward dt L (fun i => B (u i)) y) (n : Fin (N+1)) :
    ‖y n‖ ≤ energyConstant ((N:ℝ)*dt) M*(‖y 0‖+controlNorm dt u) := by
  have hstep (i : Fin N) : ‖y i.succ‖ ≤ Real.exp (2*dt*M)*(‖y i.castSucc‖+dt*‖u i‖) := by
    have hh := step_inverse_bound dt M hdt hM hsmall (L i) (hL i) (y i.succ)
    rw [hy i] at hh
    have hBu : ‖B (u i)‖ ≤ ‖u i‖ := (B.le_opNorm _).trans (by nlinarith [norm_nonneg (u i)])
    have hn := norm_add_le (y i.castSucc) (dt • B (u i))
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hdt] at hn
    have hm := mul_le_mul_of_nonneg_left hBu hdt
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith only [hn,hm]) (Real.exp_pos _).le)
  have hh := forward_recurrence_bound dt (2*dt*M) hdt (by positivity)
    (fun n => ‖y n‖) (fun i => ‖u i‖) (fun n => norm_nonneg _) (fun i => norm_nonneg _) hstep n
  have hl := time_l1_le_l2 dt hdt u
  have he : (2*dt*M)*(N:ℝ) = 2*M*((N:ℝ)*dt) := by ring
  rw [he] at hh
  have hU : 0 ≤ controlNorm dt u := Real.sqrt_nonneg _
  have hR := Real.sqrt_nonneg ((N:ℝ)*dt)
  have hbound : ‖y 0‖+dt*∑ i, ‖u i‖ ≤
      (1+Real.sqrt ((N:ℝ)*dt))*(‖y 0‖+controlNorm dt u) := by
    nlinarith [mul_nonneg hR (norm_nonneg (y 0))]
  exact hh.trans (by simpa only [energyConstant,mul_assoc] using
    mul_le_mul_of_nonneg_left hbound (Real.exp_pos (2*M*((N:ℝ)*dt))).le)

end Carleman.Physical
