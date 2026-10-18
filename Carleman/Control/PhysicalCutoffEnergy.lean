module

public import Carleman.Control.PhysicalWindow

/-! Actual physical-time energy budgets for the explicit cutoff.
Spatial exponential-weight comparison is still a separate obligation. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman.Physical
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

theorem concrete_cutoff_residual [CompleteSpace X] (g : TimeGrid) (a : ℝ) (ha : 0 < a)
    (A : X →L[ℝ] X) (V : Fin g.steps → X →L[ℝ] X) (hSym : ∀ i, (A+V i).IsSymmetric)
    (p : Fin (g.steps+1) → X) (hp : AdjointEquation g.dt (fun i => A+V i) p) (i : Fin g.steps) :
    g.dMinus (cutoffState g (cutoffNodes g a) p) i+A (cutoffState g (cutoffNodes g a) p i) =
      -V i (cutoffState g (cutoffNodes g a) p i)-cutoffRemainder g (cutoffNodes g a) p i :=
  cutoff_residual g A V hSym (cutoffNodes g a) p
    (cutoffNodes_endpoints g a ha).1 (cutoffNodes_endpoints g a ha).2 hp i

theorem cutoffNodes_one_middle (g : TimeGrid) (a : ℝ) (ha : 0 < a) (haT : a ≤ g.period/16)
    (i : Fin g.steps) (hi : i ∈ middleNodes g) : cutoffNodes g a i.castSucc = 1 := by
  obtain ⟨hl,hr⟩ := (Finset.mem_filter.mp hi).2
  apply physicalCutoff_one ha
  change 2*a ≤ min ((i.val:ℝ)*g.dt) (g.period-(i.val:ℝ)*g.dt)
  apply le_min <;> linarith [g.period_pos]

theorem cutoff_remainder_zero (g : TimeGrid) (a : ℝ) (p : Fin (g.steps+1) → X)
    (i : Fin g.steps) (hi : i ∉ transitionNodes g a) :
    cutoffRemainder g (cutoffNodes g a) p i = 0 := by
  have he : cutoffNodes g a i.succ = cutoffNodes g a i.castSucc := by
    by_contra hn
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩)
  rw [cutoffRemainder,he,sub_self,zero_div,zero_smul]

theorem cutoff_remainder_norm_bound (g : TimeGrid) (a K : ℝ) (ha : 0 < a)
    (p : Fin (g.steps+1) → X) (hp : ∀ n, ‖p n‖ ≤ K) (i : Fin g.steps) :
    ‖cutoffRemainder g (cutoffNodes g a) p i‖ ≤ K/a := by
  rw [cutoffRemainder,norm_smul,Real.norm_eq_abs]
  have hh := mul_le_mul (cutoffNodes_difference g a ha i) (hp i.succ)
    (norm_nonneg _) (by positivity : 0 ≤ (1:ℝ)/a)
  simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one] using hh

theorem cutoff_remainder_energy_bound (g : TimeGrid) (a K : ℝ) (ha : 0 < a)
    (hdt : g.dt ≤ a/4) (hK : 0 ≤ K) (p : Fin (g.steps+1) → X) (hp : ∀ n, ‖p n‖ ≤ K) :
    g.dt*(∑ i : Fin g.steps, ‖cutoffRemainder g (cutoffNodes g a) p i‖^2) ≤ 5/a*K^2 := by
  have hsum : (∑ i : Fin g.steps, ‖cutoffRemainder g (cutoffNodes g a) p i‖^2) =
      ∑ i ∈ transitionNodes g a, ‖cutoffRemainder g (cutoffNodes g a) p i‖^2 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    rw [cutoff_remainder_zero g a p i hi,norm_zero,zero_pow (by decide)]
  rw [hsum]
  have hbound : (∑ i ∈ transitionNodes g a, ‖cutoffRemainder g (cutoffNodes g a) p i‖^2) ≤
      (transitionNodes g a).card*(K/a)^2 := by
    calc
      _ ≤ ∑ _i ∈ transitionNodes g a, (K/a)^2 := Finset.sum_le_sum fun i _ =>
        (sq_le_sq₀ (norm_nonneg _) (div_nonneg hK ha.le)).mpr (cutoff_remainder_norm_bound g a K ha p hp i)
      _ = _ := by simp
  calc
    _ ≤ g.dt*((transitionNodes g a).card*(K/a)^2) := mul_le_mul_of_nonneg_left hbound g.dt_pos.le
    _ = (g.dt*(transitionNodes g a).card)*(K/a)^2 := by ring
    _ ≤ (5*a)*(K/a)^2 := mul_le_mul_of_nonneg_right (transitionNodes_measure g a ha hdt) (sq_nonneg _)
    _ = 5/a*K^2 := by field_simp

variable (g : TimeGrid) (M : ℝ) (hM : 0 ≤ M) (hsmall : g.dt*M ≤ 1/2)
  (L : Fin g.steps → X →ₗ[ℝ] X) (hL : ∀ i x, -M*‖x‖^2 ≤ inner ℝ (L i x) x)
  (p : Fin (g.steps+1) → X) (hp : Adjoint g.dt L p)

include hM hsmall hL hp

theorem physical_adjoint_terminal_bound (n : Fin (g.steps+1)) :
    ‖p n‖ ≤ Real.exp (2*M*g.period)*‖p (Fin.last g.steps)‖ := by
  have hh := adjoint_energy g.dt M g.dt_pos.le hM hsmall L hL p hp n (Fin.last g.steps) (Fin.le_last _)
  simp only [Fin.val_last] at hh
  have he : 2*M*((g.steps:ℝ)*g.dt-(n.val:ℝ)*g.dt) ≤ 2*M*g.period := by
    dsimp only [TimeGrid.period]
    nlinarith [mul_nonneg (Nat.cast_nonneg n.val) g.dt_pos.le]
  exact hh.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he) (norm_nonneg _))

theorem physical_cutoff_remainder_energy (a : ℝ) (ha : 0 < a) (hdt : g.dt ≤ a/4) :
    g.dt*(∑ i : Fin g.steps, ‖cutoffRemainder g (cutoffNodes g a) p i‖^2) ≤
      (5/a)*Real.exp (4*M*g.period)*‖p (Fin.last g.steps)‖^2 := by
  have hh := cutoff_remainder_energy_bound g a (Real.exp (2*M*g.period)*‖p (Fin.last g.steps)‖)
    ha hdt (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) p
    (physical_adjoint_terminal_bound g M hM hsmall L hL p hp)
  have he : Real.exp (2*M*g.period)^2 = Real.exp (4*M*g.period) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  rw [mul_pow,he] at hh
  simpa only [mul_assoc] using hh

theorem physical_adjoint_initial_lower (n : Fin (g.steps+1)) :
    Real.exp (-4*M*g.period)*‖p 0‖^2 ≤ ‖p n‖^2 := by
  have hh := adjoint_energy g.dt M g.dt_pos.le hM hsmall L hL p hp 0 n (Fin.zero_le _)
  simp only [Fin.val_zero,Nat.cast_zero] at hh
  have hn : (n.val:ℝ)*g.dt ≤ g.period := mul_le_mul_of_nonneg_right
    (by exact_mod_cast Fin.is_le n) g.dt_pos.le
  have he : 2*M*((n.val:ℝ)*g.dt-(0:ℝ)*g.dt) ≤ 2*M*g.period := by nlinarith only [hn,hM]
  have hb := hh.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he) (norm_nonneg _))
  have hs := (sq_le_sq₀ (norm_nonneg (p 0)) (mul_nonneg (Real.exp_pos _).le (norm_nonneg (p n)))).mpr hb
  have hx := mul_le_mul_of_nonneg_left hs (Real.exp_pos (-4*M*g.period)).le
  have hc : Real.exp (-4*M*g.period)*Real.exp (2*M*g.period)^2 = 1 := by
    rw [pow_two,← Real.exp_add,← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  simpa only [mul_pow,← mul_assoc,hc,one_mul] using hx

theorem physical_middle_energy (hdt : g.dt ≤ g.period/12) :
    (g.period/6)*Real.exp (-4*M*g.period)*‖p 0‖^2 ≤
      g.dt*(∑ i ∈ middleNodes g, ‖p i.castSucc‖^2) := by
  have hs := Finset.sum_le_sum (s := middleNodes g)
    (fun i _ => physical_adjoint_initial_lower g M hM hsmall L hL p hp i.castSucc)
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  have hh := mul_le_mul_of_nonneg_left hs g.dt_pos.le
  have hc := mul_le_mul_of_nonneg_right (middleNodes_measure g hdt)
    (mul_nonneg (Real.exp_pos (-4*M*g.period)).le (sq_nonneg ‖p 0‖))
  nlinarith only [hh,hc]

end Carleman.Physical
