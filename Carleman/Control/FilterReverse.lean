module

public import Carleman.Control.ReverseIteration

/-! Original Lemma 7.4, with the actual Rayleigh supremum of the terminal
subspace. No invariance of that subspace is assumed or used. -/
@[expose] public noncomputable section
namespace Carleman.Physical
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- The manuscript's Rayleigh quotient supremum, with Λ_{0}=0. -/
def filterRayleigh (A : X →L[ℝ] X) (F : Submodule ℝ X) : ℝ := by
  classical
  exact if F = ⊥ then 0 else sSup {r : ℝ | ∃ x : X, x ∈ F ∧ x ≠ 0 ∧ r = rayleigh A.toLinearMap x}

theorem rayleigh_le_opNorm (A : X →L[ℝ] X) (x : X) (hx : x ≠ 0) :
    rayleigh A.toLinearMap x ≤ ‖A‖ := by
  apply (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hx))).mpr
  have hc := real_inner_le_norm (A x) x
  have hn := mul_le_mul_of_nonneg_right (A.le_opNorm x) (norm_nonneg x)
  change inner ℝ (A x) x ≤ ‖A‖*‖x‖^2
  nlinarith only [hc,hn]

theorem filterRayleigh_bot (A : X →L[ℝ] X) : filterRayleigh A ⊥ = 0 := by
  simp [filterRayleigh]

theorem rayleigh_le_filterRayleigh (A : X →L[ℝ] X) (F : Submodule ℝ X)
    (x : X) (hFx : x ∈ F) (hx : x ≠ 0) : rayleigh A.toLinearMap x ≤ filterRayleigh A F := by
  have hF : F ≠ ⊥ := by
    intro hh
    rw [hh,Submodule.mem_bot] at hFx
    exact hx hFx
  rw [filterRayleigh,ite_eq_right hF]
  apply le_csSup
  · refine ⟨‖A‖,?_⟩
    intro r hr
    obtain ⟨z,_hz,hz0,rfl⟩ := hr
    exact rayleigh_le_opNorm A z hz0
  · exact ⟨x,hFx,hx,rfl⟩

/-- Exact original K_F, uniform in the fine-grid dimension and operator norm. -/
def filterConstant (T M Λ : ℝ) : ℝ := Real.exp (T*Λ+M*T+M^2*T^2/2)

theorem filterConstant_pos (T M Λ : ℝ) : 0 < filterConstant T M Λ := Real.exp_pos _

/-- Lemma 7.4 for the actual physical-time Hilbert adjoint equations. -/
theorem filter_reverse [FiniteDimensional ℝ X] (g : TimeGrid) (M : ℝ)
    (hM : 0 ≤ M) (hsmall : g.dt*M ≤ 1/2)
    (A : X →L[ℝ] X) (hAs : A.IsSymmetric) (hA : ∀ x, 0 ≤ inner ℝ (A x) x)
    (V : Fin g.steps → X →L[ℝ] X) (hVs : ∀ i, (V i).IsSymmetric) (hV : ∀ i, ‖V i‖ ≤ M)
    (F : Submodule ℝ X) (p : Fin (g.steps+1) → X)
    (hp : AdjointEquation g.dt (fun i => A+V i) p) (hF : p (Fin.last g.steps) ∈ F) :
    ‖p (Fin.last g.steps)‖ ≤ filterConstant g.period M (filterRayleigh A F)*‖p 0‖ := by
  by_cases hz : p (Fin.last g.steps) = 0
  · rw [hz,norm_zero]
    exact mul_nonneg (filterConstant_pos _ _ _).le (norm_nonneg _)
  have hs (i : Fin g.steps) : (A+V i).IsSymmetric := hAs.add (hVs i)
  have hnorm (i : Fin g.steps) (x : X) : ‖V i x‖ ≤ M*‖x‖ :=
    ((V i).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hV i) (norm_nonneg x))
  have hpeq := (adjoint_equation_iff (ne_of_gt g.dt_pos) (fun i => A+V i) hs p).mp hp
  have hh := adjoint_reverse_rayleigh g.dt M g.dt_pos.le hM hsmall A.toLinearMap hAs hA
    (fun i => (V i).toLinearMap) hnorm p hpeq
  have hq := rayleigh_le_filterRayleigh A F (p (Fin.last g.steps)) hF hz
  have he := mul_le_mul_of_nonneg_left hq g.period_pos.le
  change ‖p (Fin.last g.steps)‖ ≤ Real.exp (g.period*rayleigh A.toLinearMap (p (Fin.last g.steps))+
    M*g.period+M^2*g.period^2/2)*‖p 0‖ at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith only [he])) (norm_nonneg _))

end Carleman.Physical
