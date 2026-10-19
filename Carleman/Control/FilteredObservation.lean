module

public import Carleman.Control.FilterReverse

/-! The original logarithmic filtering condition absorbs the genuine terminal remainder. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman.Physical

theorem filter_condition_budget (T M Λ θ d S C0 : ℝ) (hC : 1 ≤ C0)
    (hΛ : T*Λ ≤ θ*d*S)
    (hgap : M*T+M^2*T^2/2+Real.log (4*C0)/2 ≤ (1-θ)*d*S) :
    4*C0*Real.exp (-2*d*S)*(filterConstant T M Λ)^2 ≤ 1 := by
  have h4 : 0 < 4*C0 := by linarith
  have hexp : Real.exp (Real.log (4*C0)+(-2*d*S)+2*(T*Λ+M*T+M^2*T^2/2)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith only [hΛ,hgap]
  have he : Real.exp (2*(T*Λ+M*T+M^2*T^2/2)) = (filterConstant T M Λ)^2 := by
    rw [show 2*(T*Λ+M*T+M^2*T^2/2) =
      (T*Λ+M*T+M^2*T^2/2)+(T*Λ+M*T+M^2*T^2/2) by ring,Real.exp_add]
    exact (pow_two _).symm
  rw [Real.exp_add,Real.exp_add,Real.exp_log h4,he] at hexp
  exact hexp

variable {X U : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

theorem filtered_observation_of_relaxed (g : TimeGrid) (M θ d S C0 : ℝ)
    (hM : 0 ≤ M) (hsmall : g.dt*M ≤ 1/2) (hC : 1 ≤ C0)
    (A : X →L[ℝ] X) (hAs : A.IsSymmetric) (hA : ∀ x, 0 ≤ inner ℝ (A x) x)
    (V : Fin g.steps → X →L[ℝ] X) (hVs : ∀ i, (V i).IsSymmetric) (hV : ∀ i, ‖V i‖ ≤ M)
    (B : U →L[ℝ] X)
    (hobs : ∀ p : Fin (g.steps+1) → X, AdjointEquation g.dt (fun i => A+V i) p →
      ‖p 0‖^2 ≤ C0*((g.dt*∑ i : Fin g.steps, ‖B.adjoint (p i.castSucc)‖^2)+
        Real.exp (-2*d*S)*‖p (Fin.last g.steps)‖^2))
    (F : Submodule ℝ X) (hΛ : g.period*filterRayleigh A F ≤ θ*d*S)
    (hgap : M*g.period+M^2*g.period^2/2+Real.log (4*C0)/2 ≤ (1-θ)*d*S)
    (p : Fin (g.steps+1) → X) (hp : AdjointEquation g.dt (fun i => A+V i) p)
    (hF : p (Fin.last g.steps) ∈ F) :
    ‖p 0‖^2 ≤ 2*C0*(g.dt*∑ i : Fin g.steps, ‖B.adjoint (p i.castSucc)‖^2) := by
  have hrev := filter_reverse g M hM hsmall A hAs hA V hVs hV F p hp hF
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
    (filterConstant_pos g.period M (filterRayleigh A F)).le (norm_nonneg _))).mpr hrev
  have hbudget := filter_condition_budget g.period M (filterRayleigh A F) θ d S C0 hC hΛ hgap
  have h1 := mul_le_mul_of_nonneg_left hs
    (mul_nonneg (zero_le_one.trans hC) (Real.exp_pos (-2*d*S)).le)
  have h2 := mul_le_mul_of_nonneg_right hbudget (sq_nonneg ‖p 0‖)
  have hrem : C0*Real.exp (-2*d*S)*‖p (Fin.last g.steps)‖^2 ≤ ‖p 0‖^2/4 := by
    nlinarith only [h1,h2]
  have ho := hobs p hp
  have hn : 0 ≤ C0*(g.dt*∑ i : Fin g.steps, ‖B.adjoint (p i.castSucc)‖^2) :=
    mul_nonneg (zero_le_one.trans hC)
      (mul_nonneg g.dt_pos.le (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  nlinarith only [ho,hrem,hn]

end Carleman.Physical
