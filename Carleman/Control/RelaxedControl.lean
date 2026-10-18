module

public import Carleman.Control.PhysicalHUM

/-! Conditional Theorem 7.3 bridge at the original operator level.
The genuine relaxed observation estimate remains an explicit obligation. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman.Physical
variable {X U : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

theorem relaxed_control_of_observation (g : TimeGrid) (M d S C : ℝ)
    (hsmall : g.dt*M ≤ 1/2) (hC : 0 ≤ C)
    (A : X →L[ℝ] X) (hAs : A.IsSymmetric) (hA : ∀ x, 0 ≤ inner ℝ (A x) x)
    (V : Fin g.steps → X →L[ℝ] X) (hVs : ∀ i, (V i).IsSymmetric) (hV : ∀ i, ‖V i‖ ≤ M)
    (B : U →L[ℝ] X)
    (hobs : ∀ p : Fin (g.steps+1) → X, AdjointEquation g.dt (fun i => A+V i) p →
      ‖p 0‖^2 ≤ C*(g.dt*(∑ i : Fin g.steps, ‖B.adjoint (p i.castSucc)‖^2)+
        Real.exp (-2*d*S)*‖p (Fin.last g.steps)‖^2)) :
    ∀ y0 : X, ∃ u : Fin g.steps → U, ∃ y : Fin (g.steps+1) → X,
      y 0 = y0 ∧ ForwardEquation g.dt (fun i => A+V i) B u y ∧
      controlNorm g.dt u ≤ Real.sqrt C*‖y0‖ ∧
      ‖y (Fin.last g.steps)‖ ≤ Real.sqrt C*Real.exp (-d*S)*‖y0‖ := by
  let L := fun i => A+V i
  have hs (i : Fin g.steps) : (L i).IsSymmetric := hAs.add (hVs i)
  have hl (i : Fin g.steps) (x : X) : -M*‖x‖^2 ≤ inner ℝ (L i x) x :=
    stiffness_potential_lower A.toLinearMap (V i).toLinearMap M hA
      (fun z => ((V i).le_opNorm z).trans (mul_le_mul_of_nonneg_right (hV i) (norm_nonneg z))) x
  have he : Real.exp (-d*S)^2 = Real.exp (-2*d*S) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have ho (p : Fin (g.steps+1) → X) (hp : Adjoint g.dt (fun i => (L i).toLinearMap) p) :
      ‖p 0‖^2 ≤ C*(g.dt*(∑ i : Fin g.steps, ‖B.adjoint (p i.castSucc)‖^2)+
        Real.exp (-d*S)^2*‖p (Fin.last g.steps)‖^2) := by
    rw [he]
    exact hobs p ((adjoint_equation_iff (ne_of_gt g.dt_pos) L hs p).mpr hp)
  intro y0
  obtain ⟨u,y,hy0,hy,hu,hterm⟩ := physical_hum_control g.dt M g.dt_pos.le hsmall
    (fun i => (L i).toLinearMap) hl B g.dt_pos hs (Real.exp (-d*S)) C (Real.exp_pos _) hC ho y0
  refine ⟨u,y,hy0,(forward_equation_iff (ne_of_gt g.dt_pos) L B u y).mpr hy,hu,?_⟩
  simpa only [mul_comm (Real.exp (-d*S)) (Real.sqrt C)] using hterm

end Carleman.Physical
