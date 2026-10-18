module

public import Carleman.Control.PhysicalEquations

/-! Original Lemma 7.1: one C(T,M) before every spatial and temporal
discretization, exact equations and complete initial/terminal state spaces. -/
@[expose] public noncomputable section
open scoped BigOperators
universe u v
namespace Carleman.Physical

/-- Full original physical-time lemma under nonnegative symmetric stiffness,
self-adjoint norm-bounded potentials, and the original control contraction. -/
theorem physical_duality_lemma (T M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (X : Type u) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
      (U : Type v) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      (g : TimeGrid), g.period = T → g.dt*M ≤ 1/2 →
      ∀ (A : X →L[ℝ] X), A.IsSymmetric → (∀ x, 0 ≤ inner ℝ (A x) x) →
      ∀ (V : Fin g.steps → X →L[ℝ] X), (∀ i, (V i).IsSymmetric) → (∀ i, ‖V i‖ ≤ M) →
      ∀ (B : U →L[ℝ] X), ‖B‖ ≤ 1 →
      let L := fun i => A+V i
      (∀ (y0 : X) (u : Fin g.steps → U),
        ∃! y : Fin (g.steps+1) → X, y 0 = y0 ∧ ForwardEquation g.dt L B u y) ∧
      (∀ pT : X, ∃! p : Fin (g.steps+1) → X,
        p (Fin.last g.steps) = pT ∧ AdjointEquation g.dt L p) ∧
      (∀ p : Fin (g.steps+1) → X, AdjointEquation g.dt L p →
        ∀ j ell : Fin (g.steps+1), j ≤ ell →
          ‖p j‖ ≤ Real.exp (2*M*((ell.val:ℝ)*g.dt-(j.val:ℝ)*g.dt))*‖p ell‖) ∧
      (∀ (u : Fin g.steps → U) (y : Fin (g.steps+1) → X), ForwardEquation g.dt L B u y →
        ∀ n, ‖y n‖ ≤ C*(‖y 0‖+controlNorm g.dt u)) ∧
      (∀ (u : Fin g.steps → U) (y p : Fin (g.steps+1) → X),
        ForwardEquation g.dt L B u y → AdjointEquation g.dt L p →
        inner ℝ (y (Fin.last g.steps)) (p (Fin.last g.steps))-inner ℝ (y 0) (p 0) =
          g.dt*∑ i, inner ℝ (u i) (B.adjoint (p i.castSucc))) := by
  refine ⟨energyConstant T M,energyConstant_pos T M,?_⟩
  intro X _ _ _ U _ _ _ g hT hsmall A hAs hA V hVs hV B hB L
  have hs (i : Fin g.steps) : (L i).IsSymmetric := (hAs.add (hVs i))
  have hl (i : Fin g.steps) (x : X) : -M*‖x‖^2 ≤ inner ℝ (L i x) x := by
    exact stiffness_potential_lower A.toLinearMap (V i).toLinearMap M hA
      (fun z => ((V i).le_opNorm z).trans (mul_le_mul_of_nonneg_right (hV i) (norm_nonneg z))) x
  have hdt := ne_of_gt g.dt_pos
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro y0 u
    obtain ⟨y,hy,hunique⟩ := existsUnique_forward g.dt (fun i => (L i).toLinearMap)
      M g.dt_pos.le hsmall hl y0 (fun i => B (u i))
    exact ⟨y,⟨hy.1,(forward_equation_iff hdt L B u y).mpr hy.2⟩,
      fun z hz => hunique z ⟨hz.1,(forward_equation_iff hdt L B u z).mp hz.2⟩⟩
  · intro pT
    obtain ⟨p,hp,hunique⟩ := existsUnique_adjoint g.dt (fun i => (L i).toLinearMap)
      M g.dt_pos.le hsmall hl pT
    exact ⟨p,⟨hp.1,(adjoint_equation_iff hdt L hs p).mpr hp.2⟩,
      fun z hz => hunique z ⟨hz.1,(adjoint_equation_iff hdt L hs z).mp hz.2⟩⟩
  · intro p hp j ell hj
    exact adjoint_energy g.dt M g.dt_pos.le hM hsmall (fun i => (L i).toLinearMap) hl p
      ((adjoint_equation_iff hdt L hs p).mp hp) j ell hj
  · intro u y hy n
    have hh := forward_energy g.dt M g.dt_pos.le hM hsmall (fun i => (L i).toLinearMap) hl
      B hB u y ((forward_equation_iff hdt L B u y).mp hy) n
    change ‖y n‖ ≤ energyConstant g.period M*(‖y 0‖+controlNorm g.dt u) at hh
    simpa only [hT] using hh
  · intro u y p hy hp
    exact control_duality g.dt (fun i => (L i).toLinearMap) hs B u y p
      ((forward_equation_iff hdt L B u y).mp hy) ((adjoint_equation_iff hdt L hs p).mp hp)

end Carleman.Physical
