module

public import Carleman.Control.PhysicalEquations

/-! Explicit joint conclusion for the original physical observation and control statements. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman.Physical
variable {X U : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

def PhysicalObservationControl (g : TimeGrid) (L : Fin g.steps → X →L[ℝ] X)
    (B : U →L[ℝ] X) (C d S : ℝ) : Prop :=
  (∀ p : Fin (g.steps+1) → X, AdjointEquation g.dt L p →
    ‖p 0‖^2 ≤ C*((g.dt*∑ i : Fin g.steps, ‖B.adjoint (p i.castSucc)‖^2)+
      Real.exp (-2*d*S)*‖p (Fin.last g.steps)‖^2)) ∧
  (∀ y0 : X, ∃ u : Fin g.steps → U, ∃ y : Fin (g.steps+1) → X,
    y 0 = y0 ∧ ForwardEquation g.dt L B u y ∧ controlNorm g.dt u ≤ Real.sqrt C*‖y0‖ ∧
      ‖y (Fin.last g.steps)‖ ≤ Real.sqrt C*Real.exp (-d*S)*‖y0‖)

def PhysicalFilteredObservationControl [FiniteDimensional ℝ X]
    (g : TimeGrid) (L : Fin g.steps → X →L[ℝ] X) (B : U →L[ℝ] X)
    (C0 θ d S : ℝ) (F : Submodule ℝ X) : Prop :=
  (∀ p : Fin (g.steps+1) → X, AdjointEquation g.dt L p → p (Fin.last g.steps) ∈ F →
    ‖p 0‖^2 ≤ 2*C0*(g.dt*∑ i : Fin g.steps, ‖B.adjoint (p i.castSucc)‖^2)) ∧
  (∀ y0 : X, ∃ u : Fin g.steps → U, ∃ y : Fin (g.steps+1) → X,
    y 0 = y0 ∧ ForwardEquation g.dt L B u y ∧ controlNorm g.dt u ≤ Real.sqrt (2*C0)*‖y0‖ ∧
      F.starProjection (y (Fin.last g.steps)) = 0 ∧
      ‖y (Fin.last g.steps)‖ ≤ C0*Real.exp (-(1-θ)*d*S)*‖y0‖)

end Carleman.Physical
