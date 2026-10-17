module

public import Carleman.Periodic.LinearMap

/-!
# Conforming reconstruction and its mass adjoint

`paper/main.tex:392–406` gives `R : X → V ⊆ H`, its mass adjoint `J : H → X`,
`Q = R J : H → V`, and `G = J R : X → X`. We represent the conforming space
as a real submodule of `H`, retaining the inclusion explicitly in `RH` and `QH`.
No energy norm on `V` is asserted here. The defining mass-adjoint equality is
original discrete data, not a claimed new theorem constructing the adjoint.

The algebra needs neither completeness nor finite dimensionality, and hence
applies in particular to the paper's real Hilbert `H` and finite-dimensional
real Hilbert `X_h`. Injectivity of `R` is used only where explicitly stated
(the injectivity clause of (N1)). No projection or identity is postulated.
-/

@[expose] public section

namespace Carleman

variable {H X : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- The time-independent reconstruction and the original mass interface. -/
structure Reconstruction (V : Submodule ℝ H) (X : Type*)
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] where
  R : X →ₗ[ℝ] V
  J : H →ₗ[ℝ] X
  mass_adjoint : ∀ (v : H) (z : X), inner ℝ (J v) z = inner ℝ v (R z : H)

namespace Reconstruction

variable {V : Submodule ℝ H} (r : Reconstruction V X)

/-- Reconstruction followed by the conforming inclusion into `H`. -/
def RH : X →ₗ[ℝ] H := V.subtype.comp r.R

/-- The paper's `Q = R J`, with values still in the conforming space. -/
def Q : H →ₗ[ℝ] V := r.R.comp r.J

/-- `Q` viewed in the ambient continuous space, for inner products and errors. -/
def QH : H →ₗ[ℝ] H := V.subtype.comp r.Q

/-- The paper's induced mass `G = J R`, with the inclusion made explicit. -/
def G : X →ₗ[ℝ] X := r.J.comp r.RH

@[simp] theorem RH_apply (z : X) : r.RH z = (r.R z : H) := rfl
@[simp] theorem Q_apply (v : H) : r.Q v = r.R (r.J v) := rfl
@[simp] theorem QH_apply (v : H) : r.QH v = r.RH (r.J v) := rfl
@[simp] theorem G_apply (z : X) : r.G z = r.J (r.RH z) := rfl

theorem R_comp_G : r.R.comp r.G = r.Q.comp r.RH := rfl
theorem J_comp_QH : r.J.comp r.QH = r.G.comp r.J := rfl

/-- Reconstruction and the mass adjoint in the other slot order. -/
theorem inner_RH (z : X) (v : H) :
    inner ℝ (r.RH z) v = inner ℝ z (r.J v) := by
  rw [RH_apply, real_inner_comm, ← r.mass_adjoint, real_inner_comm]

theorem inner_G (z w : X) :
    inner ℝ (r.G z) w = inner ℝ (r.RH z) (r.RH w) :=
  r.mass_adjoint (r.RH z) w

theorem G_symmetric (z w : X) : inner ℝ (r.G z) w = inner ℝ z (r.G w) := by
  rw [r.inner_G, real_inner_comm (r.G w), r.inner_G, real_inner_comm]

theorem G_nonneg (z : X) : 0 ≤ inner ℝ (r.G z) z := by
  rw [r.inner_G]
  exact real_inner_self_nonneg

theorem inner_G_self_eq_zero (z : X) : inner ℝ (r.G z) z = 0 ↔ r.R z = 0 := by
  rw [r.inner_G, inner_self_eq_zero]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem G_positive (hR : Function.Injective r.R) {z : X} (hz : z ≠ 0) :
    0 < inner ℝ (r.G z) z := by
  refine lt_of_le_of_ne (r.G_nonneg z) ?_
  intro h
  have hr := (r.inner_G_self_eq_zero z).mp h.symm
  exact hz (hR (hr.trans r.R.map_zero.symm))

theorem inner_QH (v w : H) :
    inner ℝ (r.QH v) w = inner ℝ (r.J v) (r.J w) :=
  r.inner_RH (r.J v) w

theorem QH_symmetric (v w : H) : inner ℝ (r.QH v) w = inner ℝ v (r.QH w) := by
  rw [r.inner_QH, real_inner_comm (r.QH w), r.inner_QH, real_inner_comm]

theorem QH_nonneg (v : H) : 0 ≤ inner ℝ (r.QH v) v := by
  rw [r.inner_QH]
  exact real_inner_self_nonneg

variable (g : TimeGrid)

/-- The mass interface on the actual time-step weighted sequence pairing. -/
theorem pairing_J (v : g.Sequence H) (z : g.Sequence X) :
    g.pairing (g.map r.J v) z = g.pairing v (g.map r.RH z) := by
  simp only [TimeGrid.pairing, TimeGrid.map_apply, r.mass_adjoint, RH_apply]

theorem pairing_RH (z : g.Sequence X) (v : g.Sequence H) :
    g.pairing (g.map r.RH z) v = g.pairing z (g.map r.J v) := by
  rw [g.pairing_comm, ← r.pairing_J, g.pairing_comm]

/-- Periodic adjoint identity with reconstruction, reusing T001. -/
theorem pairing_RH_dPlus (z : g.Sequence X) (v : g.Sequence H) :
    g.pairing (g.map r.RH (g.dPlus z)) v =
      g.pairing z (g.map r.J (g.dMinus v)) := by
  rw [r.pairing_RH, g.pairing_dPlus, g.dMinus_map]

theorem pairing_RH_dMinus (z : g.Sequence X) (v : g.Sequence H) :
    g.pairing (g.map r.RH (g.dMinus z)) v =
      g.pairing z (g.map r.J (g.dPlus v)) := by
  rw [r.pairing_RH, g.pairing_dMinus, g.dPlus_map]

end Reconstruction
end Carleman
