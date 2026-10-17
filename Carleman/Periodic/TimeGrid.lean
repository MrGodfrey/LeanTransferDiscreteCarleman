module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# A positive periodic time grid

Section 2.4 of `paper/main.tex` uses the representatives `0, …, N - 1`,
with indices interpreted modulo `N` and `T = N * δt`. The shared interface
allows every `N > 0`; in particular it includes the paper's `N ≥ 2` grids.
-/

@[expose] public section

namespace Carleman

/-- A finite nonempty periodic grid with positive time step. -/
structure TimeGrid where
  steps : ℕ
  steps_pos : 0 < steps
  dt : ℝ
  dt_pos : 0 < dt

namespace TimeGrid

variable (g : TimeGrid)

instance : NeZero g.steps := ⟨Nat.ne_of_gt g.steps_pos⟩

/-- The representatives of one full period. -/
abbrev Index := Fin g.steps

/-- All states on the grid, without a frequency or spatial restriction. -/
abbrev Sequence (E : Type*) := g.Index → E

/-- The time period `T = N * δt`. -/
def period : ℝ := g.steps * g.dt

theorem period_pos : 0 < g.period :=
  mul_pos (Nat.cast_pos.mpr g.steps_pos) g.dt_pos

/-- The equivalent convention `δt = T / N` used in the manuscript. -/
theorem dt_eq_period_div_steps : g.dt = g.period / g.steps := by
  exact (mul_div_cancel_left₀ g.dt (Nat.cast_ne_zero.mpr (NeZero.ne g.steps))).symm

/-- Cyclic successor, including the step from `N - 1` to `0`. -/
def next : Equiv.Perm g.Index := finRotate g.steps

/-- Cyclic predecessor, including the step from `0` to `N - 1`. -/
def prev : Equiv.Perm g.Index := g.next.symm

theorem next_eq_add_one (i : g.Index) : g.next i = i + 1 :=
  finRotate_apply i

theorem prev_eq_sub_one (i : g.Index) : g.prev i = i - 1 :=
  finRotate_symm_apply i

@[simp] theorem prev_next (i : g.Index) : g.prev (g.next i) = i :=
  g.next.symm_apply_apply i

@[simp] theorem next_prev (i : g.Index) : g.next (g.prev i) = i :=
  g.next.apply_symm_apply i

end TimeGrid
end Carleman
