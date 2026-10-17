module

public import Carleman.Periodic.LinearMap

/-!
# The two cellwise extensions

These are the actual half-open cells of `eq:cellwise-extension`
(`paper/main.tex:774–784`). `Fin.intCast` reduces integer node numbers to the
existing `TimeGrid.Index`; no second sequence or difference interface is used.
`D₊` uses the right endpoint (ceiling); `D₋` uses the left endpoint (floor).
-/

@[expose] public section

namespace Carleman.TimeGrid

variable (g : Carleman.TimeGrid) {E : Type*}

noncomputable def extensionPlus (u : g.Sequence E) (t : ℝ) : E :=
  u (Fin.intCast ⌈t / g.dt⌉)

noncomputable def extensionMinus (u : g.Sequence E) (t : ℝ) : E :=
  u (Fin.intCast ⌊t / g.dt⌋)

theorem extensionPlus_on_cell (u : g.Sequence E) (n : ℤ) (t : ℝ)
    (ht : ((n : ℝ) - 1) * g.dt < t ∧ t ≤ (n : ℝ) * g.dt) :
    g.extensionPlus u t = u (Fin.intCast n) := by
  unfold extensionPlus
  rw [Int.ceil_eq_iff.mpr ⟨(lt_div_iff₀ g.dt_pos).mpr ht.1,
    (div_le_iff₀ g.dt_pos).mpr ht.2⟩]

theorem extensionMinus_on_cell (u : g.Sequence E) (n : ℤ) (t : ℝ)
    (ht : (n : ℝ) * g.dt ≤ t ∧ t < ((n : ℝ) + 1) * g.dt) :
    g.extensionMinus u t = u (Fin.intCast n) := by
  unfold extensionMinus
  rw [Int.floor_eq_iff.mpr ⟨(le_div_iff₀ g.dt_pos).mpr ht.1,
    (div_lt_iff₀ g.dt_pos).mpr ht.2⟩]

/-- The initial endpoint uses the existing zero node for both orientations. -/
theorem extensionPlus_zero (u : g.Sequence E) : g.extensionPlus u 0 = u 0 := by
  simp [extensionPlus, Fin.intCast]

theorem extensionMinus_zero (u : g.Sequence E) : g.extensionMinus u 0 = u 0 := by
  simp [extensionMinus, Fin.intCast]

/-- The period endpoint wraps to the same node, without a new endpoint state. -/
theorem extensionPlus_period (u : g.Sequence E) : g.extensionPlus u g.period = u 0 := by
  simp [extensionPlus, period, ne_of_gt g.dt_pos, Fin.intCast]

theorem extensionMinus_period (u : g.Sequence E) : g.extensionMinus u g.period = u 0 := by
  simp [extensionMinus, period, ne_of_gt g.dt_pos, Fin.intCast]

variable [AddCommGroup E] [Module ℝ E]
variable {F : Type*} [AddCommGroup F] [Module ℝ F]

theorem extensionPlus_map (L : E →ₗ[ℝ] F) (u : g.Sequence E) (t : ℝ) :
    g.extensionPlus (g.map L u) t = L (g.extensionPlus u t) := rfl

theorem extensionMinus_map (L : E →ₗ[ℝ] F) (u : g.Sequence E) (t : ℝ) :
    g.extensionMinus (g.map L u) t = L (g.extensionMinus u t) := rfl

omit [Module ℝ E] in
theorem extensionPlus_add (u v : g.Sequence E) (t : ℝ) :
    g.extensionPlus (u + v) t = g.extensionPlus u t + g.extensionPlus v t := rfl

omit [Module ℝ E] in
theorem extensionMinus_add (u v : g.Sequence E) (t : ℝ) :
    g.extensionMinus (u + v) t = g.extensionMinus u t + g.extensionMinus v t := rfl

theorem extensionPlus_node_smul (a : g.Sequence ℝ) (u : g.Sequence E) (t : ℝ) :
    g.extensionPlus (fun i => a i • u i) t =
      g.extensionPlus a t • g.extensionPlus u t := rfl

theorem extensionMinus_node_smul (a : g.Sequence ℝ) (u : g.Sequence E) (t : ℝ) :
    g.extensionMinus (fun i => a i • u i) t =
      g.extensionMinus a t • g.extensionMinus u t := rfl

end Carleman.TimeGrid
