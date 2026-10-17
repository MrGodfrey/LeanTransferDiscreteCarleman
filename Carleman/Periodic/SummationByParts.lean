module

public import Carleman.Periodic.TimeGrid
public import Carleman.Periodic.Telescoping
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Periodic differences and summation by parts

The signs and pairing are those of Section 2.4, `paper/main.tex:477–500`:
`D₊ u i = (u i - u (i - 1)) / δt`, `D₋ u i = (u i - u (i + 1)) / δt`,
and `(u,v) = δt * ∑ i, ⟪u i, v i⟫_ℝ`. Thus `D₊* = D₋` with no minus sign.

The identities hold for every real inner product space, so they apply both to
the paper's finite-dimensional real `X_h` and to its real Hilbert spaces.
Completeness and finite dimensionality are unnecessary for these finite sums.
This is an auxiliary interface, not a Section 5 estimate.
-/

@[expose] public section

namespace Carleman.TimeGrid

open scoped BigOperators

variable (g : Carleman.TimeGrid)

section Differences

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The paper's `D₊`, using the cyclic predecessor. -/
noncomputable def dPlus (u : g.Sequence E) : g.Sequence E :=
  fun i => g.dt⁻¹ • (u i - u (g.prev i))

/-- The paper's `D₋`, with the sign of the negative continuous derivative. -/
noncomputable def dMinus (u : g.Sequence E) : g.Sequence E :=
  fun i => g.dt⁻¹ • (u i - u (g.next i))

theorem dPlus_apply (u : g.Sequence E) (i : g.Index) :
    g.dPlus u i = g.dt⁻¹ • (u i - u (i - 1)) := by
  rw [dPlus, g.prev_eq_sub_one]

theorem dMinus_apply (u : g.Sequence E) (i : g.Index) :
    g.dMinus u i = g.dt⁻¹ • (u i - u (i + 1)) := by
  rw [dMinus, g.next_eq_add_one]

/-- Reuse the already merged telescoping lemma for the positive difference. -/
theorem sum_dPlus_eq_zero (u : g.Sequence E) : ∑ i, g.dPlus u i = 0 := by
  simp only [dPlus, ← Finset.smul_sum, Carleman.sum_sub_perm, smul_zero]

/-- Reuse the same lemma for the other time direction. -/
theorem sum_dMinus_eq_zero (u : g.Sequence E) : ∑ i, g.dMinus u i = 0 := by
  simp only [dMinus, ← Finset.smul_sum, Carleman.sum_sub_perm, smul_zero]

end Differences

section InnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The actual `ℓ²_{δt}(H)` pairing, including the time-step factor. -/
noncomputable def pairing (u v : g.Sequence H) : ℝ :=
  g.dt * ∑ i, inner ℝ (u i) (v i)

theorem pairing_comm (u v : g.Sequence H) : g.pairing u v = g.pairing v u := by
  simp only [pairing, real_inner_comm]

theorem pairing_self_nonneg (u : g.Sequence H) : 0 ≤ g.pairing u u :=
  mul_nonneg g.dt_pos.le (Finset.sum_nonneg fun _ _ => real_inner_self_nonneg)

/-- Positivity of `δt` makes this pairing nondegenerate on all grid states. -/
theorem pairing_self_eq_zero (u : g.Sequence H) :
    g.pairing u u = 0 ↔ u = 0 := by
  simp only [pairing, mul_eq_zero, ne_of_gt g.dt_pos, false_or,
    Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => real_inner_self_nonneg),
    Finset.mem_univ, forall_const, inner_self_eq_zero]
  exact ⟨fun h => funext h, fun h i => congrFun h i⟩

/-- Move a cyclic predecessor from one slot to a successor in the other. -/
theorem sum_inner_prev (u v : g.Sequence H) :
    ∑ i, inner ℝ (u (g.prev i)) (v i) =
      ∑ i, inner ℝ (u i) (v (g.next i)) := by
  have h := Carleman.sum_sub_perm g.next (fun i => inner ℝ (u (g.prev i)) (v i))
  simpa only [Finset.sum_sub_distrib, prev_next, sub_eq_zero] using h

/-- Periodic summation by parts: the adjoint of `D₊` is `D₋`. -/
theorem pairing_dPlus (u v : g.Sequence H) :
    g.pairing (g.dPlus u) v = g.pairing u (g.dMinus v) := by
  simp only [pairing, dPlus, dMinus, real_inner_smul_left, real_inner_smul_right,
    inner_sub_left, inner_sub_right, ← Finset.mul_sum, Finset.sum_sub_distrib,
    g.sum_inner_prev]

/-- The reverse direction: the adjoint of `D₋` is `D₊`. -/
theorem pairing_dMinus (u v : g.Sequence H) :
    g.pairing (g.dMinus u) v = g.pairing u (g.dPlus v) := by
  rw [g.pairing_comm, ← g.pairing_dPlus, g.pairing_comm u]

end InnerProduct
end Carleman.TimeGrid
