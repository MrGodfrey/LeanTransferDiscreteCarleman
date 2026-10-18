module

public import Carleman.Periodic.OperatorEnergy
public import Carleman.Periodic.CellAnchor
public import Mathlib.Analysis.Calculus.MeanValue

/-! Convert the actual time derivative of a test quadratic form to cyclic
nodal increments. Endpoint compatibility handles the last cell explicitly.
The scalar derivative bound is supplied by N4 and the cell weight comparison. -/
@[expose] public noncomputable section
open Set
open scoped BigOperators
namespace Carleman.TimeGrid
variable (g : TimeGrid) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem testOperator_cell_increment (T : ℝ → H →ₗ[ℝ] H)
    (hend : T 0 = T g.period) (T' : ℝ → H →ₗ[ℝ] H)
    (hder : ∀ z t, t ∈ Icc 0 g.period →
      HasDerivWithinAt (fun x => inner ℝ z (T x z)) (inner ℝ z (T' t z))
        (Icc 0 g.period) t)
    (i : g.Index) (z : H) (K : ℝ)
    (hbound : ∀ t ∈ Icc (g.cellTime i.val) (g.cellTime (i.val+1)),
      |inner ℝ z (T' t z)| ≤ K) :
    |inner ℝ z ((T (g.nodeTime (g.next i)) - T (g.nodeTime i)) z)| ≤ g.dt * K := by
  have hsub : Icc (g.cellTime i.val) (g.cellTime (i.val+1)) ⊆ Icc 0 g.period := by
    intro t ht
    exact ⟨(g.cellTime_mem i.val (Nat.le_of_lt i.isLt)).1.trans ht.1,
      ht.2.trans (g.cellTime_mem (i.val+1) (Nat.succ_le_of_lt i.isLt)).2⟩
  have hd : ∀ t ∈ Icc (g.cellTime i.val) (g.cellTime (i.val+1)),
      HasDerivWithinAt (fun x => inner ℝ z (T x z)) (inner ℝ z (T' t z))
        (Icc (g.cellTime i.val) (g.cellTime (i.val+1))) t :=
    fun t ht => (hder z t (hsub ht)).mono hsub
  have he := norm_image_sub_le_of_norm_deriv_le_segment' hd
    (fun t ht => by simpa only [Real.norm_eq_abs] using hbound t (Ico_subset_Icc_self ht))
    (g.cellTime (i.val+1)) (right_mem_Icc.mpr (g.cellTime_lt_succ i.val).le)
  rw [g.cellTime_succ_sub, g.next_node_value T hend i] at he
  simpa only [LinearMap.sub_apply, inner_sub_right, Real.norm_eq_abs, mul_comm, cellTime, nodeTime] using he

/-- N4's genuine derivative, bounded relative to the left cell node, gives
the complete lower bound for the positive time direction. -/
theorem pairing_testOperator_dPlus_lower (T : ℝ → H →ₗ[ℝ] H)
    (hend : T 0 = T g.period) (T' : ℝ → H →ₗ[ℝ] H)
    (hder : ∀ z t, t ∈ Icc 0 g.period →
      HasDerivWithinAt (fun x => inner ℝ z (T x z)) (inner ℝ z (T' t z))
        (Icc 0 g.period) t)
    (hsym : ∀ i v w, inner ℝ v (T (g.nodeTime i) w) = inner ℝ w (T (g.nodeTime i) v))
    (hpos : ∀ i v, 0 ≤ inner ℝ v (T (g.nodeTime i) v))
    (u : g.Sequence H) (b : g.Index → ℝ)
    (hbound : ∀ i t, t ∈ Icc (g.cellTime i.val) (g.cellTime (i.val+1)) →
      |inner ℝ (u i) (T' t (u i))| ≤ b i) :
    -(1 / 2) * g.dt * ∑ i, b i ≤
      g.pairing (g.dPlus u) (fun i => T (g.nodeTime i) (u i)) := by
  apply g.pairing_variable_operator_lower Orientation.plus
    (fun i => T (g.nodeTime i)) hsym hpos u b
  intro i
  exact (le_abs_self _).trans (g.testOperator_cell_increment T hend T' hder i (u i) (b i)
    (hbound i))

/-- The negative direction uses the cell before the node. Its derivative
bound is anchored at the right endpoint, including the periodic node zero. -/
theorem pairing_testOperator_dMinus_lower (T : ℝ → H →ₗ[ℝ] H)
    (hend : T 0 = T g.period) (T' : ℝ → H →ₗ[ℝ] H)
    (hder : ∀ z t, t ∈ Icc 0 g.period →
      HasDerivWithinAt (fun x => inner ℝ z (T x z)) (inner ℝ z (T' t z))
        (Icc 0 g.period) t)
    (hsym : ∀ i v w, inner ℝ v (T (g.nodeTime i) w) = inner ℝ w (T (g.nodeTime i) v))
    (hpos : ∀ i v, 0 ≤ inner ℝ v (T (g.nodeTime i) v))
    (u : g.Sequence H) (b : g.Index → ℝ)
    (hbound : ∀ i t, t ∈ Icc (g.cellTime (g.prev i).val) (g.cellTime ((g.prev i).val+1)) →
      |inner ℝ (u i) (T' t (u i))| ≤ b i) :
    -(1 / 2) * g.dt * ∑ i, b i ≤
      g.pairing (g.dMinus u) (fun i => T (g.nodeTime i) (u i)) := by
  apply g.pairing_variable_operator_lower Orientation.minus
    (fun i => T (g.nodeTime i)) hsym hpos u b
  intro i
  have he := g.testOperator_cell_increment T hend T' hder (g.prev i) (u i) (b i) (hbound i)
  rw [g.next_prev] at he
  have hn : inner ℝ (u i) ((T (g.nodeTime (g.prev i)) - T (g.nodeTime i)) (u i)) =
      -inner ℝ (u i) ((T (g.nodeTime i) - T (g.nodeTime (g.prev i))) (u i)) := by
    simp only [LinearMap.sub_apply, inner_sub_right]
    ring
  change inner ℝ (u i) ((T (g.nodeTime (g.prev i)) - T (g.nodeTime i)) (u i)) ≤ _
  rw [hn]
  exact (neg_le_abs _).trans he

end Carleman.TimeGrid
