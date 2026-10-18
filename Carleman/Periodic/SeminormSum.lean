module

public import Carleman.Periodic.SeminormAlgebra
public import Carleman.Periodic.L2Algebra

/-! Finite Minkowski domination for actual dt-weighted seminorms, allowing
different Hilbert derivative-field spaces at the different orders. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman.TimeGrid
variable (g : TimeGrid) {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem weightedNorm_sum_le {ι : Type*} (p : g.Index → Seminorm ℝ E)
    (s : Finset ι) (u : ι → g.Sequence E) :
    g.weightedNorm p (∑ k ∈ s, u k) ≤ ∑ k ∈ s, g.weightedNorm p (u k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [weightedNorm,weightedSq]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (g.weightedNorm_add_le p _ _).trans (add_le_add le_rfl ih)

/-- Cauchy–Schwarz followed by Minkowski does not introduce a grid-size or
period factor when lifting nodewise approximation estimates. -/
theorem weightedNorm_le_field_sum {ι : Type*} [Fintype ι]
    {F : ι → Type*} [∀ k, NormedAddCommGroup (F k)] [∀ k, InnerProductSpace ℝ (F k)]
    (p : g.Index → Seminorm ℝ E) (u : g.Sequence E) (f : ∀ k, g.Sequence (F k))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ i, p i (u i) ≤ C*∑ k, ‖f k i‖) :
    g.weightedNorm p u ≤ C*∑ k, g.l2Norm (f k) := by
  let q : g.Index → Seminorm ℝ ℝ := fun _ => normSeminorm ℝ ℝ
  let v : ι → g.Sequence ℝ := fun k i => ‖f k i‖
  have hh := g.weightedNorm_le_of_bound p q u (∑ k, v k) hC (by
    intro i
    simpa only [q,v,Finset.sum_apply,coe_normSeminorm,Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun k _ => norm_nonneg (f k i))] using hb i)
  have hn (k : ι) : g.weightedNorm q (v k) = g.l2Norm (f k) := by
    simp only [l2Norm,weightedNorm,weightedSq,q,v,coe_normSeminorm,norm_norm]
  exact hh.trans ((mul_le_mul_of_nonneg_left (g.weightedNorm_sum_le q Finset.univ v) hC).trans_eq
    (by simp only [hn]))

end Carleman.TimeGrid
