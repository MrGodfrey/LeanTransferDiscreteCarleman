module

public import Carleman.Spatial.ExpressionTimeNorm
public import Carleman.Transfer.ErrorBridge

/-! A direct constructor for the order field of B4, using bounded spatial
coefficients and actual L² derivative fields. It applies to every trajectory;
no final transfer inequality or error estimate is assumed. -/
@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Carleman.TransferGeometry
variable {H X F Y Ω Z : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [AddCommGroup F] [Module ℝ F] [AddCommGroup Y] [Module ℝ Y]
  [MeasurableSpace Ω] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {ν : Measure Ω} {V : Submodule ℝ H} {a : CarlemanExponents}
  (p : TransferGeometry V X F Y a)
  {E : Fin (a.m+1) → Type*}
  [∀ k, NormedAddCommGroup (E k)] [∀ k, NormedSpace ℝ (E k)]

/-- B4-order from the actual finite expression and its true weighted fields.
Only graph-term integrability remains, exactly as in B4 finite_energy. -/
theorem order_of_L2_expression (ρ : SpatialProfile ν) (g : TimeGrid) (j : Fin a.m)
    (D : DifferentialExpression ν E Z (j.val+1))
    (J : ∀ k, V →ₗ[ℝ] Lp (E k) 2 ν)
    (hgrad : ∀ k, p.gradient k = fun t => (ρ.multiplier p.weight 0 t).seminorm.comp (J k))
    (hD : p.derivative j = fun t => (ρ.multiplier p.weight 0 t).seminorm.comp (D.onFields J))
    (u : ℝ → V)
    (hf : ∀ k, TimeSquareIntegrable g p.weight.q
      (2*(a.m-k.val : ℕ)+a.energyPower j) (p.gradient k) u) :
    timeSq g p.weight.q (a.c j) (p.derivative j) u ≤
      D.boundSq * p.graphSq g (a.energyPower j) u := by
  rw [hD, graphSq]
  simp_rw [hgrad] at hf ⊢
  exact D.timeSq_le_graph g p.weight.q p.weight.lower
    (fun t => ρ.multiplier p.weight 0 t) J u (a.c j) (a.energyPower j)
    (a.order_exponent_le j) hf

/-- One coefficient constant is fixed before the time grid, weight and state.
This supplies all j in ErrorBridge.order with the same K. -/
theorem order_of_L2_expressions_uniform
    (D : ∀ j : Fin a.m, DifferentialExpression ν E Z (j.val+1)) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (p : TransferGeometry V X F Y a) (ρ : SpatialProfile ν) (g : TimeGrid)
      (J : ∀ k, V →ₗ[ℝ] Lp (E k) 2 ν),
      (∀ k, p.gradient k = fun t => (ρ.multiplier p.weight 0 t).seminorm.comp (J k)) →
      (∀ j, p.derivative j = fun t => (ρ.multiplier p.weight 0 t).seminorm.comp ((D j).onFields J)) →
      ∀ u : ℝ → V,
      (∀ j k, TimeSquareIntegrable g p.weight.q
        (2*(a.m-k.val : ℕ)+a.energyPower j) (p.gradient k) u) →
      ∀ j, timeSq g p.weight.q (a.c j) (p.derivative j) u ≤
        K * p.graphSq g (a.energyPower j) u := by
  refine ⟨1 + ∑ j, (D j).boundSq, ?_, ?_⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => (D j).boundSq_nonneg)
  · intro p ρ g J hgrad hD u hf j
    apply (p.order_of_L2_expression ρ g j (D j) J hgrad (hD j) u (hf j)).trans
    apply mul_le_mul_of_nonneg_right
    · have hs := Finset.single_le_sum (s := Finset.univ)
        (fun j _ => (D j).boundSq_nonneg) (Finset.mem_univ j)
      linarith
    · exact Finset.sum_nonneg fun k _ =>
        timeSq_nonneg g p.weight.q p.weight.nonneg _ _ _
end Carleman.TransferGeometry
