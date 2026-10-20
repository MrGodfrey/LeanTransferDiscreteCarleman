module

public import Carleman.Continuous.FormOperator

/-! Full equality of the original associated operator graph and its adjoint graph. -/
@[expose] public noncomputable section
open Set
namespace Carleman.CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V)
/-- The adjoint graph equals the original graph: full unbounded self-adjointness. -/
theorem operator_adjoint_graph_iff (y f : H) :
    (∀ v : b.domain, inner ℝ (b.operator v) y=inner ℝ (v : H) f) ↔
      ∃ z : b.domain, (z : H)=y ∧ b.operator z=f := by
  constructor
  · intro h
    let z := b.resolvent 1 zero_le_one (f+y)
    have hz : b.operator z+(z : H)=f+y := by
      simpa only [one_smul] using b.resolvent_equation 1 zero_le_one (f+y)
    have ht (v : b.domain) : inner ℝ (b.operator v+(v : H)) (y-(z : H))=0 := by
      have hv := h v
      have hs := b.operator_symmetric v z
      have he := congrArg (fun x : H => inner ℝ (v : H) x) hz
      simp only [inner_add_right] at he
      rw [inner_add_left,inner_sub_right,inner_sub_right]
      linarith
    let v := b.resolvent 1 zero_le_one (y-(z : H))
    have he : b.operator v+(v : H)=y-(z : H) := by
      simpa only [one_smul] using b.resolvent_equation 1 zero_le_one (y-(z : H))
    have hn := ht v
    rw [he,real_inner_self_eq_norm_sq] at hn
    have hy : y=(z : H) := sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (y-(z : H))]))
    refine ⟨z,hy.symm,?_⟩
    rw [hy] at hz
    exact add_right_cancel hz
  · rintro ⟨z,rfl,rfl⟩
    exact fun v => b.operator_symmetric v z
end Carleman.CoerciveForm

