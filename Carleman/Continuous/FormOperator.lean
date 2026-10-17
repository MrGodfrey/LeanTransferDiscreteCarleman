module

public import Carleman.Continuous.FormSolve

/-! Closedness and dense definition of the actual A1 associated operator,
derived from its coercive form and constructed resolvent. -/
@[expose] public noncomputable section
open Set
namespace Carleman.CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V)

def resolventH : H →L[ℝ] H := b.embed.comp (b.resolventEnergy 1 zero_le_one)

theorem resolventH_eq (f : H) : b.resolventH f = (b.resolvent 1 zero_le_one f : H) := rfl

def operatorGraph : Submodule ℝ (H × H) :=
  (b.domain.subtype.prod b.operator).range

omit [CompleteSpace V] in
theorem operatorGraph_mem (x y : H) :
    (x,y) ∈ b.operatorGraph ↔ ∃ v : b.domain, (v : H) = x ∧ b.operator v = y := by
  change (∃ v : b.domain, ((v : H), b.operator v) = (x,y)) ↔ _
  simp only [Prod.mk.injEq]

/-- The graph is a closed equality of actual continuous resolvent maps. -/
theorem operatorGraph_eq : (b.operatorGraph : Set (H × H)) =
    {p | b.resolventH (p.2+p.1) = p.1} := by
  ext p
  change (p.1,p.2) ∈ b.operatorGraph ↔ b.resolventH (p.2+p.1) = p.1
  rw [b.operatorGraph_mem]
  constructor
  · rintro ⟨v, hv, ha⟩
    have he := b.resolvent_unique 1 zero_le_one (p.2+p.1)
      (v := v) (by simp only [one_smul, hv, ha])
    change b.resolventH (p.2+p.1) = p.1
    rw [b.resolventH_eq, ← he, hv]
  · intro hp
    let v := b.resolvent 1 zero_le_one (p.2+p.1)
    have hv : (v : H) = p.1 := hp
    refine ⟨v, hv, ?_⟩
    have he := b.resolvent_equation 1 zero_le_one (p.2+p.1)
    change b.operator v + 1 • (v : H) = _ at he
    rw [one_smul, hv] at he
    exact add_right_cancel he

theorem operatorGraph_isClosed : IsClosed (b.operatorGraph : Set (H × H)) := by
  rw [b.operatorGraph_eq]
  exact isClosed_eq (b.resolventH.continuous.comp (continuous_snd.add continuous_fst)) continuous_fst

variable [CompleteSpace H]

instance operatorGraph_completeSpace : CompleteSpace b.operatorGraph := by
  let : IsClosed (b.operatorGraph : Set (H × H)) := b.operatorGraph_isClosed
  exact IsClosed.completeSpace_coe

/-- The associated domain is dense in the original H, with no density input
for D(A) beyond the original dense V embedding. -/
theorem domain_dense : Dense (b.domain : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  apply le_antisymm ?_ bot_le
  intro y hy
  change y = 0
  let v := b.resolvent 1 zero_le_one y
  have hz : inner ℝ (v : H) y = 0 := (b.domain.mem_orthogonal y).mp hy _ v.property
  have he := b.resolvent_equation 1 zero_le_one y
  change b.operator v + 1 • (v : H) = y at he
  rw [one_smul] at he
  have hn : (v : H) = 0 := by
    rw [← he, inner_add_right, real_inner_comm (b.operator v) (v : H),
      real_inner_self_eq_norm_sq] at hz
    have hnon := b.operator_nonneg v
    exact norm_eq_zero.mp (by nlinarith [sq_nonneg ‖(v : H)‖])
  have hv : v = 0 := Subtype.ext hn
  rw [hv, map_zero, Submodule.coe_zero, add_zero] at he
  exact he.symm

end Carleman.CoerciveForm
