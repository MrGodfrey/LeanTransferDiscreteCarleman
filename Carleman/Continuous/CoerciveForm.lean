module

public import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-! The original A1 form data and its associated operator. The operator domain
is constructed from the variational identity; no resolvent or evolution
existence statement is an input. H and V need not be finite dimensional. -/
@[expose] public noncomputable section
open Set InnerProductSpace
namespace Carleman
variable (H V : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

structure CoerciveForm where
  embed : V →L[ℝ] H
  injective : Function.Injective embed
  dense : DenseRange embed
  form : V →L[ℝ] V →L[ℝ] ℝ
  symmetric : ∀ v w, form v w = form w v
  coercive : IsCoercive form

namespace CoerciveForm
variable {H V} (b : CoerciveForm H V)

theorem form_nonneg (v : V) : 0 ≤ b.form v v := by
  obtain ⟨c, hc, hb⟩ := b.coercive
  exact (by positivity : 0 ≤ c*‖v‖*‖v‖).trans (hb v)

/-- Density of the original energy embedding identifies H loads. -/
theorem eq_of_tests {f g : H} (h : ∀ w, inner ℝ f (b.embed w) = inner ℝ g (b.embed w)) : f = g := by
  have he : (fun y : H => inner ℝ f y) = (fun y => inner ℝ g y) :=
    b.dense.equalizer (continuous_const.inner continuous_id)
      (continuous_const.inner continuous_id) (funext h)
  exact ext_inner_right ℝ (congrFun he)

def domainV : Submodule ℝ V where
  carrier := {v | ∃ f : H, ∀ w, b.form v w = inner ℝ f (b.embed w)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro v z ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨f+g, by intro w; simp [hf, hg, inner_add_left]⟩
  smul_mem' := by
    rintro c v ⟨f, hf⟩
    exact ⟨c • f, by intro w; simp [hf, real_inner_smul_left]⟩

def domain : Submodule ℝ H := b.domainV.map b.embed.toLinearMap

def energyRaw (v : b.domain) : V := Classical.choose v.property

theorem energyRaw_mem (v : b.domain) : b.energyRaw v ∈ b.domainV :=
  (Classical.choose_spec v.property).1

theorem embed_energyRaw (v : b.domain) : b.embed (b.energyRaw v) = (v : H) :=
  (Classical.choose_spec v.property).2

def energy : b.domain →ₗ[ℝ] V where
  toFun := b.energyRaw
  map_add' v z := by
    apply b.injective
    simp only [map_add, b.embed_energyRaw, Submodule.coe_add]
  map_smul' c v := by
    apply b.injective
    simp only [map_smul, b.embed_energyRaw, Submodule.coe_smul, RingHom.id_apply]

theorem embed_energy (v : b.domain) : b.embed (b.energy v) = (v : H) := b.embed_energyRaw v

def operatorRaw (v : b.domain) : H := Classical.choose (b.energyRaw_mem v)

theorem operatorRaw_test (v : b.domain) (w : V) :
    inner ℝ (b.operatorRaw v) (b.embed w) = b.form (b.energy v) w :=
  (Classical.choose_spec (b.energyRaw_mem v) w).symm

/-- The actual associated unbounded operator on a submodule of H. -/
def operator : b.domain →ₗ[ℝ] H where
  toFun := b.operatorRaw
  map_add' v z := by
    apply b.eq_of_tests
    intro w
    simp only [inner_add_left, b.operatorRaw_test, map_add, add_apply]
  map_smul' c v := by
    apply b.eq_of_tests
    intro w
    simp only [real_inner_smul_left, b.operatorRaw_test, map_smul, smul_apply,
      smul_eq_mul, RingHom.id_apply]

theorem operator_test (v : b.domain) (w : V) :
    inner ℝ (b.operator v) (b.embed w) = b.form (b.energy v) w :=
  b.operatorRaw_test v w

/-- Membership is the original associated-operator variational definition. -/
def domainElement (v : V) (f : H) (hf : ∀ w, b.form v w = inner ℝ f (b.embed w)) : b.domain :=
  ⟨b.embed v, ⟨v, ⟨f, hf⟩, rfl⟩⟩

theorem energy_domainElement (v : V) (f : H)
    (hf : ∀ w, b.form v w = inner ℝ f (b.embed w)) :
    b.energy (b.domainElement v f hf) = v :=
  b.injective (b.embed_energy _)

theorem operator_domainElement (v : V) (f : H)
    (hf : ∀ w, b.form v w = inner ℝ f (b.embed w)) :
    b.operator (b.domainElement v f hf) = f := by
  apply b.eq_of_tests
  intro w
  rw [b.operator_test, b.energy_domainElement, hf]

theorem operator_symmetric (v z : b.domain) :
    inner ℝ (b.operator v) (z : H) = inner ℝ (v : H) (b.operator z) := by
  rw [← b.embed_energy z, b.operator_test, b.symmetric, ← b.operator_test,
    b.embed_energy, real_inner_comm]

theorem operator_nonneg (v : b.domain) : 0 ≤ inner ℝ (b.operator v) (v : H) := by
  rw [← b.embed_energy v, b.operator_test]
  exact b.form_nonneg _

end CoerciveForm
end Carleman
