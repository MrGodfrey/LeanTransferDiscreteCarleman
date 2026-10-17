module

public import Carleman.Continuous.CoerciveForm

/-! Actual solutions of bounded coercive variational equations, including
all positive shifts of the A1 associated operator. -/
@[expose] public noncomputable section
open InnerProductSpace Set
namespace Carleman
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

def variationalSolve (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) :
    (V →L[ℝ] ℝ) →L[ℝ] V :=
  hB.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (toDual ℝ V).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem variationalSolve_spec (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (f : V →L[ℝ] ℝ) (w : V) : B (variationalSolve B hB f) w = f w := by
  rw [← hB.continuousLinearEquivOfBilin_apply]
  change inner ℝ (hB.continuousLinearEquivOfBilin
    (hB.continuousLinearEquivOfBilin.symm ((toDual ℝ V).symm f))) w = f w
  rw [ContinuousLinearEquiv.apply_symm_apply, toDual_symm_apply]

theorem variationalSolve_unique (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (f : V →L[ℝ] ℝ) {u : V} (hu : ∀ w, B u w = f w) :
    u = variationalSolve B hB f := by
  apply hB.continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro w
  rw [hB.continuousLinearEquivOfBilin_apply, hB.continuousLinearEquivOfBilin_apply,
    variationalSolve_spec, hu]

namespace CoerciveForm
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (b : CoerciveForm H V)

def shiftedForm (r : ℝ) : V →L[ℝ] V →L[ℝ] ℝ :=
  b.form + r • ((innerSL ℝ).bilinearComp b.embed b.embed : V →L[ℝ] V →L[ℝ] ℝ)

omit [CompleteSpace V] in
theorem shiftedForm_apply (r : ℝ) (v w : V) :
    b.shiftedForm r v w = b.form v w + r * inner ℝ (b.embed v) (b.embed w) := rfl

omit [CompleteSpace V] in
theorem shiftedForm_coercive {r : ℝ} (hr : 0 ≤ r) : IsCoercive (b.shiftedForm r) := by
  obtain ⟨c, hc, h⟩ := b.coercive
  refine ⟨c, hc, fun v => (h v).trans ?_⟩
  change b.form v v ≤ b.form v v + r * inner ℝ (b.embed v) (b.embed v)
  exact le_add_of_nonneg_right (mul_nonneg hr real_inner_self_nonneg)

def loadFunctional : H →L[ℝ] V →L[ℝ] ℝ :=
  (ContinuousLinearMap.precompR V (innerSL ℝ)).flip b.embed

omit [CompleteSpace V] in
theorem loadFunctional_apply (f : H) (w : V) :
    b.loadFunctional f w = inner ℝ f (b.embed w) := rfl

def resolventEnergy (r : ℝ) (hr : 0 ≤ r) : H →L[ℝ] V :=
  (variationalSolve (b.shiftedForm r) (b.shiftedForm_coercive hr)).comp b.loadFunctional

theorem resolventEnergy_test (r : ℝ) (hr : 0 ≤ r) (f : H) (w : V) :
    b.form (b.resolventEnergy r hr f) w =
      inner ℝ (f - r • b.embed (b.resolventEnergy r hr f)) (b.embed w) := by
  have h := variationalSolve_spec (b.shiftedForm r) (b.shiftedForm_coercive hr)
    (b.loadFunctional f) w
  change b.form (b.resolventEnergy r hr f) w +
    r*inner ℝ (b.embed (b.resolventEnergy r hr f)) (b.embed w) = inner ℝ f (b.embed w) at h
  rw [inner_sub_left, real_inner_smul_left]
  linarith

/-- Constructed resolvent with values in the genuine associated domain. -/
def resolvent (r : ℝ) (hr : 0 ≤ r) (f : H) : b.domain :=
  b.domainElement (b.resolventEnergy r hr f)
    (f-r • b.embed (b.resolventEnergy r hr f)) (b.resolventEnergy_test r hr f)

theorem resolvent_equation (r : ℝ) (hr : 0 ≤ r) (f : H) :
    b.operator (b.resolvent r hr f) + r • (b.resolvent r hr f : H) = f := by
  rw [resolvent, b.operator_domainElement]
  exact sub_add_cancel _ _

theorem resolvent_unique (r : ℝ) (hr : 0 ≤ r) (f : H) {v : b.domain}
    (hv : b.operator v + r • (v : H) = f) : v = b.resolvent r hr f := by
  have he : b.energy v = b.resolventEnergy r hr f := by
    apply variationalSolve_unique (b.shiftedForm r) (b.shiftedForm_coercive hr) (b.loadFunctional f)
    intro w
    rw [b.shiftedForm_apply, ← b.operator_test, b.embed_energy, ← hv,
      b.loadFunctional_apply, inner_add_left, real_inner_smul_left]
  apply Subtype.ext
  rw [← b.embed_energy v, he]
  rfl

/-- Surjectivity and uniqueness are conclusions of A1, not assumptions. -/
theorem existsUnique_shifted (r : ℝ) (hr : 0 ≤ r) (f : H) :
    ∃! v : b.domain, b.operator v + r • (v : H) = f :=
  ⟨b.resolvent r hr f, b.resolvent_equation r hr f,
    fun _ hv => b.resolvent_unique r hr f hv⟩

end CoerciveForm
end Carleman
