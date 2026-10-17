module

public import Carleman.Continuous.FormOperator
public import Carleman.Periodic.EulerShift

/-! Identify the constructed operator with any original operator defined by
exactly the A1 variational domain. This transfers the analytic conclusions
to existing domain/operator interfaces without postulating their solutions. -/
@[expose] public noncomputable section
open Set
namespace Carleman.CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] (b : CoerciveForm H V)

/-- Full variational characterization of the associated domain and action. -/
def IsAssociated {D : Submodule ℝ H} (A : D →ₗ[ℝ] H) : Prop :=
  ∀ x f : H, (∃ v : D, (v : H) = x ∧ A v = f) ↔
    ∃ v : V, b.embed v = x ∧ ∀ w, b.form v w = inner ℝ f (b.embed w)

theorem operator_isAssociated : b.IsAssociated b.operator := by
  intro x f
  constructor
  · rintro ⟨v, hv, hf⟩
    refine ⟨b.energy v, (b.embed_energy v).trans hv, ?_⟩
    intro w
    rw [← b.operator_test, hf]
  · rintro ⟨v, hv, hf⟩
    exact ⟨b.domainElement v f hf, hv, b.operator_domainElement v f hf⟩

theorem IsAssociated.domain_eq {D : Submodule ℝ H} {A : D →ₗ[ℝ] H} (h : b.IsAssociated A) :
    D = b.domain := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, hv, _⟩ := (b.operator_isAssociated x (A ⟨x,hx⟩)).mpr
      ((h x (A ⟨x,hx⟩)).mp ⟨⟨x,hx⟩, rfl, rfl⟩)
    exact hv ▸ v.property
  · intro hx
    obtain ⟨v, hv, _⟩ := (h x (b.operator ⟨x,hx⟩)).mpr
      ((b.operator_isAssociated x (b.operator ⟨x,hx⟩)).mp ⟨⟨x,hx⟩, rfl, rfl⟩)
    exact hv ▸ v.property

theorem IsAssociated.operator_eq {A : b.domain →ₗ[ℝ] H} (h : b.IsAssociated A) : A = b.operator := by
  ext v
  obtain ⟨z, hz, ha⟩ := (b.operator_isAssociated (v : H) (A v)).mpr
    ((h (v : H) (A v)).mp ⟨v, rfl, rfl⟩)
  have hze : z = v := Subtype.ext hz
  simpa only [hze] using ha.symm

variable [CompleteSpace V]

/-- The existing A:D→H receives the constructed cyclic solution for every
load. The only identification premise is its original variational definition. -/
theorem IsAssociated.existsUnique_periodicEuler {D : Submodule ℝ H} {A : D →ₗ[ℝ] H}
    (h : b.IsAssociated A) (g : TimeGrid) (s : Orientation)
    (μ : g.Sequence ℝ) (hμ : ∀ i, 0 ≤ μ i) (f : g.Sequence H) :
    ∃! u : g.Sequence D, ∀ i,
      s.difference g (fun k => (u k : H)) i + A (u i) + μ i • (u i : H) = f i := by
  have hd := h.domain_eq b
  subst D
  have ha := h.operator_eq b
  subst A
  exact b.existsUnique_periodicEuler g s μ hμ f

omit [CompleteSpace V] in
theorem IsAssociated.euler_unweighted_graph {D : Submodule ℝ H} {A : D →ₗ[ℝ] H}
    (h : b.IsAssociated A) {m : ℕ} (hm : 0 < m) {β L : ℝ}
    (hL : eulerShiftThreshold m β ≤ L) (g : TimeGrid) (w : TimeWeight)
    (hw : TimeWeightRegularity w g β) (hmesh : g.dt*w.max^2 ≤ cellThreshold β 0 0)
    (s : Orientation) (u : g.Sequence D) :
    g.l2Norm (s.difference g (fun k => (u k : H))) + g.l2Norm (fun i => A (u i)) +
      g.l2Norm (fun i => (L*w.nodes g i)^(2*m) • (u i : H)) ≤
      3 * g.l2Norm (fun i => s.difference g (fun k => (u k : H)) i +
        A (u i) + (L*w.nodes g i)^(2*m) • (u i : H)) := by
  have hd := h.domain_eq b
  subst D
  have ha := h.operator_eq b
  subst A
  exact b.euler_unweighted_graph hm hL g w hw hmesh s u

end Carleman.CoerciveForm
