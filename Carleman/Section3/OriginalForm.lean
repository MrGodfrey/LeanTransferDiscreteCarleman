module

public import Carleman.Spatial.ConformingHilbert
public import Carleman.Continuous.FormAssociated

/-! The original closed dense conforming space in its Sobolev Hilbert norm.
The scalar form and full variational operator domain are identified explicitly;
no boundary or spectral restriction is introduced by the realization. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Set
namespace Carleman
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)}

/-- A1's closed dense V and bounded symmetric coercive bilinear form. The
continuous bilinear map is the usual bounded form in the H^m Hilbert norm. -/
structure OriginalForm (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S) where
  V : Submodule ℝ (Lp ℝ 2 ν)
  sobolev : V ≤ sobolevSubspace d m ν S
  closed : IsClosed {u : WeakSobolevJet d m ν S | WeakSobolevJet.value u ∈ V}
  dense : Dense (V : Set (Lp ℝ 2 ν))
  form : conformingHilbert (m := m) (S := S) V →L[ℝ]
    conformingHilbert (m := m) (S := S) V →L[ℝ] ℝ
  symmetric : ∀ u v, form u v = form v u
  coercive : ∃ c > (0 : ℝ), ∀ u, c*‖u‖*‖u‖ ≤ form u u

namespace OriginalForm
variable {hS : IsOpen S} {hν : ∀ᵐ x ∂ν, x ∈ S} (a : OriginalForm (m := m) hS hν)

abbrev Energy := conformingHilbert (m := m) (S := S) a.V
instance : CompleteSpace a.Energy := conformingHilbert_completeSpace a.V a.closed

def model : CoerciveForm (Lp ℝ 2 ν) a.Energy :=
  conformingCoerciveForm a.V hS hν a.sobolev a.dense a.form a.symmetric a.coercive

def valueEquiv : a.Energy ≃ₗ[ℝ] a.V :=
  LinearEquiv.ofBijective
    ((conformingEmbed (m := m) (S := S) a.V).toLinearMap.codRestrict a.V (fun u => u.property)) (by
      constructor
      · intro u v h
        exact conformingEmbed_injective a.V hS hν (congrArg Subtype.val h)
      · intro v
        obtain ⟨u,hu⟩ := (conformingEmbed_range a.V a.sobolev).ge v.property
        exact ⟨u, Subtype.ext hu⟩)

theorem valueEquiv_coe (u : a.Energy) : (a.valueEquiv u : Lp ℝ 2 ν) = a.model.embed u := rfl

def scalarForm (u v : a.V) : ℝ := a.form (a.valueEquiv.symm u) (a.valueEquiv.symm v)

theorem scalarForm_value (u v : a.Energy) :
    a.scalarForm (a.valueEquiv u) (a.valueEquiv v) = a.form u v := by
  simp only [scalarForm,LinearEquiv.symm_apply_apply]

theorem domain_le : a.model.domain ≤ a.V := by
  intro x hx
  have he := a.valueEquiv_coe (a.model.energy ⟨x,hx⟩)
  rw [a.model.embed_energy] at he
  have hv := (a.valueEquiv (a.model.energy ⟨x,hx⟩)).property
  rw [he] at hv
  exact hv

theorem operator_test (u : a.model.domain) (v : a.V) :
    a.scalarForm (a.model.domain.inclusion a.domain_le u) v =
      inner ℝ (a.model.operator u) (v : Lp ℝ 2 ν) := by
  have hu : a.model.domain.inclusion a.domain_le u = a.valueEquiv (a.model.energy u) := by
    apply Subtype.ext
    exact (a.model.embed_energy u).symm
  rw [hu,scalarForm,LinearEquiv.symm_apply_apply]
  have hv := a.valueEquiv_coe (a.valueEquiv.symm v)
  rw [LinearEquiv.apply_symm_apply] at hv
  rw [hv]
  exact (a.model.operator_test u (a.valueEquiv.symm v)).symm

/-- Exactly the full original variational domain/action, in both directions. -/
theorem associated_iff {D : Submodule ℝ (Lp ℝ 2 ν)} (A : D →ₗ[ℝ] Lp ℝ 2 ν) :
    a.model.IsAssociated A ↔ ∀ x f : Lp ℝ 2 ν,
      (∃ v : D, (v : Lp ℝ 2 ν) = x ∧ A v = f) ↔
        ∃ v : a.V, (v : Lp ℝ 2 ν) = x ∧ ∀ w : a.V,
          a.scalarForm v w = inner ℝ f (w : Lp ℝ 2 ν) := by
  have he (x f : Lp ℝ 2 ν) :
      (∃ v : a.Energy, a.model.embed v = x ∧ ∀ w,
        a.model.form v w = inner ℝ f (a.model.embed w)) ↔
      ∃ v : a.V, (v : Lp ℝ 2 ν) = x ∧ ∀ w : a.V,
        a.scalarForm v w = inner ℝ f (w : Lp ℝ 2 ν) := by
    constructor
    · rintro ⟨v,hv,ht⟩
      refine ⟨a.valueEquiv v,hv,?_⟩
      intro w
      obtain ⟨z,rfl⟩ := a.valueEquiv.surjective w
      rw [a.scalarForm_value,a.valueEquiv_coe]
      exact ht z
    · rintro ⟨v,hv,ht⟩
      obtain ⟨z,rfl⟩ := a.valueEquiv.surjective v
      refine ⟨z,hv,?_⟩
      intro w
      change a.form z w = inner ℝ f (a.model.embed w)
      simpa only [a.scalarForm_value,a.valueEquiv_coe] using ht (a.valueEquiv w)
  unfold CoerciveForm.IsAssociated
  simp only [he]
end OriginalForm
end Carleman
