module

public import Carleman.Continuous.FormSquareRoot
public import Carleman.Section3.OriginalForm
/-! The complete square-root representation in the original conforming value space. -/
@[expose] public noncomputable section
set_option maxHeartbeats 2000000
open Set MeasureTheory
namespace Carleman.OriginalForm
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} {hS : IsOpen S} {hν : ∀ᵐ x ∂ν, x ∈ S}
  (a : OriginalForm (m := m) hS hν)

theorem formSqrtDomain_eq : a.model.formSqrtDomain=a.V :=
  conformingEmbed_range a.V a.sobolev

structure SquareRootData (Ahalf : a.V →ₗ[ℝ] Lp ℝ 2 ν) : Prop where
  nonnegative : ∀ v : a.V, 0 ≤ inner ℝ (Ahalf v) (v : Lp ℝ 2 ν)
  adjoint_graph : ∀ y g : Lp ℝ 2 ν,
    (∀ v : a.V, inner ℝ (Ahalf v) y=inner ℝ (v : Lp ℝ 2 ν) g) ↔
      ∃ v : a.V, (v : Lp ℝ 2 ν)=y ∧ Ahalf v=g
  square_graph : ∀ x f : Lp ℝ 2 ν,
    (∃ v : a.V, (v : Lp ℝ 2 ν)=x ∧ ∃ u : a.V, (u : Lp ℝ 2 ν)=Ahalf v ∧ Ahalf u=f) ↔
      ∃ z : a.model.domain, (z : Lp ℝ 2 ν)=x ∧ a.model.operator z=f
  energy : ∀ v : a.V, ‖Ahalf v‖^2=a.scalarForm v v

theorem exists_squareRootData : ∃ Ahalf : a.V →ₗ[ℝ] Lp ℝ 2 ν, a.SquareRootData Ahalf := by
  obtain ⟨S,hS,hAdj,hSq,hE⟩ := a.model.exists_positive_form_square_root
  let f := a.V.inclusion a.formSqrtDomain_eq.ge
  let g := a.model.formSqrtDomain.inclusion a.formSqrtDomain_eq.le
  let Ahalf := S.comp f
  refine ⟨Ahalf,⟨?_,?_,?_,?_⟩⟩
  · intro v
    exact hS (f v)
  · intro y t
    constructor
    · intro h
      have hh : ∀ v : a.model.formSqrtDomain, inner ℝ (S v) y=inner ℝ (v : Lp ℝ 2 ν) t := by
        intro v
        exact h (g v)
      obtain ⟨v,hv,hs⟩ := (hAdj y t).mp hh
      exact ⟨g v,hv,hs⟩
    · rintro ⟨v,hv,hs⟩
      have hh := (hAdj y t).mpr ⟨f v,hv,hs⟩
      exact fun u => hh (f u)
  · intro x t
    constructor
    · rintro ⟨v,hv,u,hu,hs⟩
      exact (hSq x t).mp ⟨f v,hv,f u,hu,hs⟩
    · intro h
      obtain ⟨v,hv,u,hu,hs⟩ := (hSq x t).mpr h
      exact ⟨g v,hv,g u,hu,hs⟩
  · intro v
    obtain ⟨u,rfl⟩ := a.valueEquiv.surjective v
    rw [a.scalarForm_value]
    exact hE u
end Carleman.OriginalForm
