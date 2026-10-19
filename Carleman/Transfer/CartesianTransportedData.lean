module

public import Carleman.Transfer.CartesianHeatGeometry

/-! The original numerical data on a fixed domain with its canonical transported load interface. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace Carleman
attribute [local instance] Classical.propDecidable

theorem cartesian_numericalData_on {d : ℕ} {S : Set (SpatialCoordinates (d+1))}
    (hS : IsOpen S) (hc : Convex ℝ S) (hcompact : IsCompact (closure S))
    (ρ : SpatialProfile (volume.restrict S)) (hρ : ContDiffOn ℝ 2 ρ.value (closure S))
    (κ β τStar : ℝ) (hκ : 1 ≤ κ) (hβ : 0 < β) (hτStar : 0 ≤ τStar)
    (ω₀ ω : Set (SpatialCoordinates (d+1))) (hω₀ : MeasurableSet ω₀)
    (hcompact₀ : IsCompact (closure ω₀)) (hω : IsOpen ω) (hinc : closure ω₀ ⊆ ω) :
    let a := boundedDirichletOriginalForm hS (Nat.succ_pos d)
      (hcompact.isBounded.subset subset_closure)
    ∃ ε > (0:ℝ), ε ≤ 1 ∧ ∃ Ctime > (0:ℝ), ∃ Csuper > (0:ℝ),
      ∃ (Capp : ℝ) (hCa : 0 < Capp), ∃ Cnum > (0:ℝ),
    ∀ (o δ : Fin (d+1) → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin (d+1) → ℕ)
      (hdom : openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)=S) (h : ℝ) (hh : 0 < h),
      (∀ j, h/κ ≤ δ j) → (∀ j, δ j ≤ h) →
    ∀ (hD : a.model.domain ≤ sobolevSubspace (d+1) (2*1) (volume.restrict S) S)
      (w : TimeWeight) (g : TimeGrid) (_H : TimeWeightRegularity w g β), h*w.max ≤ ε →
    Nonempty (Section5.NumericalData a hD
      (show Reconstruction (dirichletSubspace S) (CartesianPhysicalState δ hδ N) from
        hdom ▸ cartesianReconstruction o δ hδ N)
      (cartesianPhysicalLaplacian o δ hδ N).toLinearMap 0
      (cartesianLoadInterfaceOn o δ hδ N hdom)
      (cartesianPhysicalControlExtension o δ hδ N ω).adjoint.toLinearMap
      g w ρ ω₀ hω₀
      (fun t => cartesianStateSeminorm o δ hδ N (ρ.multiplier w 0 t).value)
      (fun t => cartesianStateSeminorm o δ hδ N (ρ.multiplier w 0 t).value)
      (fun t => cartesianControlSeminorm o δ hδ N ω (ρ.multiplier w 0 t).value)
      τStar Ctime Csuper Cnum h (cartesianErrorScales Capp h hCa.le hh.le)) := by
  dsimp only
  obtain ⟨ε,hε,he1,Ctime,hCt,Csuper,hCs,Capp,hCa,Cnum,hCn,hnum⟩ :=
    cartesian_numericalData hS hc hcompact ρ hρ κ β τStar hκ hβ hτStar
      ω₀ ω hω₀ hcompact₀ hω hinc
  refine ⟨ε,hε,he1,Ctime,hCt,Csuper,hCs,Capp,hCa,Cnum,hCn,?_⟩
  intro o δ hδ N hdom h hh hlower hupper hD w g H hsmall
  subst S
  exact hnum o δ hδ N rfl h hh hlower hupper hD w g H hsmall

end Carleman
