module

public import Carleman.Spatial.HigherAnalyticData
public import Carleman.Section3.OriginalSquareRoot

/-! The full general coefficient spatial proposition, including the original
square-root form domain and energy identity. Original graph regularity is retained. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000
open MeasureTheory Set Filter
open scoped BigOperators ContDiff
namespace Carleman
variable {d m : ℕ} {S : Set (SpatialCoordinates d)}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem higherCoefficient_spatial_operators
    (hΩ : IsBoundedLipschitzDomain S F)
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedWeakCoefficient S (2*m))
    (hsym : ∀ α β, ((a α β).derivative []).value =ᵐ[volume.restrict S] ((a β α).derivative []).value)
    (hcoer : ∃ c > (0:ℝ), ∀ v : HigherDirichletEnergy S m,
      c*‖v‖*‖v‖ ≤ higherCoefficientForm S m (fun α β => (a α β).derivative []) v v)
    (hD : (higherCoefficientOriginalForm hΩ.isOpen (fun α β => (a α β).derivative []) hsym hcoer).model.domain ≤
      sobolevSubspace d (2*m) (volume.restrict S) S)
    {Creg : ℝ} (_hCreg : 0 < Creg)
    (hgraph : ∀ z : (higherCoefficientOriginalForm hΩ.isOpen (fun α β => (a α β).derivative []) hsym hcoer).model.domain,
      ‖SobolevHilbert.ofJet (domainSobolevJet hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hD z)‖ ≤
        Creg*‖(higherCoefficientOriginalForm hΩ.isOpen (fun α β => (a α β).derivative []) hsym hcoer).model.operator z‖)
    (r : SpatialCoordinates d → ℝ) (hr : SmoothOnClosure r S) :
    let f := higherCoefficientOriginalForm hΩ.isOpen (fun α β => (a α β).derivative []) hsym hcoer
    (∃ Ahalf : f.V →ₗ[ℝ] Lp ℝ 2 (volume.restrict S), f.SquareRootData Ahalf) ∧
    f.model.domain=higherDirichletSubspace S m ⊓ sobolevSubspace d (2*m) (volume.restrict S) S ∧
    Dense (f.model.domain : Set (Lp ℝ 2 (volume.restrict S))) ∧
    IsClosed (f.model.operatorGraph : Set (Lp ℝ 2 (volume.restrict S) × Lp ℝ 2 (volume.restrict S))) ∧
    (∀ z : f.model.domain, 0 ≤ inner ℝ (f.model.operator z) (z : Lp ℝ 2 (volume.restrict S))) ∧
    (∀ y g : Lp ℝ 2 (volume.restrict S),
      (∀ z : f.model.domain, inner ℝ (f.model.operator z) y=inner ℝ (z : Lp ℝ 2 (volume.restrict S)) g) ↔
        ∃ z : f.model.domain, (z : Lp ℝ 2 (volume.restrict S))=y ∧ f.model.operator z=g) ∧
    (∀ z : f.model.domain,
      ‖domainSobolevJet hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hD z‖ ≤ Creg*‖f.model.operator z‖) ∧
    ∃ ρ : SpatialProfile (volume.restrict S), ρ.value=r ∧
      ∃ c > (0:ℝ), ∃ C Ccomm : ℝ, 0 < C ∧ 0 < Ccomm ∧
        ∀ (w : TimeWeight) (τStar : ℝ),
        Section3.AllowedFamily hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet)
          (higherDirichletSubspace_sobolev S m) hD f.scalarForm f.model.operator
          ρ w c C Ccomm τStar := by
  dsimp only
  exact ⟨(higherCoefficientOriginalForm hΩ.isOpen (fun α β => (a α β).derivative []) hsym hcoer).exists_squareRootData,
    higherCoefficient_analytic_realization hΩ a hsym hcoer hD _hCreg hgraph r hr⟩

end Carleman
