module

public import Carleman.Spatial.HigherAllowedData
public import Carleman.Continuous.FormSelfAdjoint
public import Carleman.Section3.OriginalWeights

/-! General coefficient spatial analytic realization. Original elliptic graph regularity
remains an explicit manuscript hypothesis. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000
open MeasureTheory Set Filter
open scoped BigOperators ContDiff
namespace Carleman
variable {d m : ℕ} {S : Set (SpatialCoordinates d)}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem higherCoefficient_analytic_realization
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
  let : IsFiniteMeasure (volume.restrict S) := ⟨by simpa only [Measure.restrict_apply_univ] using (hΩ.isBounded.measure_lt_top (μ := volume))⟩
  dsimp only
  let f := higherCoefficientOriginalForm hΩ.isOpen (fun α β => (a α β).derivative []) hsym hcoer
  refine ⟨higherCoefficient_operator_domain_eq hΩ.isOpen a hsym hcoer hD,
    f.model.domain_dense,f.model.operatorGraph_isClosed,f.model.operator_nonneg,
    f.model.operator_adjoint_graph_iff,?_,?_⟩
  · intro z
    exact (SobolevHilbert.toJet_norm_le (SobolevHilbert.ofJet
      (domainSobolevJet hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hD z))).trans (hgraph z)
  · obtain ⟨ρ,hρ⟩ := exists_profile_of_smooth hΩ.isOpen hΩ.isBounded r hr
    obtain ⟨c,hc,C,Ccomm,hC,hCc,hfamily⟩ := higherCoefficient_allowed_family_uniform hΩ a hsym hcoer ρ (by rwa [hρ])
    exact ⟨ρ,hρ,c,hc,C,Ccomm,hC,hCc,hfamily hD⟩

end Carleman
