module
public import Carleman.Spatial.FiniteHalfspaceRegularity
public import Carleman.Spatial.BoxAnalyticData
public import Carleman.Section3.OriginalSquareRoot
public import Carleman.Continuous.FormSelfAdjoint
/-! Original Corollary A.2: the genuine Dirichlet Laplacian on bounded convex
polytopes and boxes supplies the complete spatial analytic package, without a
regularity premise. Constants precede all admissible time weights and parameters. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

def DirichletSpatialAnalyticData (hS : IsOpen S) (hd : 0<d) (hb : Bornology.IsBounded S)
    (hD : (boundedDirichletOriginalForm hS hd hb).model.domain≤sobolevSubspace d 2 (volume.restrict S) S)
    (r : SpatialCoordinates d → ℝ) : Prop :=
  let a := boundedDirichletOriginalForm hS hd hb
  (∃ Ahalf : a.V →ₗ[ℝ] Lp ℝ 2 (volume.restrict S), a.SquareRootData Ahalf) ∧
  a.model.domain=sobolevSubspace d 2 (volume.restrict S) S ⊓ dirichletSubspace S ∧
  Dense (a.model.domain : Set (Lp ℝ 2 (volume.restrict S))) ∧
  IsClosed (a.model.operatorGraph : Set (Lp ℝ 2 (volume.restrict S) × Lp ℝ 2 (volume.restrict S))) ∧
  (∀ z : a.model.domain, 0 ≤ inner ℝ (a.model.operator z) (z : Lp ℝ 2 (volume.restrict S))) ∧
  (∀ y g : Lp ℝ 2 (volume.restrict S),
    (∀ z : a.model.domain, inner ℝ (a.model.operator z) y=inner ℝ (z : Lp ℝ 2 (volume.restrict S)) g) ↔
      ∃ z : a.model.domain, (z : Lp ℝ 2 (volume.restrict S))=y ∧ a.model.operator z=g) ∧
  ∃ ρ : SpatialProfile (volume.restrict S), ρ.value=r ∧
    ∃ Creg > (0:ℝ), ∃ C Ccomm : ℝ, 1≤C ∧ 0<Ccomm ∧
      (∀ z : a.model.domain,
        ‖domainSobolevJet hS (ae_restrict_mem hS.measurableSet) hD z‖≤Creg*‖a.model.operator z‖) ∧
      ∀ (w : TimeWeight) (τStar : ℝ),
        Section3.AllowedFamily hS (ae_restrict_mem hS.measurableSet)
          (dirichletSubspace_sobolev S) hD a.scalarForm a.model.operator ρ w (1/2) C Ccomm τStar

theorem dirichlet_spatial_analytic_of_regularity (hS : IsOpen S) (hd : 0<d) (hb : Bornology.IsBounded S)
    (hD : (boundedDirichletOriginalForm hS hd hb).model.domain≤sobolevSubspace d 2 (volume.restrict S) S)
    (hgraph : ∃ Creg > (0:ℝ), ∀ z : (boundedDirichletOriginalForm hS hd hb).model.domain,
      ‖domainSobolevJet hS (ae_restrict_mem hS.measurableSet) hD z‖≤
        Creg*‖(boundedDirichletOriginalForm hS hd hb).model.operator z‖)
    (r : SpatialCoordinates d → ℝ) (hr : SmoothOnClosure r S) :
    DirichletSpatialAnalyticData hS hd hb hD r := by
  let a := boundedDirichletOriginalForm hS hd hb
  refine ⟨a.exists_squareRootData,?_,a.model.domain_dense,a.model.operatorGraph_isClosed,
    a.model.operator_nonneg,a.model.operator_adjoint_graph_iff,?_⟩
  · exact le_antisymm (le_inf hD a.domain_le) (h2_dirichlet_le_domain hS hd hb)
  · obtain ⟨ρ,hρ⟩ := exists_profile_of_smooth hS hb r hr
    obtain ⟨Creg,hCr,hreg⟩ := hgraph
    obtain ⟨C,Ccomm,hC,hCc,hfamily⟩ := dirichlet_allowed_family_uniform hS hd hb ρ (by rwa [hρ])
    exact ⟨ρ,hρ,Creg,hCr,C,Ccomm,hC,hCc,hreg,hfamily hD⟩

theorem finite_halfspace_analytic_realization {ι : Type*} [Fintype ι] (hd : 0<d)
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ)
    (hb : Bornology.IsBounded {x | ∀ i, b i<ℓ i x}) {c : SpatialCoordinates d} (hc : ∀ i, b i<ℓ i c)
    (r : SpatialCoordinates d → ℝ) (hr : SmoothOnClosure r {x | ∀ i, b i<ℓ i x}) :
    DirichletSpatialAnalyticData (finite_halfspace_isOpen ℓ b) hd hb
      (finite_halfspace_dirichlet_domain_le_h2 hd ℓ b hb hc) r :=
  dirichlet_spatial_analytic_of_regularity (finite_halfspace_isOpen ℓ b) hd hb
    (finite_halfspace_dirichlet_domain_le_h2 hd ℓ b hb hc)
    (finite_halfspace_dirichlet_graph_estimate hd ℓ b hb hc) r hr

theorem box_full_spatial_analytic_realization (hd : 0<d) (lo hi : Fin d → ℝ)
    (hpos : ∀ i, lo i<hi i) (r : SpatialCoordinates d → ℝ) (hr : SmoothOnClosure r (openCoordinateBox lo hi)) :
    DirichletSpatialAnalyticData (openCoordinateBox_isOpen lo hi) hd (openCoordinateBox_isBounded lo hi)
      (box_dirichlet_domain_le_h2 hd lo hi hpos) r :=
  dirichlet_spatial_analytic_of_regularity (openCoordinateBox_isOpen lo hi) hd (openCoordinateBox_isBounded lo hi)
    (box_dirichlet_domain_le_h2 hd lo hi hpos) (box_dirichlet_graph_estimate hd lo hi hpos) r hr

end Carleman
