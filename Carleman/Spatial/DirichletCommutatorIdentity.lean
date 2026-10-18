module

public import Carleman.Spatial.DirichletOperatorProduct
public import Carleman.Spatial.CommutatorPerturbation

/-! The exact commutator of the original form operator, on every domain
state and using its genuine first-order weak jet. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

noncomputable def dirichletDomainJet (hS : IsOpen S) (hd : 0 < d) (hb : Bornology.IsBounded S)
    (z : (boundedDirichletOriginalForm hS hd hb).model.domain) :
    WeakSobolevJet d 1 (volume.restrict S) S :=
  domainSobolevJet hS (ae_restrict_mem hS.measurableSet)
    ((boundedDirichletOriginalForm hS hd hb).domain_le.trans (dirichletSubspace_sobolev S)) z

theorem dirichletDomainJet_value (hS : IsOpen S) (hd : 0 < d) (hb : Bornology.IsBounded S)
    (z : (boundedDirichletOriginalForm hS hd hb).model.domain) :
    WeakSobolevJet.value (dirichletDomainJet hS hd hb z) = (z : Lp ℝ 2 (volume.restrict S)) :=
  domainSobolevJet_value _ _ _ _

theorem dirichletDomainJet_graph (hS : IsOpen S) (hd : 0 < d) (hb : Bornology.IsBounded S)
    (z : (boundedDirichletOriginalForm hS hd hb).model.domain) :
    dirichletDomainJet hS hd hb z ∈ dirichletJetSpace S ∧
    IsWeakNegativeLaplacian (dirichletDomainJet hS hd hb z)
      ((boundedDirichletOriginalForm hS hd hb).model.operator z) := by
  obtain ⟨u,hu,huD,huf⟩ := (dirichlet_operator_graph_iff hS hd hb _ _).mp ⟨z,rfl,rfl⟩
  have he : u=dirichletDomainJet hS hd hb z :=
    WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)
      (hu.trans (dirichletDomainJet_value hS hd hb z).symm)
  simpa only [he] using And.intro huD huf

theorem conformingWeight_operator_of_graph {ν : Measure (SpatialCoordinates d)}
    {D : Submodule ℝ (Lp ℝ 2 ν)} (A : D →ₗ[ℝ] Lp ℝ 2 ν) (σ : BoundedMultiplier ν)
    (hp : ∀ z : D, σ.map (z : Lp ℝ 2 ν) ∈ D) (z : D) (x f : Lp ℝ 2 ν)
    (hx : x=(z : Lp ℝ 2 ν))
    (hgraph : ∃ y : D, (y : Lp ℝ 2 ν)=σ.map x ∧ A y=f) :
    A (conformingWeight σ hp z)=f := by
  obtain ⟨y,hy,hyf⟩ := hgraph
  have he : y=conformingWeight σ hp z := Subtype.ext (hy.trans (congrArg σ.map hx))
  rwa [he] at hyf

set_option maxHeartbeats 800000 in
theorem dirichlet_operator_mul_eq (hS : IsOpen S) (hd : 0 < d) (hb : Bornology.IsBounded S)
    (σ : BoundedMultiplier (volume.restrict S)) (hσ : BoundedSmoothOn σ.value S)
    (hpres : ∀ z : (boundedDirichletOriginalForm hS hd hb).model.domain,
      σ.map (z : Lp ℝ 2 (volume.restrict S)) ∈ (boundedDirichletOriginalForm hS hd hb).model.domain)
    (z : (boundedDirichletOriginalForm hS hd hb).model.domain) :
    (boundedDirichletOriginalForm hS hd hb).model.operator (conformingWeight σ hpres z) =
      σ.map ((boundedDirichletOriginalForm hS hd hb).model.operator z)-
        smoothLaplacianCorrection hS σ hσ (dirichletDomainJet hS hd hb z) := by
  exact conformingWeight_operator_of_graph (boundedDirichletOriginalForm hS hd hb).model.operator
    σ hpres z _ _ (dirichletDomainJet_value hS hd hb z)
    (boundedSmooth_dirichlet_operator_product hS hd hb σ hσ
      (dirichletDomainJet hS hd hb z) (dirichletDomainJet_graph hS hd hb z).1
      ((boundedDirichletOriginalForm hS hd hb).model.operator z)
      (dirichletDomainJet_graph hS hd hb z).2)

set_option maxHeartbeats 800000 in
theorem dirichlet_conjugatedCommutator_eq (hS : IsOpen S) (hd : 0 < d)
    (hb : Bornology.IsBounded S) (σ ξ : BoundedMultiplier (volume.restrict S))
    (hσ : BoundedSmoothOn σ.value S)
    (hpres : ∀ z : (boundedDirichletOriginalForm hS hd hb).model.domain,
      σ.map (z : Lp ℝ 2 (volume.restrict S)) ∈ (boundedDirichletOriginalForm hS hd hb).model.domain)
    (hipres : ∀ z : (boundedDirichletOriginalForm hS hd hb).model.domain,
      ξ.map (z : Lp ℝ 2 (volume.restrict S)) ∈ (boundedDirichletOriginalForm hS hd hb).model.domain)
    (z : (boundedDirichletOriginalForm hS hd hb).model.domain) :
    conjugatedCommutator (boundedDirichletOriginalForm hS hd hb).model.operator σ ξ hpres hipres z =
      -smoothLaplacianCorrection hS σ hσ
        (dirichletDomainJet hS hd hb (conformingWeight ξ hipres z)) := by
  unfold conjugatedCommutator
  rw [dirichlet_operator_mul_eq hS hd hb σ hσ hpres]
  abel

end Carleman
