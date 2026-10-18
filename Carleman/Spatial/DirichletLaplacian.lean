module

public import Carleman.Spatial.WeakLaplacian

/-! The genuine Dirichlet form operator acts as the actual negative
Laplacian on H² ∩ H¹₀. The converse H² regularity is not assumed or claimed. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

def dirichletH2Energy (u : WeakSobolevJet d 2 (volume.restrict S) S)
    (hu : WeakSobolevJet.value u ∈ dirichletSubspace S) : DirichletEnergy S :=
  ⟨SobolevHilbert.ofJet (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u),hu⟩

theorem dirichletH2Energy_value (u : WeakSobolevJet d 2 (volume.restrict S) S)
    (hu : WeakSobolevJet.value u ∈ dirichletSubspace S) :
    conformingEmbed (m := 1) (S := S) (dirichletSubspace S) (dirichletH2Energy u hu) =
      WeakSobolevJet.value u := rfl

theorem dirichletH2Energy_green (hS : IsOpen S)
    (u : WeakSobolevJet d 2 (volume.restrict S) S)
    (hu : WeakSobolevJet.value u ∈ dirichletSubspace S) (v : DirichletEnergy S) :
    dirichletForm S (dirichletH2Energy u hu) v =
      inner ℝ (negativeLaplacian u) (conformingEmbed (m := 1) (S := S) (dirichletSubspace S) v) := by
  exact negativeLaplacian_dirichlet hS u (SobolevHilbert.toJet v.val)
    ((mem_dirichletJetSpace_iff S hS _).mpr v.property)

def dirichletH2DomainElement (hS : IsOpen S) (hd : 0 < d) (hb : Bornology.IsBounded S)
    (u : WeakSobolevJet d 2 (volume.restrict S) S)
    (hu : WeakSobolevJet.value u ∈ dirichletSubspace S) :
    (boundedDirichletOriginalForm hS hd hb).model.domain :=
  (boundedDirichletOriginalForm hS hd hb).model.domainElement
    (dirichletH2Energy u hu) (negativeLaplacian u) (dirichletH2Energy_green hS u hu)

theorem dirichletH2DomainElement_value (hS : IsOpen S) (hd : 0 < d) (hb : Bornology.IsBounded S)
    (u : WeakSobolevJet d 2 (volume.restrict S) S)
    (hu : WeakSobolevJet.value u ∈ dirichletSubspace S) :
    (dirichletH2DomainElement hS hd hb u hu : Lp ℝ 2 (volume.restrict S)) =
      WeakSobolevJet.value u := rfl

theorem dirichletH2DomainElement_operator (hS : IsOpen S) (hd : 0 < d) (hb : Bornology.IsBounded S)
    (u : WeakSobolevJet d 2 (volume.restrict S) S)
    (hu : WeakSobolevJet.value u ∈ dirichletSubspace S) :
    (boundedDirichletOriginalForm hS hd hb).model.operator (dirichletH2DomainElement hS hd hb u hu) =
      negativeLaplacian u :=
  (boundedDirichletOriginalForm hS hd hb).model.operator_domainElement _ _ _

theorem h2_dirichlet_le_domain (hS : IsOpen S) (hd : 0 < d) (hb : Bornology.IsBounded S) :
    sobolevSubspace d 2 (volume.restrict S) S ⊓ dirichletSubspace S ≤
      (boundedDirichletOriginalForm hS hd hb).model.domain := by
  rintro _ ⟨⟨u,rfl⟩,hu⟩
  exact (dirichletH2DomainElement hS hd hb u hu).property

end Carleman
