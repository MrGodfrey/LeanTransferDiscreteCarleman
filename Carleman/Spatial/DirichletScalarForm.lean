module

public import Carleman.Spatial.WeakWeightedForm
public import Carleman.Spatial.ShiftedFormBounds

/-! Identification of the original scalar Dirichlet form with the actual
weak gradient pairing; no alternative energy or domain is introduced. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

set_option maxHeartbeats 800000 in
theorem dirichlet_scalarForm_eq (hS : IsOpen S) (hd : 0 < d) (hb : Bornology.IsBounded S)
    (u v : dirichletSubspace S) (U V : WeakSobolevJet d 1 (volume.restrict S) S)
    (hU : WeakSobolevJet.value U=(u : Lp ℝ 2 (volume.restrict S)))
    (hV : WeakSobolevJet.value V=(v : Lp ℝ 2 (volume.restrict S))) :
    (boundedDirichletOriginalForm hS hd hb).scalarForm u v=weakGradientPairing U V := by
  let a := boundedDirichletOriginalForm hS hd hb
  have hu : U ∈ dirichletJetSpace S := (mem_dirichletJetSpace_iff S hS U).mpr (hU ▸ u.property)
  have hv : V ∈ dirichletJetSpace S := (mem_dirichletJetSpace_iff S hS V).mpr (hV ▸ v.property)
  have heU : a.valueEquiv (dirichletJetEnergy U hu)=u := Subtype.ext hU
  have heV : a.valueEquiv (dirichletJetEnergy V hv)=v := Subtype.ext hV
  change a.scalarForm u v= _
  rw [← heU,← heV]
  exact a.scalarForm_value (dirichletJetEnergy U hu) (dirichletJetEnergy V hv)

theorem dirichlet_scalarForm_canonical (hS : IsOpen S) (hd : 0 < d) (hb : Bornology.IsBounded S)
    (u v : dirichletSubspace S) :
    (boundedDirichletOriginalForm hS hd hb).scalarForm u v=
      weakGradientPairing
        (domainSobolevJet hS (ae_restrict_mem hS.measurableSet) (dirichletSubspace_sobolev S) u)
        (domainSobolevJet hS (ae_restrict_mem hS.measurableSet) (dirichletSubspace_sobolev S) v) :=
  dirichlet_scalarForm_eq hS hd hb u v _ _ (domainSobolevJet_value _ _ _ _) (domainSobolevJet_value _ _ _ _)

end Carleman
