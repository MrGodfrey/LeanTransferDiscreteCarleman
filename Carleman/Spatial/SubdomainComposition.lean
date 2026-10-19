module

public import Carleman.Spatial.SubdomainContinuity

/-! Nested restrictions preserve the same original L2 classes and weak jets. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S T U : Set (SpatialCoordinates d)}
  {E : Type*} [NormedAddCommGroup E]

theorem subdomainLp_trans (hST : S ⊆ T) (hTU : T ⊆ U)
    (u : Lp E 2 (volume.restrict U)) :
    subdomainLp hST (subdomainLp hTU u)=subdomainLp (hST.trans hTU) u := by
  apply Lp.ext
  exact ((subdomainLp_ae hST _).trans ((subdomainLp_ae hTU u).filter_mono
    (ae_mono (Measure.restrict_mono hST le_rfl)))).trans (subdomainLp_ae (hST.trans hTU) u).symm

theorem subdomainLp_self (u : Lp E 2 (volume.restrict S)) : subdomainLp (Subset.rfl : S ⊆ S) u=u :=
  Lp.ext (subdomainLp_ae Subset.rfl u)

theorem subdomainLp_restrictRegion (hST : S ⊆ T) (u : Lp E 2 (volume : Measure (SpatialCoordinates d))) :
    subdomainLp hST (Physical.restrictRegionLp T u)=Physical.restrictRegionLp S u := by
  apply Lp.ext
  exact ((subdomainLp_ae hST _).trans ((Physical.restrictRegionLp_ae T u).filter_mono
    (ae_mono (Measure.restrict_mono hST le_rfl)))).trans (Physical.restrictRegionLp_ae S u).symm

namespace WeakSobolevJet
variable {m : ℕ}

theorem restrictSubdomain_trans (hST : S ⊆ T) (hTU : T ⊆ U)
    (u : WeakSobolevJet d m (volume.restrict U) U) :
    restrictSubdomain hST (restrictSubdomain hTU u)=restrictSubdomain (hST.trans hTU) u := by
  apply Subtype.ext
  funext k
  exact subdomainLp_trans hST hTU (field k u)

theorem restrictSubdomain_self (u : WeakSobolevJet d m (volume.restrict S) S) :
    restrictSubdomain (Subset.rfl : S ⊆ S) u=u := by
  apply Subtype.ext
  funext k
  exact subdomainLp_self (field k u)

theorem restrictSubdomain_restrictDomain (hST : S ⊆ T) (u : WeakSobolevJet d m volume univ) :
    restrictSubdomain hST (restrictDomain T u)=restrictDomain S u := by
  apply Subtype.ext
  funext k
  exact subdomainLp_restrictRegion hST (field k u)

end WeakSobolevJet
end Carleman
