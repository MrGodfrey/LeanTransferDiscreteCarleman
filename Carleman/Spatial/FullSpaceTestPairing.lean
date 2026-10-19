module

public import Carleman.Spatial.ReflectionTest
public import Carleman.Spatial.SmoothBoundaryDirichlet

/-! Exact full-space and restricted pairings of the same weak jets and tests. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem zeroExtendLp_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (hS : MeasurableSet S)
    (u : Lp E 2 (volume.restrict S)) (v : Lp E 2 (volume : Measure (SpatialCoordinates d))) :
    inner ℝ (zeroExtendLp hS u) v=inner ℝ u (Physical.restrictRegionLp S v) := by
  rw [← Physical.restrictRegion_adjoint S hS,ContinuousLinearMap.adjoint_inner_left]
  rfl

theorem WeakSobolevJet.zeroExtendDirichlet_pairing (hS : IsOpen S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (v : WeakSobolevJet d 1 volume univ) :
    weakGradientPairing (zeroExtendDirichlet hS u hu) v=
      weakGradientPairing u (restrictDomain S v) :=
  zeroExtendLp_inner hS.measurableSet _ _

theorem SpatialTest.fullJet_eq_zeroExtend (hS : IsOpen S) (φ : SpatialTest S) :
    φ.fullJet=WeakSobolevJet.zeroExtendDirichlet hS φ.sobolevJet (test_mem_dirichletJetSpace S φ) := by
  apply WeakSobolevJet.value_injective isOpen_univ (Filter.Eventually.of_forall fun _ => mem_univ _)
  exact Lp.ext (φ.fullJet_value_ae.trans (φ.zeroExtendDirichlet_value_ae hS).symm)

theorem SpatialTest.fullJet_pairing (hS : IsOpen S) (φ : SpatialTest S)
    (u : WeakSobolevJet d 1 volume univ) :
    weakGradientPairing u φ.fullJet=weakGradientPairing (WeakSobolevJet.restrictDomain S u) φ.sobolevJet := by
  rw [φ.fullJet_eq_zeroExtend hS,weakGradientPairing_apply,real_inner_comm]
  change weakGradientPairing (WeakSobolevJet.zeroExtendDirichlet hS φ.sobolevJet
    (test_mem_dirichletJetSpace S φ)) u=_
  rw [WeakSobolevJet.zeroExtendDirichlet_pairing,weakGradientPairing_apply,weakGradientPairing_apply,
    real_inner_comm]

theorem SpatialTest.fullJet_inner (hS : IsOpen S) (φ : SpatialTest S)
    (f : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    inner ℝ f (WeakSobolevJet.value φ.fullJet)=
      inner ℝ (Physical.restrictRegionLp S f) (φ.toLp (volume.restrict S)) := by
  rw [φ.fullJet_eq_zeroExtend hS,WeakSobolevJet.zeroExtendDirichlet_value,φ.sobolevJet_value,
    real_inner_comm,zeroExtendLp_inner,real_inner_comm]

theorem SpatialTest.fullJet_boundary_mem (hS : IsOpen S) (hconv : Convex ℝ S)
    (hb : Bornology.IsBounded S) (hne : S.Nonempty)
    (φ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hzero : ∀ x ∈ frontier S, φ.value x=0) :
    WeakSobolevJet.restrictDomain S φ.fullJet ∈ dirichletJetSpace S := by
  apply smooth_boundary_zero_mem_dirichletJetSpace hS hconv hb hne φ hzero
  rw [WeakSobolevJet.restrictDomain_value]
  exact (Physical.restrictRegionLp_ae S _).trans (φ.fullJet_value_ae.filter_mono ae_restrict_le)

end Carleman
