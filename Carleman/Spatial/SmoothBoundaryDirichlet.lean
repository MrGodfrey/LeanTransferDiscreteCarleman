module

public import Carleman.Spatial.ZeroBoundaryIndicator
public import Carleman.Spatial.SubdomainContinuity

/-! Every actual compact smooth function vanishing on the boundary of the
original bounded convex open domain belongs to the defining H1_0 closure. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem smooth_boundary_zero_mem_dirichletJetSpace (hS : IsOpen S) (hconv : Convex ℝ S)
    (hb : Bornology.IsBounded S) (hne : S.Nonempty) (φ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hzero : ∀ x ∈ frontier S, φ.value x=0)
    (u : WeakSobolevJet d 1 (volume.restrict S) S)
    (hu : WeakSobolevJet.value u =ᵐ[volume.restrict S] φ.value) :
    u ∈ dirichletJetSpace S := by
  obtain ⟨a,ha⟩ := hne
  obtain ⟨C,hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport φ.compact φ.smooth (by simp)
  have hI := zeroBoundary_indicator_lipschitz hC hzero
  have hcomp := indicator_hasCompactSupport (S := S) φ.compact
  let U := compactLipschitzSobolevJet hI hcomp
  have hmem := piecewiseSmooth_mem_dirichletJetSpace hS hconv hb ha hI hcomp
    (indicator_tsupport_subset_closure φ.value) (indicator_contDiffAt_ae hS hconv (φ.smooth.of_le (by simp)))
  have he : WeakSobolevJet.restrictDomain S U=u := by
    apply WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)
    rw [WeakSobolevJet.restrictDomain_value]
    apply Lp.ext
    have hU : WeakSobolevJet.value U =ᵐ[volume] S.indicator φ.value :=
      compactLipschitzSobolevJet_value_ae hI hcomp
    filter_upwards [Physical.restrictRegionLp_ae S (WeakSobolevJet.value U),
      hU.filter_mono ae_restrict_le,hu,ae_restrict_mem hS.measurableSet] with x h1 h2 h3 hx
    rw [h1,h2,h3,indicator_of_mem hx]
  rwa [he] at hmem

theorem smooth_boundary_test_mem_dirichletJetSpace (hS : IsOpen S) (hconv : Convex ℝ S)
    (hb : Bornology.IsBounded S) (hne : S.Nonempty) (φ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hzero : ∀ x ∈ frontier S, φ.value x=0) :
    WeakSobolevJet.restrictSubdomain (subset_univ S) φ.sobolevJet ∈ dirichletJetSpace S :=
  smooth_boundary_zero_mem_dirichletJetSpace hS hconv hb hne φ hzero _
    (WeakSobolevJet.restrictSubdomain_test_value_ae (subset_univ S) φ)

end Carleman
