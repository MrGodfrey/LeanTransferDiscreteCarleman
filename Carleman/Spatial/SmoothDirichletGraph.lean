module

public import Carleman.Spatial.SmoothLaplacianL2Limit
public import Carleman.Spatial.SmoothBoundaryDirichlet
public import Carleman.Spatial.WeakPoissonRestriction

/-! Smooth zero-boundary functions belong to the actual form operator graph. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SpatialTest
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem laplacianOnLp_eq_subdomain (φ : SpatialTest (univ : Set (SpatialCoordinates d))) :
    φ.laplacianOnLp S=subdomainLp (subset_univ S) φ.laplacianLp := by
  apply Lp.ext
  exact (φ.laplacianOnLp_ae S).trans
    ((subdomainLp_ae (subset_univ S) φ.laplacianLp).trans
      (φ.laplacianLp_ae.filter_mono (ae_mono (Measure.restrict_mono (subset_univ S) le_rfl)))).symm

theorem exists_dirichlet_domain_of_boundary (hS : IsOpen S) (hd : 0 < d)
    (hb : Bornology.IsBounded S) (hconv : Convex ℝ S) (hne : S.Nonempty)
    (φ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hz : ∀ x ∈ frontier S, φ.value x=0) :
    ∃ z : (boundedDirichletOriginalForm hS hd hb).model.domain,
      (z : Lp ℝ 2 (volume.restrict S))=φ.toLp (volume.restrict S) ∧
      (boundedDirichletOriginalForm hS hd hb).model.operator z= -φ.laplacianOnLp S := by
  apply (dirichlet_operator_graph_iff hS hd hb _ _).mpr
  refine ⟨WeakSobolevJet.restrictSubdomain (subset_univ S) φ.sobolevJet,?_,
    smooth_boundary_test_mem_dirichletJetSpace hS hconv hb hne φ hz,?_⟩
  · apply Lp.ext
    exact (WeakSobolevJet.restrictSubdomain_test_value_ae (subset_univ S) φ).trans
      (φ.toLp_ae (volume.restrict S)).symm
  · obtain ⟨w,hw,hlap,_⟩ := φ.exists_H2_jet isOpen_univ
    have hp := negativeLaplacian_isWeak w
    rw [hw,hlap] at hp
    have hr := hp.restrictSubdomain isOpen_univ hS (subset_univ S)
    have he : subdomainLp (subset_univ S) (-φ.laplacianLp)= -φ.laplacianOnLp S := by
      rw [φ.laplacianOnLp_eq_subdomain]
      exact (subdomainLinearMap (subset_univ S)).map_neg _
    rwa [he] at hr

end Carleman.SpatialTest
