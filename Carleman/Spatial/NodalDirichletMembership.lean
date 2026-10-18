module

public import Carleman.Spatial.CompactMollificationLimit
public import Carleman.Spatial.SobolevRestriction
public import Carleman.Spatial.NodalContractionLimit

/-! Genuine zero-boundary nodal functions belong to H¹₀ defined as the
H¹ closure of all compactly supported smooth spatial tests. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem compactLipschitzSobolevJet_value_ae {f : SpatialCoordinates d → ℝ} {C : ℝ≥0}
    (hC : LipschitzWith C f) (hf : HasCompactSupport f) :
    WeakSobolevJet.value (compactLipschitzSobolevJet hC hf) =ᵐ[volume] f := by
  rw [compactLipschitzSobolevJet_value]
  exact compactLipschitzLp_ae hC hf

theorem compactLipschitz_mem_dirichletJetSpace (hS : IsOpen S)
    {f : SpatialCoordinates d → ℝ} {C : ℝ≥0} (hC : LipschitzWith C f)
    (hf : HasCompactSupport f) (hsupp : tsupport f ⊆ S) :
    WeakSobolevJet.restrictDomain S (compactLipschitzSobolevJet hC hf) ∈ dirichletJetSpace S := by
  obtain ⟨δ,hδ,hbuffer⟩ := hf.exists_cthickening_subset_open hS hsupp
  have hlim := WeakSobolevJet.restrictDomain_tendsto (S := S) (compactMollification_tendsto_H1 hC hf)
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hlim
  have hsmall : ∀ᶠ n in atTop, (shrinkingBump d n).rOut < δ :=
    shrinkingBump_radius_tendsto.eventually (gt_mem_nhds hδ)
  filter_upwards [hsmall] with n hn
  let φ : SpatialTest S := {
    value := compactMollification f n
    smooth := compactMollification_smooth hC.continuous n
    compact := compactMollification_compact hf n
    support := (compactMollification_support f n).trans
      ((Metric.cthickening_mono hn.le _).trans hbuffer) }
  rw [restrictedJet_eq_test hS φ _
    (compactLipschitzSobolevJet_value_ae (compactMollification_lipschitz hC n)
      (compactMollification_compact hf n))]
  exact test_mem_dirichletJetSpace S φ

namespace SimplicialPartition
variable {ι : Type*} [Fintype ι] (M : SimplicialPartition S ι)

theorem nodal_inward_mem_dirichletJetSpace (hS : IsOpen S) (hconv : Convex ℝ S)
    (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k) = 0)
    {a : SpatialCoordinates d} (ha : a ∈ S) (n : ℕ) :
    WeakSobolevJet.restrictDomain S (M.nodalContractedSobolevJet hS hM hB f hf a
      (inwardRatio n) (inwardRatio_pos n).ne') ∈ dirichletJetSpace S :=
  compactLipschitz_mem_dirichletJetSpace hS
    (contractedFunction_lipschitz a _ _ (M.nodalFunction_lipschitzWith hS hM hB f hf))
    (contractedFunction_compact a _ _ (M.nodalFunction_hasCompactSupport f))
    (contractedFunction_support_inside hS hconv ha (inwardRatio_pos n) (inwardRatio_lt_one n)
      (M.nodalFunction_tsupport_subset f))

theorem nodal_global_restrict_mem_dirichletJetSpace (hS : IsOpen S) (hconv : Convex ℝ S)
    (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k) = 0)
    {a : SpatialCoordinates d} (ha : a ∈ S) :
    WeakSobolevJet.restrictDomain S (M.nodalGlobalSobolevJet hS hM hB f hf) ∈ dirichletJetSpace S := by
  have hlim := WeakSobolevJet.restrictDomain_tendsto (S := S)
    (M.nodal_inward_tendsto_H1 hS hconv hM hB f hf ha)
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hlim
  exact Filter.Eventually.of_forall (M.nodal_inward_mem_dirichletJetSpace hS hconv hM hB f hf ha)

variable [IsFiniteMeasure (volume.restrict S)]

theorem nodalLp_mem_dirichletSubspace (hS : IsOpen S) (hconv : Convex ℝ S)
    (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k) = 0) :
    M.nodalLp hS.measurableSet hM f ∈ dirichletSubspace S := by
  by_cases hs0 : S = ∅
  · subst S
    have hz : M.nodalLp hS.measurableSet hM f = 0 := by
      apply Lp.ext
      simp only [Measure.restrict_empty,ae_zero]
      exact Filter.eventually_bot
    rw [hz]
    exact (dirichletSubspace ∅).zero_mem
  · obtain ⟨a,ha⟩ := Set.nonempty_iff_ne_empty.mpr hs0
    refine ⟨WeakSobolevJet.restrictDomain S (M.nodalGlobalSobolevJet hS hM hB f hf),
      M.nodal_global_restrict_mem_dirichletJetSpace hS hconv hM hB f hf ha,?_⟩
    rw [WeakSobolevJet.restrictDomain_value,M.nodalGlobalSobolevJet_value]
    apply Lp.ext
    exact (Physical.restrictRegionLp_ae S _).trans
      (((M.nodalGlobalLp_ae hS hM hB f hf).filter_mono ae_restrict_le).trans
        (M.nodalLp_ae hS.measurableSet hM f).symm)

theorem nodalLp_mem_dirichletConformingSpace (hS : IsOpen S) (hconv : Convex ℝ S)
    (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k) = 0) :
    M.nodalLp hS.measurableSet hM f ∈ M.conformingSpace (dirichletSubspace S) :=
  ⟨M.nodalLp_piecewise_affine hS.measurableSet hM f,
    M.nodalLp_mem_dirichletSubspace hS hconv hM hB f hf⟩

end SimplicialPartition
end Carleman
