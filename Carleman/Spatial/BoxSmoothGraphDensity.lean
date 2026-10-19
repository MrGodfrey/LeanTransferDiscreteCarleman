module

public import Carleman.Spatial.SmoothDirichletGraph
public import Carleman.Spatial.BoxDirichletRegularity
public import Carleman.Continuous.RegularTimeCore

/-! Actual smooth zero-boundary states are dense in the full box Dirichlet operator graph. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman
variable {d : ℕ}

theorem exists_box_smooth_operator_graph_approximation (hd : 0 < d) (a b : Fin d → ℝ)
    (hpos : ∀ i, a i < b i) :
    let B := (boundedDirichletOriginalForm (openCoordinateBox_isOpen a b) hd
      (openCoordinateBox_isBounded a b)).model
    ∀ z : B.operatorGraph,
      ∃ U : ℕ → SpatialTest (univ : Set (SpatialCoordinates d)),
        ∃ Z : ℕ → B.operatorGraph,
          (∀ n, ∀ x ∈ frontier (openCoordinateBox a b), (U n).value x=0) ∧
          (∀ n, B.graphH (Z n)=(U n).toLp (volume.restrict (openCoordinateBox a b))) ∧
          (∀ n, B.graphA (Z n)= -(U n).laplacianOnLp (openCoordinateBox a b)) ∧
          Tendsto Z atTop (𝓝 z) := by
  intro B z
  let S := openCoordinateBox a b
  have hS : IsOpen S := openCoordinateBox_isOpen a b
  have hb : Bornology.IsBounded S := openCoordinateBox_isBounded a b
  obtain ⟨u,hu⟩ := box_dirichlet_domain_le_h2 hd a b hpos (B.graphDomain z).property
  have humem : WeakSobolevJet.value u ∈ dirichletSubspace S := by
    rw [hu]
    exact (boundedDirichletOriginalForm hS hd hb).domain_le (B.graphDomain z).property
  have hu0 : WeakSobolevJet.truncate (by decide : 1 ≤ 2) u ∈ dirichletJetSpace S :=
    (mem_dirichletJetSpace_iff S hS _).mpr humem
  have he : dirichletH2DomainElement hS hd hb u humem=B.graphDomain z :=
    Subtype.ext hu
  have hAu : negativeLaplacian u=B.graphA z := by
    have h := dirichletH2DomainElement_operator hS hd hb u humem
    rw [he,B.graphDomain_operator] at h
    exact h.symm
  obtain ⟨U,hbdy,h0,_,h2⟩ := exists_box_dirichlet_compact_h2_approximation a b hpos u hu0
  choose zn hzn hAn using fun n => (U n).exists_dirichlet_domain_of_boundary hS hd hb
    (openCoordinateBox_convex a b) (openCoordinateBox_nonempty a b hpos) (hbdy n)
  let Z := fun n => B.graphOfDomain (zn n)
  refine ⟨U,Z,hbdy,hzn,hAn,?_⟩
  have ht0 : Tendsto (fun n => (U n).toLp (volume.restrict S)) atTop (𝓝 (B.graphH z)) := by
    have ht := lp_tendsto_of_representative_L2_error (fun n => (U n).toLp (volume.restrict S))
      (WeakSobolevJet.value u) (fun n => (U n).value) (fun n => (U n).toLp_ae (volume.restrict S)) h0
    rw [hu] at ht
    convert! ht using 1
  have htA : Tendsto (fun n => -(U n).laplacianOnLp S) atTop (𝓝 (B.graphA z)) := by
    simpa only [hAu] using SpatialTest.laplacianOnLp_tendsto U u h2
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun n => ((zn n : Lp ℝ 2 (volume.restrict S)), B.operator (zn n))) atTop (𝓝 z.val)
  have heA : (fun n => B.operator (zn n))=(fun n => -(U n).laplacianOnLp S) := funext hAn
  change Tendsto (fun n => ((zn n : Lp ℝ 2 (volume.restrict S)), (fun n => B.operator (zn n)) n)) atTop (𝓝 z.val)
  rw [heA]
  simp only [hzn]
  exact ht0.prodMk_nhds htA

end Carleman
