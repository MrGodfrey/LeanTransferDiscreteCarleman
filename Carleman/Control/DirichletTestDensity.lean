module

public import Carleman.Control.P1TestInterpolation
public import Carleman.Spatial.SpatialTestOperations

/-! Original smooth tests are dense in the actual Dirichlet energy norm. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology BigOperators NNReal
namespace Carleman
variable {d : ℕ}

theorem exists_dirichlet_test_sequence {S : Set (SpatialCoordinates d)} (hS : IsOpen S)
    (w : DirichletEnergyState S) :
    ∃ ψ : ℕ → SpatialTest S, Tendsto (fun n => (ψ n).dirichletState) atTop (𝓝 w) := by
  have hm : SobolevHilbert.toJet w.val ∈ dirichletJetSpace S :=
    (mem_dirichletJetSpace_iff S hS _).mpr w.property
  obtain ⟨u,hu,ht⟩ := mem_closure_iff_seq_limit.mp hm
  choose ψ hψ using fun n => exists_test_of_mem_test_span hS (hu n)
  refine ⟨ψ,?_⟩
  apply tendsto_subtype_rng.mpr
  have hh := SobolevHilbert.ofJet.continuous.tendsto _ |>.comp ht
  have he : SobolevHilbert.ofJet (SobolevHilbert.toJet w.val)=w.val :=
    SobolevHilbert.jetEquiv.symm_apply_apply w.val
  rw [he] at hh
  simpa only [Function.comp_def,← hψ,SpatialTest.dirichletState] using hh

end Carleman
