module

public import Carleman.Spatial.DirichletZeroExtension

/-! The actual H¹ zero extension is continuous on the original H¹₀
space, and agrees with the original global function for every smooth test. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Carleman
variable {d : ℕ} {T : Set (SpatialCoordinates d)}

theorem SpatialTest.zeroExtendDirichlet_value_ae (hT : IsOpen T) (φ : SpatialTest T) :
    WeakSobolevJet.value (WeakSobolevJet.zeroExtendDirichlet hT φ.sobolevJet
      (test_mem_dirichletJetSpace T φ)) =ᵐ[volume] φ.value := by
  rw [WeakSobolevJet.zeroExtendDirichlet_value,φ.sobolevJet_value]
  have ha := (ae_restrict_iff' hT.measurableSet).mp (φ.toLp_ae (volume.restrict T))
  filter_upwards [zeroExtendLp_ae hT.measurableSet (φ.toLp (volume.restrict T)),ha] with x hx hf
  rw [hx]
  by_cases ht : x ∈ T
  · rw [indicator_of_mem ht,hf ht]
  · rw [indicator_of_notMem ht]
    exact (image_eq_zero_of_notMem_tsupport (fun h => ht (φ.support h))).symm

theorem WeakSobolevJet.zeroExtendDirichlet_tendsto (hT : IsOpen T)
    (U : ℕ → WeakSobolevJet d 1 (volume.restrict T) T)
    (hU : ∀ n, U n ∈ dirichletJetSpace T)
    (u : WeakSobolevJet d 1 (volume.restrict T) T) (hu : u ∈ dirichletJetSpace T)
    (ht : Tendsto U atTop (𝓝 u)) :
    Tendsto (fun n => zeroExtendDirichlet hT (U n) (hU n)) atTop
      (𝓝 (zeroExtendDirichlet hT u hu)) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro k
  change Tendsto (fun n => zeroExtendLp hT.measurableSet (field k (U n))) atTop
    (𝓝 (zeroExtendLp hT.measurableSet (field k u)))
  have hf := ((fieldCLM k).continuous.tendsto u).comp ht
  have he := ((Physical.restrictRegionCLM (ν := volume) (E := DerivativeFiber d k.val) T).adjoint.continuous.tendsto
    (field k u)).comp hf
  simpa only [Function.comp_def,fieldCLM_apply,Physical.restrictRegion_adjoint T hT.measurableSet] using he

end Carleman
