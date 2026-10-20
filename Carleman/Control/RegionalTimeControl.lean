module

public import Carleman.Control.SupportedTimeControl
public import Carleman.Control.TimeReconstructionEstimates

/-! Actual regional time controls retain exactly their norm and spatial support. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Carleman

theorem regional_time_control_norm {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (T : ℝ) (g : TimeGrid) (hT : g.period=T) (ω : Set Ω) (hω : MeasurableSet ω)
    (u : Fin g.steps → Lp ℝ 2 (ν.restrict ω)) :
    ‖fixedTimeCellReconstruction T g hT
      (fun i => (Physical.restrictRegionCLM (ν := ν) ω).adjoint (u i))‖=Physical.controlNorm g.dt u := by
  subst T
  change ‖timeCellReconstruction g (fun i => (Physical.restrictRegionCLM (ν := ν) ω).adjoint (u i))‖=_
  rw [timeCellReconstruction_norm]
  simp only [Physical.controlNorm,Physical.restrictRegion_adjoint ω hω,zeroExtendLp_norm]

theorem regional_time_control_supported {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (T : ℝ) (g : TimeGrid) (hT : g.period=T) (ω : Set Ω) (hω : MeasurableSet ω)
    (u : Fin g.steps → Lp ℝ 2 (ν.restrict ω)) :
    ∀ᵐ t ∂volume.restrict (Ioc 0 T), fixedTimeCellReconstruction T g hT
      (fun i => (Physical.restrictRegionCLM (ν := ν) ω).adjoint (u i)) t ∈ Physical.supportedRegionSpace ω := by
  subst T
  have hs i : (Physical.restrictRegionCLM (ν := ν) ω).adjoint (u i) ∈ Physical.supportedRegionSpace ω := by
    apply (Physical.mem_supportedRegionSpace_iff ω hω _).mpr
    rw [Physical.restrictRegion_adjoint ω hω]
    filter_upwards [zeroExtendLp_ae hω (u i)] with x hx
    intro hn
    rw [hx,indicator_of_notMem hn]
  have he := timeCellReconstruction_ae g
    (fun i => (Physical.restrictRegionCLM (ν := ν) ω).adjoint (u i))
  filter_upwards [he] with t ht
  change timeCellReconstruction g (fun i => (Physical.restrictRegionCLM (ν := ν) ω).adjoint (u i)) t ∈ _
  rw [ht]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : t ∈ g.physicalTimeCell i
  · simpa only [indicator_of_mem hi] using hs i
  · simp only [indicator_of_notMem hi,Submodule.zero_mem]


end Carleman
