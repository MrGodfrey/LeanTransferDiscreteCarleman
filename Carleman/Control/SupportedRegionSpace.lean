module

public import Carleman.Control.ObservedRegionLp

/-! Actual a.e. spatial support as a closed Hilbert subspace, and recovery by zero extension. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace Carleman.Physical
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} (ω : Set Ω)

def supportedRegionSpace : Submodule ℝ (Lp ℝ 2 ν) := (restrictRegionCLM (ν := ν) ωᶜ).ker

theorem supportedRegionSpace_closed : IsClosed (supportedRegionSpace (ν := ν) ω : Set (Lp ℝ 2 ν)) :=
  (restrictRegionCLM (ν := ν) ωᶜ).isClosed_ker

theorem mem_supportedRegionSpace_iff (hω : MeasurableSet ω) (u : Lp ℝ 2 ν) :
    u ∈ supportedRegionSpace ω ↔ ∀ᵐ x ∂ν, x ∉ ω → u x = 0 := by
  change restrictRegionLp ωᶜ u = 0 ↔ _
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have he := restrictRegionLp_ae ωᶜ u
  constructor
  · intro hz
    apply (ae_restrict_iff' hω.compl).mp
    filter_upwards [he,hz] with x hx hz
    exact hx.symm.trans hz
  · intro hz
    have hh := (ae_restrict_iff' hω.compl).mpr hz
    exact he.trans hh

theorem zeroExtend_restrict_of_supported (hω : MeasurableSet ω) (u : Lp ℝ 2 ν)
    (hu : u ∈ supportedRegionSpace ω) : zeroExtendLp hω (restrictRegionLp ω u) = u := by
  have hz := (mem_supportedRegionSpace_iff ω hω u).mp hu
  apply Lp.ext
  filter_upwards [zeroExtendLp_ae hω (restrictRegionLp ω u),
    (ae_restrict_iff' hω).mp (restrictRegionLp_ae ω u),hz] with x he hr hh
  rw [he]
  by_cases hx : x ∈ ω
  · rw [indicator_of_mem hx,hr hx]
  · rw [indicator_of_notMem hx,hh hx]

end Carleman.Physical
