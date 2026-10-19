module

public import Carleman.Spatial.LocalWeightedNorm
public import Carleman.Spatial.CellwiseInverseWeight
public import Carleman.Continuous.BochnerNormAlgebra
public import Carleman.Continuous.NormDomination

/-! Local anchor comparisons for the actual global weighted Lp class,
including smaller measures whose sets need only be included almost everywhere. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman.BoundedMultiplier
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ ν : Measure X}

theorem bochner_map_restrict (w : BoundedMultiplier μ) (hνμ : ν ≤ μ) (u : Lp E 2 μ) :
    bochnerL2Norm ν (w.map u) = (w.restrictMeasure hνμ).seminorm
      (((Lp.memLp u).mono_measure hνμ).toLp u) := by
  rw [seminorm_apply,← bochnerL2Norm_coe]
  apply bochnerL2Norm_congr_ae
  filter_upwards [(w.map_ae u).filter_mono (ae_mono hνμ),
    (w.restrictMeasure hνμ).map_ae (((Lp.memLp u).mono_measure hνμ).toLp u),
    ((Lp.memLp u).mono_measure hνμ).coeFn_toLp] with x h1 h2 h3
  rw [h1,h2,h3]
  rfl

theorem bochner_map_le_anchor (w : BoundedMultiplier μ) (hνμ : ν ≤ μ) (W s : ℝ)
    (hw : ∀ᵐ x ∂ν, |w.value x| ≤ W*s) (u : Lp E 2 μ) :
    bochnerL2Norm ν (w.map u) ≤ W*s*bochnerL2Norm ν u := by
  rw [w.bochner_map_restrict hνμ u,bochnerL2Norm_eq u ((Lp.memLp u).mono_measure hνμ)]
  exact (w.restrictMeasure hνμ).seminorm_le_anchor W s hw _

theorem bochner_le_map_anchor (w : BoundedMultiplier μ) (hνμ : ν ≤ μ) (W s : ℝ) (hs : 0 < s)
    (hw : ∀ᵐ x ∂ν, s ≤ W*|w.value x|) (u : Lp E 2 μ) :
    bochnerL2Norm ν u ≤ (W/s)*bochnerL2Norm ν (w.map u) := by
  rw [w.bochner_map_restrict hνμ u,bochnerL2Norm_eq u ((Lp.memLp u).mono_measure hνμ)]
  exact (w.restrictMeasure hνμ).norm_le_seminorm_anchor W s hs hw _

end Carleman.BoundedMultiplier
