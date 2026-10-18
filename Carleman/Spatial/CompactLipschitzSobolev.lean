module

public import Carleman.Spatial.LipschitzGlobalSobolev
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! Every actual compactly supported Lipschitz function has a full-space
H¹ jet with its genuine a.e. Frechet derivative. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace Carleman
variable {d : ℕ} {f : SpatialCoordinates d → ℝ} {C : ℝ≥0}

theorem compactLipschitz_fderiv_memLp (hC : LipschitzWith C f) (hf : HasCompactSupport f) :
    MemLp (fderiv ℝ f) 2 (volume : Measure (SpatialCoordinates d)) := by
  have hg : MemLp ((tsupport f).indicator (fun _ => (C : ℝ))) 2
      (volume : Measure (SpatialCoordinates d)) :=
    memLp_indicator_const _ (isClosed_tsupport f).measurableSet.nullMeasurableSet _
      (.inr hf.measure_lt_top.ne)
  apply hg.of_le_mul (c := 1) (measurable_fderiv ℝ f).aestronglyMeasurable
  filter_upwards with x
  by_cases hx : x ∈ tsupport f
  · rw [indicator_of_mem hx,one_mul,Real.norm_eq_abs,abs_of_nonneg C.coe_nonneg]
    exact norm_fderiv_le_of_lipschitz ℝ hC
  · rw [indicator_of_notMem hx,fderiv_of_notMem_tsupport ℝ hx]
    simp

def compactLipschitzDerivativeLp (hC : LipschitzWith C f) (hf : HasCompactSupport f) :
    Lp (SpatialCoordinates d →L[ℝ] ℝ) 2 (volume : Measure (SpatialCoordinates d)) :=
  (compactLipschitz_fderiv_memLp hC hf).toLp (fderiv ℝ f)

theorem compactLipschitzDerivativeLp_ae (hC : LipschitzWith C f) (hf : HasCompactSupport f) :
    compactLipschitzDerivativeLp hC hf =ᵐ[volume] fderiv ℝ f := MemLp.coeFn_toLp _

def compactLipschitzLp (hC : LipschitzWith C f) (hf : HasCompactSupport f) :
    Lp ℝ 2 (volume : Measure (SpatialCoordinates d)) :=
  (hC.continuous.memLp_of_hasCompactSupport hf).toLp f

theorem compactLipschitzLp_ae (hC : LipschitzWith C f) (hf : HasCompactSupport f) :
    compactLipschitzLp hC hf =ᵐ[volume] f := MemLp.coeFn_toLp _

def compactLipschitzSobolevJet (hC : LipschitzWith C f) (hf : HasCompactSupport f) :
    WeakSobolevJet d 1 volume Set.univ := by
  apply lipschitzGlobalJet hC (compactLipschitzLp hC hf) (compactLipschitzDerivativeLp hC hf)
    (compactLipschitzLp_ae hC hf)
  filter_upwards [compactLipschitzDerivativeLp_ae hC hf,hC.ae_differentiableAt (μ := volume)] with x hx hd
  rw [hx]
  exact hd.hasFDerivAt

theorem compactLipschitzSobolevJet_value (hC : LipschitzWith C f) (hf : HasCompactSupport f) :
    WeakSobolevJet.value (compactLipschitzSobolevJet hC hf) = compactLipschitzLp hC hf :=
  lipschitzGlobalJet_value _ _ _ _ _

end Carleman
