module

public import Carleman.Spatial.WeakDerivativeUnique
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Differentiating an actual compactly supported smooth test retains its
support. The two classical test derivatives commute as actual L² classes. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Carleman.SpatialTest
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {S : Set E}

def derivativeTest (φ : SpatialTest S) (e : E) : SpatialTest S where
  value x := fderiv ℝ φ.value x e
  smooth := (φ.smooth.fderiv_right (by simp)).clm_apply contDiff_const
  compact := φ.compact.fderiv_apply ℝ e
  support := (tsupport_fderiv_apply_subset ℝ e).trans φ.support

theorem derivativeTest_toLp (φ : SpatialTest S) (e : E)
    (ν : Measure E) [IsFiniteMeasureOnCompacts ν] :
    (φ.derivativeTest e).toLp ν = φ.derivativeLp ν e := by
  apply Lp.ext
  exact ((φ.derivativeTest e).toLp_ae ν).trans (φ.derivativeLp_ae ν e).symm

theorem derivativeTest_derivativeLp_commute (φ : SpatialTest S) (e f : E)
    (ν : Measure E) [IsFiniteMeasureOnCompacts ν] :
    (φ.derivativeTest e).derivativeLp ν f = (φ.derivativeTest f).derivativeLp ν e := by
  have hdf : ContDiff ℝ 1 (fderiv ℝ φ.value) := φ.smooth.fderiv_right (by simp)
  have he (x : E) (v w : E) :
      fderiv ℝ (fun y => fderiv ℝ φ.value y v) x w = fderiv ℝ (fderiv ℝ φ.value) x w v := by
    have h := fderiv_clm_apply (hdf.differentiable (by simp) x) (differentiableAt_const v)
    simp only [fderiv_const_apply,ContinuousLinearMap.comp_zero,zero_add] at h
    exact congrArg (fun A : E →L[ℝ] ℝ => A w) h
  apply Lp.ext
  filter_upwards [(φ.derivativeTest e).derivativeLp_ae ν f,
    (φ.derivativeTest f).derivativeLp_ae ν e] with x hx hy
  rw [hx,hy]
  change fderiv ℝ (fun y => fderiv ℝ φ.value y e) x f =
    fderiv ℝ (fun y => fderiv ℝ φ.value y f) x e
  rw [he,he]
  exact φ.smooth.contDiffAt.isSymmSndFDerivAt (by simp) f e

end Carleman.SpatialTest
