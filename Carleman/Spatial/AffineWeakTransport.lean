module

public import Carleman.Spatial.WeakDerivative
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Change variables in the full weak derivative identity using an actual
volume-preserving affine chart. All tests and L² representatives are transported. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Carleman
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def affineSpatialChart (A : E ≃L[ℝ] F) (b : F) : E ≃ₜ F :=
  A.toHomeomorph.trans (Homeomorph.addRight b)

theorem affineSpatialChart_apply (A : E ≃L[ℝ] F) (b : F) (x : E) :
    affineSpatialChart A b x=A x+b := rfl

theorem affineSpatialChart_hasFDerivAt (A : E ≃L[ℝ] F) (b : F) (x : E) :
    HasFDerivAt (affineSpatialChart A b) A.toContinuousLinearMap x :=
  A.hasFDerivAt.add_const b

namespace SpatialTest
variable {S : Set E} {T : Set F}

def pullbackAffine (φ : SpatialTest T) (A : E ≃L[ℝ] F) (b : F)
    (hST : (affineSpatialChart A b) ⁻¹' T ⊆ S) : SpatialTest S where
  value := φ.value ∘ affineSpatialChart A b
  smooth := φ.smooth.comp (A.contDiff.add contDiff_const)
  compact := φ.compact.comp_homeomorph (affineSpatialChart A b)
  support := by
    rw [tsupport_comp_eq_preimage]
    exact (preimage_mono φ.support).trans hST

theorem pullbackAffine_derivative (φ : SpatialTest T) (A : E ≃L[ℝ] F) (b : F)
    (hST : (affineSpatialChart A b) ⁻¹' T ⊆ S) (x e : E) :
    fderiv ℝ (φ.pullbackAffine A b hST).value x e =
      fderiv ℝ φ.value (affineSpatialChart A b x) (A e) := by
  have hd := ((φ.smooth.differentiable (by simp)).differentiableAt.hasFDerivAt).comp x
    (affineSpatialChart_hasFDerivAt A b x)
  exact congrArg (fun L : E →L[ℝ] ℝ => L e) hd.fderiv

end SpatialTest

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {ν : Measure E} {μ : Measure F}

def affineTransportLp (A : E ≃L[ℝ] F) (b : F)
    (hm : MeasurePreserving (affineSpatialChart A b) ν μ) : Lp ℝ 2 ν →+ Lp ℝ 2 μ :=
  Lp.compMeasurePreserving (affineSpatialChart A b).symm
    (MeasurePreserving.symm (affineSpatialChart A b).toMeasurableEquiv hm)

theorem affineTransportLp_ae (A : E ≃L[ℝ] F) (b : F)
    (hm : MeasurePreserving (affineSpatialChart A b) ν μ) (u : Lp ℝ 2 ν) :
    affineTransportLp A b hm u =ᵐ[μ] u ∘ (affineSpatialChart A b).symm :=
  Lp.coeFn_compMeasurePreserving _ _

theorem affineTransportLp_norm (A : E ≃L[ℝ] F) (b : F)
    (hm : MeasurePreserving (affineSpatialChart A b) ν μ) (u : Lp ℝ 2 ν) :
    ‖affineTransportLp A b hm u‖=‖u‖ := Lp.norm_compMeasurePreserving _ _

theorem integral_mul_affineTransportLp (A : E ≃L[ℝ] F) (b : F)
    (hm : MeasurePreserving (affineSpatialChart A b) ν μ) (u : Lp ℝ 2 ν) (a : F → ℝ) :
    (∫ y, a y * affineTransportLp A b hm u y ∂μ)=
      ∫ x, a (affineSpatialChart A b x)*u x ∂ν := by
  calc
    _ = ∫ y, a y*u ((affineSpatialChart A b).symm y) ∂μ := by
      apply integral_congr_ae
      filter_upwards [affineTransportLp_ae A b hm u] with y hy
      rw [hy]
      rfl
    _ = _ := by
      simpa using (MeasurePreserving.integral_comp'
        (f := (affineSpatialChart A b).toMeasurableEquiv) hm
        (fun y => a y*u ((affineSpatialChart A b).symm y))).symm

theorem IsWeakSpatialDerivative.affine_transport
    [IsFiniteMeasureOnCompacts ν] [IsFiniteMeasureOnCompacts μ]
    {S : Set E} {T : Set F} {e : E} {u v : Lp ℝ 2 ν}
    (hw : IsWeakSpatialDerivative ν S e u v) (A : E ≃L[ℝ] F) (b : F)
    (hm : MeasurePreserving (affineSpatialChart A b) ν μ)
    (hST : (affineSpatialChart A b) ⁻¹' T ⊆ S) :
    IsWeakSpatialDerivative μ T (A e)
      (affineTransportLp A b hm u) (affineTransportLp A b hm v) := by
  rw [IsWeakSpatialDerivative.iff_integral] at hw ⊢
  intro φ
  rw [integral_mul_affineTransportLp,integral_mul_affineTransportLp]
  have h := hw (φ.pullbackAffine A b hST)
  simp_rw [SpatialTest.pullbackAffine_derivative] at h
  exact h

end Carleman
