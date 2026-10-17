module

public import Carleman.Spatial.OperatorMultiplier
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Const

/-! Spatial weak derivatives on L² classes. Every compactly supported smooth
scalar test function is admissible; its L² membership and that of its actual
Fréchet derivative are proved. The integration-by-parts condition is not a
pointwise regularity requirement on the state. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Carleman
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

structure SpatialTest (S : Set E) where
  value : E → ℝ
  smooth : ContDiff ℝ ∞ value
  compact : HasCompactSupport value
  support : tsupport value ⊆ S

namespace SpatialTest
variable {S : Set E} (φ : SpatialTest S) (ν : Measure E) [IsFiniteMeasureOnCompacts ν]

theorem memLp : MemLp φ.value 2 ν :=
  φ.smooth.continuous.memLp_of_hasCompactSupport φ.compact

theorem memLp_derivative (e : E) : MemLp (fun x => fderiv ℝ φ.value x e) 2 ν :=
  ((φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
    (φ.compact.fderiv_apply ℝ e)

def toLp : Lp ℝ 2 ν := (φ.memLp ν).toLp φ.value

def derivativeLp (e : E) : Lp ℝ 2 ν :=
  (φ.memLp_derivative ν e).toLp (fun x => fderiv ℝ φ.value x e)

theorem toLp_ae : φ.toLp ν =ᵐ[ν] φ.value := (φ.memLp ν).coeFn_toLp

theorem derivativeLp_ae (e : E) :
    φ.derivativeLp ν e =ᵐ[ν] (fun x => fderiv ℝ φ.value x e) :=
  (φ.memLp_derivative ν e).coeFn_toLp

end SpatialTest

/-- For the paper choose ν=volume restricted to the spatial domain S.
All state functions are L² equivalence classes. -/
def IsWeakSpatialDerivative (ν : Measure E) [IsFiniteMeasureOnCompacts ν]
    (S : Set E) (e : E) (u v : Lp ℝ 2 ν) : Prop :=
  ∀ φ : SpatialTest S, inner ℝ u (φ.derivativeLp ν e) = -inner ℝ v (φ.toLp ν)

namespace IsWeakSpatialDerivative
variable {ν : Measure E} [IsFiniteMeasureOnCompacts ν] {S : Set E} {e : E}
  {u v u' v' : Lp ℝ 2 ν}

/-- The definition is precisely the distributional identity on genuine
Lebesgue/Bochner integrals, using a.e. representatives only. -/
theorem iff_integral : IsWeakSpatialDerivative ν S e u v ↔
    ∀ φ : SpatialTest S,
      (∫ x, fderiv ℝ φ.value x e * u x ∂ν) = -(∫ x, φ.value x * v x ∂ν) := by
  have hi : ∀ (z : Lp ℝ 2 ν) (φ : SpatialTest S),
      inner ℝ z (φ.toLp ν) = ∫ x, φ.value x * z x ∂ν := by
    intro z φ
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [φ.toLp_ae ν] with x hx
    simp only [hx, RCLike.inner_apply, conj_trivial]
  have hd : ∀ (z : Lp ℝ 2 ν) (φ : SpatialTest S),
      inner ℝ z (φ.derivativeLp ν e) = ∫ x, fderiv ℝ φ.value x e * z x ∂ν := by
    intro z φ
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [φ.derivativeLp_ae ν e] with x hx
    simp only [hx, RCLike.inner_apply, conj_trivial]
  simp only [IsWeakSpatialDerivative, hi, hd]

theorem zero : IsWeakSpatialDerivative ν S e 0 0 := by
  intro φ
  simp

theorem add (h : IsWeakSpatialDerivative ν S e u v)
    (h' : IsWeakSpatialDerivative ν S e u' v') :
    IsWeakSpatialDerivative ν S e (u+u') (v+v') := by
  intro φ
  rw [inner_add_left, inner_add_left, h φ, h' φ]
  ring

theorem smul (h : IsWeakSpatialDerivative ν S e u v) (c : ℝ) :
    IsWeakSpatialDerivative ν S e (c • u) (c • v) := by
  intro φ
  rw [real_inner_smul_left, real_inner_smul_left, h φ]
  ring
end IsWeakSpatialDerivative
end Carleman
