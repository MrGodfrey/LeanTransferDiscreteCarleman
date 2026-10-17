module

public import Carleman.Spatial.WeakDerivative
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Uniqueness of the genuine spatial weak derivative on an open domain. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ν : Measure E} [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set E}

/-- An L² class supported on the open domain is determined by all its smooth
compactly supported tests. Restricting volume to S supplies hν. -/
theorem spatial_eq_zero_of_tests (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
    (v : Lp ℝ 2 ν) (h : ∀ φ : SpatialTest S, inner ℝ v (φ.toLp ν) = 0) : v = 0 := by
  have ha := hS.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (((Lp.memLp v).locallyIntegrable (by norm_num)).locallyIntegrableOn S)
    (fun φ hφ hc hs => by
      let ψ : SpatialTest S := ⟨φ, hφ, hc, hs⟩
      have hp := h ψ
      rw [L2.inner_def] at hp
      convert hp using 1
      apply integral_congr_ae
      filter_upwards [ψ.toLp_ae ν] with x hx
      simp only [hx, RCLike.inner_apply, conj_trivial, smul_eq_mul]
      rfl)
  apply Lp.ext
  filter_upwards [ha, hν, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := ν)] with x hx hxs hz
  exact (hx hxs).trans hz.symm

namespace IsWeakSpatialDerivative
variable {e : E} {u v v' : Lp ℝ 2 ν}

theorem unique (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
    (h : IsWeakSpatialDerivative ν S e u v) (h' : IsWeakSpatialDerivative ν S e u v') :
    v = v' := by
  apply sub_eq_zero.mp
  apply spatial_eq_zero_of_tests hS hν
  intro φ
  rw [inner_sub_left]
  have hh := h φ
  have hh' := h' φ
  linarith

/-- There are no nonzero weak derivatives of the zero class. -/
theorem of_zero (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
    (h : IsWeakSpatialDerivative ν S e 0 v) : v = 0 :=
  h.unique hS hν zero
end IsWeakSpatialDerivative
end Carleman
