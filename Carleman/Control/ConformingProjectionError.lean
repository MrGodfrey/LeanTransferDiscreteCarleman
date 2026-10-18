module

public import Carleman.Control.GalerkinNumericalData

/-! Actual orthogonal projection errors from interpolation errors and weighted
projection/inverse estimates. These estimates are not asserted for a mesh. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Physical
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {ν : Measure Ω}
  (V X : Submodule ℝ (Lp E 2 ν)) [CompleteSpace X] (hX : X ≤ V)

def conformingProjector : V →ₗ[ℝ] V :=
  (X.inclusion hX).comp (X.orthogonalProjectionOnto.toLinearMap.comp V.subtype)

theorem conformingProjector_eq_Q (v : V) :
    conformingProjector V X hX v = (conformingReconstruction V X hX).Q (v : Lp E 2 ν) := rfl

theorem conformingProjector_inclusion (x : X) :
    conformingProjector V X hX (X.inclusion hX x) = X.inclusion hX x := by
  change X.inclusion hX (X.orthogonalProjectionOnto (x : Lp E 2 ν)) = _
  rw [X.orthogonalProjectionOnto_mem_subspace_eq_self]

theorem conformingProjector_error_decomposition (v : V) (x : X) :
    v-conformingProjector V X hX v =
      (v-X.inclusion hX x)-conformingProjector V X hX (v-X.inclusion hX x) := by
  rw [map_sub,conformingProjector_inclusion]
  abel

theorem conformingProjector_l2_error (σ : BoundedMultiplier ν) (Cp : ℝ)
    (hproj : ∀ u : Lp E 2 ν,
      σ.seminorm (X.orthogonalProjectionOnto u : Lp E 2 ν) ≤ Cp*σ.seminorm u)
    (v : V) (x : X) :
    σ.seminorm ((v-conformingProjector V X hX v : V) : Lp E 2 ν) ≤
      (1+Cp)*σ.seminorm ((v-X.inclusion hX x : V) : Lp E 2 ν) := by
  rw [conformingProjector_error_decomposition V X hX v x]
  let e := v-X.inclusion hX x
  have hh := map_sub_le_add σ.seminorm (e : Lp E 2 ν)
    (conformingProjector V X hX e : Lp E 2 ν)
  apply hh.trans
  have hp := hproj (e : Lp E 2 ν)
  change σ.seminorm (conformingProjector V X hX e : Lp E 2 ν) ≤ Cp*σ.seminorm (e : Lp E 2 ν) at hp
  linarith only [hp]

theorem conformingProjector_energy_error (p : Seminorm ℝ V) (ζ : BoundedMultiplier ν)
    (CI Cp : ℝ) (hCI : 0 ≤ CI)
    (hproj : ∀ u : Lp E 2 ν,
      ζ.seminorm (X.orthogonalProjectionOnto u : Lp E 2 ν) ≤ Cp*ζ.seminorm u)
    (hinv : ∀ x : X, p (X.inclusion hX x) ≤ CI*ζ.seminorm (x : Lp E 2 ν))
    (v : V) (x : X) :
    p (v-conformingProjector V X hX v) ≤
      p (v-X.inclusion hX x)+CI*Cp*ζ.seminorm ((v-X.inclusion hX x : V) : Lp E 2 ν) := by
  rw [conformingProjector_error_decomposition V X hX v x]
  let e := v-X.inclusion hX x
  apply (map_sub_le_add p e (conformingProjector V X hX e)).trans
  have hh := (hinv (X.orthogonalProjectionOnto (e : Lp E 2 ν))).trans
    (mul_le_mul_of_nonneg_left (hproj (e : Lp E 2 ν)) hCI)
  change p (conformingProjector V X hX e) ≤ CI*(Cp*ζ.seminorm (e : Lp E 2 ν)) at hh
  linarith only [hh]

end Carleman.Physical
