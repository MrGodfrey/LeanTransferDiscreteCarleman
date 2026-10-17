module

public import Carleman.Transfer.Reconstruction
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Constructing the mass adjoint from the paper's reconstruction

The general algebraic interface accepts the defining mass equality as data.
Under the paper's Hilbert `H` and finite-dimensional real inner product `X`,
this module constructs that data from `R` alone, using mathlib's bounded
operator adjoint. Neither `V` nor `H` is required to be finite-dimensional,
and no norm on `V` other than its inclusion into `H` enters the construction.
-/

@[expose] public section

namespace Carleman.Reconstruction

variable {H X : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable {V : Submodule ℝ H}

/-- A linear reconstruction determines its mass adjoint in the actual paper spaces. -/
noncomputable def ofLinearMap (R : X →ₗ[ℝ] V) : Reconstruction V X where
  R := R
  J := (ContinuousLinearMap.adjoint (V.subtype.comp R).toContinuousLinearMap).toLinearMap
  mass_adjoint v z :=
    ContinuousLinearMap.adjoint_inner_left (V.subtype.comp R).toContinuousLinearMap z v

@[simp] theorem ofLinearMap_R (R : X →ₗ[ℝ] V) : (ofLinearMap R).R = R := rfl

/-- Existence and uniqueness of the map defined by `eq:massinterface`. -/
theorem existsUnique_mass_adjoint (R : X →ₗ[ℝ] V) :
    ∃! J : H →ₗ[ℝ] X, ∀ (v : H) (z : X),
      inner ℝ (J v) z = inner ℝ v (R z : H) :=
  ⟨(ofLinearMap R).J, (ofLinearMap R).mass_adjoint,
    fun J hJ => (ofLinearMap R).J_unique J hJ⟩

end Carleman.Reconstruction
