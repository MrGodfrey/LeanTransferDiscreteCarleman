module

public import Carleman.Transfer.SpatialConsistency
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Existence for every load in the fully discrete auxiliary scheme. The
finite-dimensional argument applies to the entire cyclic state space and
uses the already proved uniqueness with the genuine mass G=JR. -/
@[expose] public noncomputable section
namespace Carleman.Reconstruction
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  {V : Submodule ℝ H} (r : Reconstruction V X) (g : TimeGrid)

def auxiliaryEuler (s : Orientation) (A : X →ₗ[ℝ] X) (μ : g.Sequence ℝ) :
    g.Sequence X →ₗ[ℝ] g.Sequence X where
  toFun z := s.difference g z + r.shiftedSpatial g A μ z
  map_add' u v := by
    funext i
    simp only [Pi.add_apply, Orientation.difference_neighbor, shiftedSpatial,
      map_add, smul_add]
    module
  map_smul' c u := by
    funext i
    simp only [Pi.smul_apply, Orientation.difference_neighbor, shiftedSpatial,
      map_smul, RingHom.id_apply, smul_sub, smul_add]
    module

theorem auxiliaryEuler_injective (s : Orientation) (hR : Function.Injective r.R)
    (A : X →ₗ[ℝ] X) (hA : ∀ z, 0 ≤ inner ℝ (A z) z)
    (μ : g.Sequence ℝ) (hμ : ∀ i, 0 < μ i) :
    Function.Injective (r.auxiliaryEuler g s A μ) := by
  intro u v h
  cases s
  · exact r.shifted_dPlus_unique g hR A hA μ hμ u v h
  · exact r.shifted_dMinus_unique g hR A hA μ hμ u v h

/-- The paper's assertion after `eq:auxEuler`, for both time directions,
any positive nodal shift and every load on the full finite-dimensional X. -/
theorem existsUnique_auxiliaryEuler [FiniteDimensional ℝ X]
    (s : Orientation) (hR : Function.Injective r.R)
    (A : X →ₗ[ℝ] X) (hA : ∀ z, 0 ≤ inner ℝ (A z) z)
    (μ : g.Sequence ℝ) (hμ : ∀ i, 0 < μ i) (f : g.Sequence X) :
    ∃! z : g.Sequence X, s.difference g z + r.shiftedSpatial g A μ z = f := by
  have hi := r.auxiliaryEuler_injective g s hR A hA μ hμ
  have hs := (LinearMap.injective_iff_surjective (f := r.auxiliaryEuler g s A μ)).mp hi
  obtain ⟨z, hz⟩ := hs f
  exact ⟨z, hz, fun v hv => hi (hv.trans hz.symm)⟩

end Carleman.Reconstruction
