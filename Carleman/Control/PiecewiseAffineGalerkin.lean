module

public import Carleman.Spatial.PiecewiseAffinePartition
public import Carleman.Control.GalerkinStiffness

/-! The actual finite dimensional conforming piecewise affine space supplies
the Galerkin stiffness. It does not assert mesh approximation or a particular
Dirichlet realization of the variational space. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Physical
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasure ν]
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} {hS : IsOpen S} {hν : ∀ᵐ x ∂ν, x ∈ S}
  (a : OriginalForm (m := m) hS hν)
  {ι : Type*} [Fintype ι] (K : ι → Set (SpatialCoordinates d))
  (hK : ∀ i, MeasurableSet (K i)) (R : ℝ)
  (hR : ∀ i, ∀ᵐ x ∂ν, x ∈ K i → ‖x‖ ≤ R)

/-- This is the intersection with the actual variational subspace, not an
arbitrary finite dimensional state space supplied by the caller. -/
abbrev affineGalerkinSpace := conformingPiecewiseAffineSpace K hK R hR a.V

def affineGalerkinStiffness : affineGalerkinSpace a K hK R hR →L[ℝ] affineGalerkinSpace a K hK R hR :=
  galerkinStiffness a (affineGalerkinSpace a K hK R hR)
    (conformingPiecewiseAffineSpace_le K hK R hR a.V)

theorem affineGalerkinStiffness_pairing (x y : affineGalerkinSpace a K hK R hR) :
    inner ℝ (affineGalerkinStiffness a K hK R hR x) y =
      a.scalarForm (Submodule.inclusion (conformingPiecewiseAffineSpace_le K hK R hR a.V) x)
        (Submodule.inclusion (conformingPiecewiseAffineSpace_le K hK R hR a.V) y) :=
  galerkinStiffness_form a _ _ x y

theorem affineGalerkinStiffness_symmetric :
    (affineGalerkinStiffness a K hK R hR).toLinearMap.IsSymmetric :=
  galerkinStiffness_symmetric a _ _

theorem affineGalerkinStiffness_nonneg (x : affineGalerkinSpace a K hK R hR) :
    0 ≤ inner ℝ (affineGalerkinStiffness a K hK R hR x) x :=
  galerkinStiffness_nonneg a _ _ x

omit [IsLocallyFiniteMeasure ν] in
theorem affineGalerkinSpace_membership
    (hpartition : ∀ᵐ x ∂ν, ∃ i, x ∈ K i ∧ ∀ j, x ∈ K j → j=i)
    (u : Lp ℝ 2 ν) :
    u ∈ affineGalerkinSpace a K hK R hR ↔
      u ∈ a.V ∧ ∀ i, ∃ c : Fin (d+1) → ℝ, ∀ᵐ x ∂ν, x ∈ K i →
        u x = c 0+∑ j : Fin d, c j.succ*x j :=
  mem_conformingPiecewiseAffineSpace_iff K hK R hR hpartition a.V u

end Carleman.Physical
