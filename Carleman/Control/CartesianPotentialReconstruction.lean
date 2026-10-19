module

public import Carleman.Control.CartesianAveragedPotential
public import Carleman.Spatial.FiniteCellMultiplier

/-! The original averaged potential reconstructed on dual cells, with exact discrete-continuous pairing. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ} (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ) (g : TimeGrid)
variable (b : BoundedMultiplier ((volume.restrict (Ioc 0 g.period)).prod
  (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))))

def cartesianReconstructedPotential (i : Fin g.steps) :
    BoundedMultiplier (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))) :=
  finiteCellMultiplier (cartesianDualCell o δ N) (cartesianDualCell_measurable o δ N)
    (cartesianDualCell_disjoint o δ hδ N) (cartesianAveragedPotential o δ N g b i)
    b.bound b.bound_nonneg (cartesianAveragedPotential_bound o δ hδ N g b i)

theorem cartesianReconstructedPotential_bound (i : Fin g.steps) :
    (cartesianReconstructedPotential o δ hδ N g b i).bound=b.bound := rfl

theorem cartesianReconstructedPotential_on_cell (i : Fin g.steps) (a : CartesianInteriorIndex N)
    {x : SpatialCoordinates d} (hx : x ∈ cartesianDualCell o δ N a) :
    (cartesianReconstructedPotential o δ hδ N g b i).value x=
      (g.dt*(∏ j, δ j))⁻¹ * ∫ t in g.physicalTimeCell i,
        ∫ y in cartesianDualCell o δ N a, b.value (t,y) := by
  change finiteCellFunction (cartesianDualCell o δ N) (cartesianAveragedPotential o δ N g b i) x=_
  rw [finiteCellFunction_on_cell _ (cartesianDualCell_disjoint o δ hδ N) _ a hx]
  exact cartesianAveragedPotential_formula o δ hδ N g b i a

theorem cartesianReconstructedPotential_zero_outside (i : Fin g.steps)
    {x : SpatialCoordinates d} (hx : x ∉ ⋃ a : CartesianInteriorIndex N, cartesianDualCell o δ N a) :
    (cartesianReconstructedPotential o δ hδ N g b i).value x=0 :=
  finiteCellFunction_zero_outside _ _ hx

theorem cartesianReconstructedPotential_commute (i : Fin g.steps) (z : CartesianPhysicalState δ hδ N) :
    (cartesianReconstructedPotential o δ hδ N g b i).map (cartesianCellIsometry o δ hδ N z)=
      cartesianCellIsometry o δ hδ N (PhysicalFiniteSpace.multiplier (cartesianAveragedPotential o δ N g b i) z) :=
  finiteCellMultiplier_commute _ _ _ _ _ _ _ _ z

theorem cartesianReconstructedPotential_pairing (i : Fin g.steps) (z w : CartesianPhysicalState δ hδ N) :
    inner ℝ (PhysicalFiniteSpace.multiplier (cartesianAveragedPotential o δ N g b i) z) w=
      inner ℝ ((cartesianReconstructedPotential o δ hδ N g b i).map (cartesianCellIsometry o δ hδ N z))
        (cartesianCellIsometry o δ hδ N w) := by
  rw [cartesianReconstructedPotential_commute,cartesianCellIsometry_inner]

end Carleman
