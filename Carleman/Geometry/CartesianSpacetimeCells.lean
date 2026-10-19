module

public import Carleman.Geometry.CartesianDualCells
public import Carleman.Control.TimeCellReconstruction

/-! The actual product time cells and interior Cartesian dual cells. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

def cartesianSpacetimeCell (o δ : Fin d → ℝ) (N : Fin d → ℕ) (g : TimeGrid)
    (a : Fin g.steps × CartesianInteriorIndex N) : Set (ℝ × SpatialCoordinates d) :=
  g.physicalTimeCell a.1 ×ˢ cartesianDualCell o δ N a.2

theorem cartesianSpacetimeCell_measurable (o δ : Fin d → ℝ) (N : Fin d → ℕ) (g : TimeGrid)
    (a : Fin g.steps × CartesianInteriorIndex N) : MeasurableSet (cartesianSpacetimeCell o δ N g a) :=
  measurableSet_Ioc.prod (cartesianDualCell_measurable o δ N a.2)

theorem cartesianSpacetimeCell_disjoint (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (g : TimeGrid) : Pairwise fun a b : Fin g.steps × CartesianInteriorIndex N =>
      Disjoint (cartesianSpacetimeCell o δ N g a) (cartesianSpacetimeCell o δ N g b) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro x hxa hxb
  by_cases ht : a.1=b.1
  · have hs : a.2 ≠ b.2 := fun he => hab (Prod.ext ht he)
    exact Set.disjoint_left.mp (cartesianDualCell_disjoint o δ hδ N hs) hxa.2 hxb.2
  · exact Set.disjoint_left.mp (g.physicalTimeCell_disjoint ht) hxa.1 hxb.1

theorem cartesianSpacetimeCell_restrict_volume (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (g : TimeGrid) (a : Fin g.steps × CartesianInteriorIndex N) :
    ((volume.restrict (Ioc 0 g.period)).prod
      (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))).real
        (cartesianSpacetimeCell o δ N g a)=g.dt*(∏ j, δ j) := by
  rw [cartesianSpacetimeCell,measureReal_prod_prod,g.physicalTimeCell_restrict_volume,
    cartesianDualCell_restrict_volume o δ hδ N a.2]

end Carleman
