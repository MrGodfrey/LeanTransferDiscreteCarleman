module

public import Carleman.Geometry.CartesianSpacetimeCells
public import Carleman.Control.CartesianPotentialReconstruction

/-! The original full spacetime piecewise-constant potential, zero on the true uncovered region. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ} (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ) (g : TimeGrid)
variable (b : BoundedMultiplier ((volume.restrict (Ioc 0 g.period)).prod
  (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))))

def cartesianSpacetimePotential :
    BoundedMultiplier ((volume.restrict (Ioc 0 g.period)).prod
      (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))) :=
  finiteCellMultiplier (cartesianSpacetimeCell o δ N g) (cartesianSpacetimeCell_measurable o δ N g)
    (cartesianSpacetimeCell_disjoint o δ hδ N g) (fun a => cartesianAveragedPotential o δ N g b a.1 a.2)
    b.bound b.bound_nonneg (fun a => cartesianAveragedPotential_bound o δ hδ N g b a.1 a.2)

theorem cartesianSpacetimePotential_bound : (cartesianSpacetimePotential o δ hδ N g b).bound=b.bound := rfl

theorem cartesianSpacetimePotential_on_cell (a : Fin g.steps × CartesianInteriorIndex N)
    {z : ℝ × SpatialCoordinates d} (hz : z ∈ cartesianSpacetimeCell o δ N g a) :
    (cartesianSpacetimePotential o δ hδ N g b).value z=cartesianAveragedPotential o δ N g b a.1 a.2 :=
  finiteCellFunction_on_cell _ (cartesianSpacetimeCell_disjoint o δ hδ N g) _ a hz

theorem cartesianSpacetimePotential_zero_outside {z : ℝ × SpatialCoordinates d}
    (hz : z ∉ ⋃ a : Fin g.steps × CartesianInteriorIndex N, cartesianSpacetimeCell o δ N g a) :
    (cartesianSpacetimePotential o δ hδ N g b).value z=0 :=
  finiteCellFunction_zero_outside _ _ hz

include hδ in
theorem cartesianAveragedPotential_product_formula (a : Fin g.steps × CartesianInteriorIndex N) :
    cartesianAveragedPotential o δ N g b a.1 a.2=(g.dt*(∏ j, δ j))⁻¹*
      ∫ z in cartesianSpacetimeCell o δ N g a, b.value z
        ∂((volume.restrict (Ioc 0 g.period)).prod
          (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))) := by
  rw [cartesianAveragedPotential_formula o δ hδ N g b a.1 a.2,
    cartesianSpacetimeCell,setIntegral_prod b.value b.integrable.restrict]
  simp only [Measure.restrict_restrict (show MeasurableSet (g.physicalTimeCell a.1) from measurableSet_Ioc),
    Measure.restrict_restrict (cartesianDualCell_measurable o δ N a.2),
    Set.inter_eq_left.mpr (g.physicalTimeCell_subset a.1),
    Set.inter_eq_left.mpr (cartesianDualCell_subset o δ hδ N a.2)]

theorem cartesianSpacetimePotential_on_time_cell (i : Fin g.steps) {t : ℝ}
    (ht : t ∈ g.physicalTimeCell i) (x : SpatialCoordinates d) :
    (cartesianSpacetimePotential o δ hδ N g b).value (t,x)=
      (cartesianReconstructedPotential o δ hδ N g b i).value x := by
  classical
  by_cases hx : x ∈ ⋃ a : CartesianInteriorIndex N, cartesianDualCell o δ N a
  · obtain ⟨a,ha⟩ := mem_iUnion.mp hx
    rw [cartesianSpacetimePotential_on_cell o δ hδ N g b (i,a) ⟨ht,ha⟩]
    exact (finiteCellFunction_on_cell _ (cartesianDualCell_disjoint o δ hδ N) _ a ha).symm
  · rw [cartesianReconstructedPotential_zero_outside o δ hδ N g b i hx]
    apply cartesianSpacetimePotential_zero_outside
    intro hz
    obtain ⟨a,ha⟩ := mem_iUnion.mp hz
    exact hx (mem_iUnion.mpr ⟨a.2,ha.2⟩)

def cartesianSpacetimeCellIsometry :
    PhysicalFiniteSpace (Fin g.steps × CartesianInteriorIndex N) (g.dt*(∏ j, δ j))
      (mul_pos g.dt_pos (Finset.prod_pos (fun j _ => hδ j))) →ₗᵢ[ℝ]
      Lp ℝ 2 ((volume.restrict (Ioc 0 g.period)).prod
        (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))) :=
  finiteCellIsometry (cartesianSpacetimeCell o δ N g) (cartesianSpacetimeCell_measurable o δ N g)
    (mul_pos g.dt_pos (Finset.prod_pos (fun j _ => hδ j))) (cartesianSpacetimeCell_disjoint o δ hδ N g)
    (cartesianSpacetimeCell_restrict_volume o δ hδ N g)

theorem cartesianSpacetimeCellIsometry_adjoint_average
    (u : Lp ℝ 2 ((volume.restrict (Ioc 0 g.period)).prod
      (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))))
    (a : Fin g.steps × CartesianInteriorIndex N) :
    ((cartesianSpacetimeCellIsometry o δ hδ N g).toContinuousLinearMap.adjoint u) a=
      (g.dt*(∏ j, δ j))⁻¹*∫ z in cartesianSpacetimeCell o δ N g a, u z
        ∂((volume.restrict (Ioc 0 g.period)).prod
          (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))) :=
  finiteCellIsometry_adjoint _ _ _ _ _ u a

end Carleman
