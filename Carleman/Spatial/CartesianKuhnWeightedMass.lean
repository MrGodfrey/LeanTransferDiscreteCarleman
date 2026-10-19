module

public import Carleman.Spatial.CartesianKuhnMassAssembly

/-! Exact assembly of the original weighted diagonal nodal mass. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

theorem cartesianInteriorData_weight (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) (w : SpatialCoordinates d → ℝ)
    (x : SpatialCoordinates d) :
    cartesianInteriorData o δ N (fun a => w (cartesianInteriorPoint o δ N a)*f a) x=
      w x*cartesianInteriorData o δ N f x := by
  classical
  by_cases hx : ∃ a, cartesianInteriorPoint o δ N a=x
  · obtain ⟨a,rfl⟩ := hx
    rw [cartesianInteriorData_at_node o δ hδ N,cartesianInteriorData_at_node o δ hδ N]
  · have hn (a : CartesianInteriorIndex N) : cartesianInteriorPoint o δ N a ≠ x := fun h => hx ⟨a,h⟩
    simp only [cartesianInteriorData,ite_eq_right (hn _),Finset.sum_const_zero,mul_zero]

theorem cartesianKuhn_weighted_mass_assembly (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) (w : SpatialCoordinates d → ℝ) :
    (∑ i : CartesianCellIndex N,
      (volume.real (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)/(d+1:ℝ))*
      (∑ k, (w ((cartesianFiniteSimplex o δ hδ N i).points k)*
        cartesianInteriorData o δ N f ((cartesianFiniteSimplex o δ hδ N i).points k))^2))=
      (∏ j, δ j)*(∑ a, (w (cartesianInteriorPoint o δ N a)*f a)^2) := by
  have h := cartesianKuhn_vertex_mass_sq_assembly o δ hδ N
    (fun a => w (cartesianInteriorPoint o δ N a)*f a)
  simpa only [cartesianInteriorData_weight o δ hδ N] using h

end Carleman
