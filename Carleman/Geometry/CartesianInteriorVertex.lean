module

public import Carleman.Geometry.CartesianInteriorNodes

/-! Every actual lattice point in the open grid domain is represented by
exactly the original finite interior-node index type. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem cartesianGridPoint_interior_index (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (z : Fin d → ℤ)
    (hz : cartesianGridPoint o δ z ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) :
    ∃ a : CartesianInteriorIndex N, cartesianInteriorLatticeIndex N a=z := by
  have hb (j : Fin d) : 0 < z j ∧ z j < (N j:ℤ) := by
    have hj := hz j
    change o j < o j+(z j:ℝ)*δ j ∧ o j+(z j:ℝ)*δ j < o j+(N j:ℝ)*δ j at hj
    have hl : (0:ℝ) < z j := (mul_pos_iff_of_pos_right (hδ j)).mp (by linarith [hj.1])
    have hu : (z j:ℝ) < N j := (mul_lt_mul_iff_left₀ (hδ j)).mp (by linarith [hj.2])
    exact_mod_cast (show (0:ℝ) < (z j:ℝ) ∧ (z j:ℝ) < N j from ⟨hl,hu⟩)
  let a : CartesianInteriorIndex N := fun j => ⟨(z j-1).toNat,by have hj := hb j; omega⟩
  refine ⟨a,?_⟩
  funext j
  have hj := hb j
  change (((z j-1).toNat:ℤ)+1)=z j
  omega

theorem cartesianFiniteSimplex_interior_vertex (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (i : CartesianCellIndex N) (k : Fin (d+1))
    (hk : (cartesianFiniteSimplex o δ hδ N i).points k ∈
      openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) :
    ∃ a : CartesianInteriorIndex N,
      cartesianInteriorPoint o δ N a=(cartesianFiniteSimplex o δ hδ N i).points k := by
  have he := cartesianKuhnSimplex_points_eq_gridPoint o δ hδ (cartesianCellLatticeIndex N i).1 i.2 k
  change (cartesianFiniteSimplex o δ hδ N i).points k=_ at he
  rw [he] at hk ⊢
  obtain ⟨a,ha⟩ := cartesianGridPoint_interior_index o δ hδ N _ hk
  exact ⟨a,by rw [cartesianInteriorPoint,ha]⟩

end Carleman
