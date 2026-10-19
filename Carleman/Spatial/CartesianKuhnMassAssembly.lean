module

public import Carleman.Spatial.CartesianKuhnReconstruction

/-! Exact assembly of the genuine cell vertex masses into the original
diagonal nodal mass, without a mesh-cardinality loss. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

theorem cartesianInteriorData_sq (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) (x : SpatialCoordinates d) :
    (cartesianInteriorData o δ N f x)^2=cartesianInteriorData o δ N (fun a => (f a)^2) x := by
  classical
  by_cases hx : ∃ a, cartesianInteriorPoint o δ N a=x
  · obtain ⟨a,rfl⟩ := hx
    rw [cartesianInteriorData_at_node o δ hδ N,cartesianInteriorData_at_node o δ hδ N]
  · have hn (a : CartesianInteriorIndex N) : cartesianInteriorPoint o δ N a ≠ x := fun h => hx ⟨a,h⟩
    simp only [cartesianInteriorData,ite_eq_right (hn _),Finset.sum_const_zero,zero_pow (by decide : 2≠0)]

theorem cartesianInteriorData_zero_compl (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) {x : SpatialCoordinates d}
    (hx : x ∉ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) :
    cartesianInteriorData o δ N f x=0 := by
  classical
  apply Finset.sum_eq_zero
  intro a _
  apply ite_eq_right
  intro he
  exact hx (he ▸ cartesianInteriorPoint_mem o δ hδ N a)

theorem cartesianKuhnLoadCoefficients_interiorData (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) (i : CartesianCellIndex N) (k : Fin (d+1)) :
    cartesianKuhnLoadCoefficients o δ hδ N (cartesianInteriorData o δ N f) i k=
      cartesianInteriorData o δ N f ((cartesianFiniteSimplex o δ hδ N i).points k) := by
  unfold cartesianKuhnLoadCoefficients
  split_ifs with h
  · rfl
  · exact (cartesianInteriorData_zero_compl o δ hδ N f h).symm

theorem cartesianKuhn_vertex_mass (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : CartesianInteriorIndex N) :
    (∑ i : CartesianCellIndex N, ∑ k : Fin (d+1),
      if (cartesianFiniteSimplex o δ hδ N i).points k=cartesianInteriorPoint o δ N a
      then volume.real (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)/(d+1:ℝ) else 0)=∏ j, δ j := by
  have ha := cartesianInteriorPoint_mem o δ hδ N a
  have hm := (cartesianKuhnPartition o δ hδ N).integral_eq_sum_cells
    (openCoordinateBox_isOpen _ _) (openCoordinateBox_convex _ _)
    (cartesianKuhnHat o δ hδ N (cartesianInteriorLatticeIndex N a))
    (cartesianKuhnHat_integrable o δ hδ N _ ha).integrableOn
  rw [cartesianKuhnHat_mass_domain o δ hδ N _ ha] at hm
  change (∏ j, δ j)=(∑ i : CartesianCellIndex N,
    ∫ x in simplicialCell (cartesianFiniteSimplex o δ hδ N i).points,
      cartesianKuhnHat o δ hδ N (cartesianInteriorLatticeIndex N a) x) at hm
  simp_rw [integral_cartesianKuhnHat_cell] at hm
  exact hm.symm

theorem cartesianKuhn_vertex_mass_assembly (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) :
    (∑ i : CartesianCellIndex N,
      (volume.real (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)/(d+1:ℝ))*
      (∑ k, cartesianInteriorData o δ N f ((cartesianFiniteSimplex o δ hδ N i).points k)))=
      (∏ j, δ j)*(∑ a, f a) := by
  classical
  have he (i : CartesianCellIndex N) :
      (volume.real (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)/(d+1:ℝ))*
      (∑ k, cartesianInteriorData o δ N f ((cartesianFiniteSimplex o δ hδ N i).points k))=
      ∑ a : CartesianInteriorIndex N, f a*(∑ k : Fin (d+1),
        if (cartesianFiniteSimplex o δ hδ N i).points k=cartesianInteriorPoint o δ N a
        then volume.real (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)/(d+1:ℝ) else 0) := by
    simp only [cartesianInteriorData,Finset.mul_sum,mul_ite,mul_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro k _
    simp only [eq_comm,mul_comm]
  simp_rw [he]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,cartesianKuhn_vertex_mass o δ hδ N]
  rw [← Finset.sum_mul,mul_comm]

theorem cartesianKuhn_vertex_mass_sq_assembly (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) :
    (∑ i : CartesianCellIndex N,
      (volume.real (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)/(d+1:ℝ))*
      (∑ k, (cartesianInteriorData o δ N f ((cartesianFiniteSimplex o δ hδ N i).points k))^2))=
      (∏ j, δ j)*(∑ a, (f a)^2) := by
  simp_rw [cartesianInteriorData_sq o δ hδ N]
  exact cartesianKuhn_vertex_mass_assembly o δ hδ N _

end Carleman
