module

public import Carleman.Spatial.CartesianKuhnNodal

/-! The actual nodal hats agree with barycentric coordinates on incident
cells and have topological support in their finite closed vertex stars. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

theorem cartesianKuhnHat_on_incidentCell (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ) (i : CartesianCellIndex N) (k : Fin (d+1))
    (ha : cartesianGridPoint o δ a=(cartesianFiniteSimplex o δ hδ N i).points k)
    {x : SpatialCoordinates d} (hx : x ∈ simplicialCell (cartesianFiniteSimplex o δ hδ N i).points) :
    cartesianKuhnHat o δ hδ N a x=simplexBarycentric (cartesianFiniteSimplex o δ hδ N i) k x := by
  rw [cartesianKuhnHat_on_cell o δ hδ N a i hx,ha]
  simp only [(cartesianFiniteSimplex o δ hδ N i).independent.injective.eq_iff,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem cartesianKuhnHat_zero_on_nonincidentCell (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ) (i : CartesianCellIndex N)
    (ha : cartesianGridPoint o δ a ∉ Set.range (cartesianFiniteSimplex o δ hδ N i).points)
    {x : SpatialCoordinates d} (hx : x ∈ simplicialCell (cartesianFiniteSimplex o δ hδ N i).points) :
    cartesianKuhnHat o δ hδ N a x=0 := by
  rw [cartesianKuhnHat_on_cell o δ hδ N a i hx]
  apply Finset.sum_eq_zero
  intro k _
  exact ite_eq_right (fun he => ha ⟨k,he⟩)

def cartesianFiniteNodeStar (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ) : Set (SpatialCoordinates d) :=
  ⋃ i : CartesianCellIndex N,
    if cartesianGridPoint o δ a ∈ Set.range (cartesianFiniteSimplex o δ hδ N i).points
    then simplicialCell (cartesianFiniteSimplex o δ hδ N i).points else ∅

theorem cartesianFiniteNodeStar_compact (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ) : IsCompact (cartesianFiniteNodeStar o δ hδ N a) := by
  apply isCompact_iUnion
  intro i
  split_ifs
  · exact simplicialCell_compact _
  · exact isCompact_empty

theorem cartesianKuhnHat_support_subset (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ) :
    Function.support (cartesianKuhnHat o δ hδ N a) ⊆ cartesianFiniteNodeStar o δ hδ N a := by
  intro x hx
  have hc : x ∈ closure (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) := by
    by_contra hn
    exact hx ((cartesianKuhnPartition o δ hδ N).nodalFunction_zero_outside _ hn)
  rw [← (cartesianKuhnPartition o δ hδ N).cells_union] at hc
  obtain ⟨i,hi⟩ := mem_iUnion.mp hc
  change x ∈ simplicialCell (cartesianFiniteSimplex o δ hδ N i).points at hi
  have ha : cartesianGridPoint o δ a ∈ Set.range (cartesianFiniteSimplex o δ hδ N i).points := by
    by_contra hn
    exact hx (cartesianKuhnHat_zero_on_nonincidentCell o δ hδ N a i hn hi)
  exact mem_iUnion.mpr ⟨i,by simpa only [ite_eq_left ha] using hi⟩

theorem cartesianKuhnHat_tsupport_subset (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ) :
    tsupport (cartesianKuhnHat o δ hδ N a) ⊆ cartesianFiniteNodeStar o δ hδ N a :=
  closure_minimal (cartesianKuhnHat_support_subset o δ hδ N a)
    (cartesianFiniteNodeStar_compact o δ hδ N a).isClosed

theorem cartesianKuhnHat_tsupport_subset_cellStar (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ) (i : CartesianCellIndex N)
    (ha : cartesianGridPoint o δ a ∈ Set.range (cartesianFiniteSimplex o δ hδ N i).points) :
    tsupport (cartesianKuhnHat o δ hδ N a) ⊆
      cartesianKuhnStarPatch o δ hδ (cartesianCellLatticeIndex N i).1 i.2 := by
  intro x hx
  obtain ⟨j,hj⟩ := mem_iUnion.mp (cartesianKuhnHat_tsupport_subset o δ hδ N a hx)
  by_cases hn : cartesianGridPoint o δ a ∈ Set.range (cartesianFiniteSimplex o δ hδ N j).points
  · rw [ite_eq_left hn] at hj
    obtain ⟨k,hk⟩ := ha
    obtain ⟨l,hl⟩ := hn
    exact ⟨(cartesianCellLatticeIndex N j).1,j.2,k,l,hk.trans hl.symm,hj⟩
  · simp only [ite_eq_right hn,mem_empty_iff_false] at hj

end Carleman
