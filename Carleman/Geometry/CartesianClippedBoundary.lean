module

public import Carleman.Geometry.CartesianClippedPatch
public import Carleman.Geometry.KuhnFaceMatching

/-! Physical faces of the concrete clipped patches contain every physical
boundary point of the central cell, including all boundary vertices. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem cartesianFiniteSimplex_subset_closedPatch (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (i : CartesianCellIndex N) :
    simplicialCell (cartesianFiniteSimplex o δ hδ N i).points ⊆
      closedCoordinateBox (cartesianClippedPatchLower o δ N i) (cartesianClippedPatchUpper o δ N i) := by
  intro x hx j
  have hb := cartesianKuhnSimplex_cell_subset_box o δ hδ (cartesianCellLatticeIndex N i).1 i.2 hx j
  change o j+((i.1 j).val:ℝ)*δ j ≤ x j ∧ x j ≤ o j+(((i.1 j).val:ℝ)+1)*δ j at hb
  have hz : (0:ℝ) ≤ (i.1 j).val := Nat.cast_nonneg _
  have hN : ((i.1 j).val:ℝ)+1 ≤ N j := by exact_mod_cast (i.1 j).isLt
  constructor
  · apply max_le <;> nlinarith [hδ j]
  · apply le_min <;> nlinarith [hδ j]

theorem cartesianClosedPatch_subset_closedDomain (o δ : Fin d → ℝ)
    (N : Fin d → ℕ) (i : CartesianCellIndex N) :
    closedCoordinateBox (cartesianClippedPatchLower o δ N i) (cartesianClippedPatchUpper o δ N i) ⊆
      closedCoordinateBox o (fun j => o j+(N j:ℝ)*δ j) := by
  intro x hx j
  exact ⟨(le_max_left _ _).trans (hx j).1,(hx j).2.trans (min_le_left _ _)⟩

def cartesianClippedPhysicalFaces (o δ : Fin (d+1) → ℝ) (N : Fin (d+1) → ℕ)
    (i : CartesianCellIndex N) : Finset (Fin (d+1) × Bool) := by
  classical
  exact Finset.univ.filter (fun f => if f.2 then
    cartesianClippedPatchUpper o δ N i f.1=o f.1+(N f.1:ℝ)*δ f.1
    else cartesianClippedPatchLower o δ N i f.1=o f.1)

theorem cartesianClippedPhysicalFaces_frontier (o δ : Fin (d+1) → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin (d+1) → ℕ) (i : CartesianCellIndex N) (f : Fin (d+1) × Bool)
    (hf : f ∈ cartesianClippedPhysicalFaces o δ N i) :
    coordinateClosedFace f.1 (cartesianClippedPatchLower o δ N i) (cartesianClippedPatchUpper o δ N i) f.2 ⊆
      frontier (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) := by
  intro x hx
  have hpos (j : Fin (d+1)) : o j < o j+(N j:ℝ)*δ j := by
    have hn : (0:ℝ) < N j := by exact_mod_cast (show 0 < N j by have h := (i.1 j).isLt; omega)
    nlinarith [hδ j]
  have hc : x ∈ closure (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) := by
    rw [closure_openCoordinateBox _ _ hpos]
    exact cartesianClosedPatch_subset_closedDomain o δ N i hx.1
  change x ∈ closure (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) ∧
    x ∉ interior (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))
  refine ⟨hc,?_⟩
  rw [(openCoordinateBox_isOpen _ _).interior_eq]
  intro hn
  have hb := (Finset.mem_filter.mp hf).2
  have he := hx.2
  cases f with
  | mk j upper =>
    cases upper <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hb he
    · change x j=cartesianClippedPatchLower o δ N i j at he
      rw [hb] at he
      exact (ne_of_gt (hn j).1) he
    · change x j=cartesianClippedPatchUpper o δ N i j at he
      rw [hb] at he
      exact (ne_of_lt (hn j).2) he

theorem cartesianCell_boundary_in_physicalFace (o δ : Fin (d+1) → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin (d+1) → ℕ) (i : CartesianCellIndex N) {x : SpatialCoordinates (d+1)}
    (hx : x ∈ simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)
    (hn : x ∉ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) :
    ∃ f ∈ cartesianClippedPhysicalFaces o δ N i,
      x ∈ coordinateClosedFace f.1 (cartesianClippedPatchLower o δ N i) (cartesianClippedPatchUpper o δ N i) f.2 := by
  classical
  have hp := cartesianFiniteSimplex_subset_closedPatch o δ hδ N i hx
  have hS := cartesianClosedPatch_subset_closedDomain o δ N i hp
  change ¬ ∀ j, o j < x j ∧ x j < o j+(N j:ℝ)*δ j at hn
  push Not at hn
  obtain ⟨j,hj⟩ := hn
  by_cases hl : o j < x j
  · have he : x j=o j+(N j:ℝ)*δ j := le_antisymm (hS j).2 (hj hl)
    have hb : cartesianClippedPatchUpper o δ N i j=o j+(N j:ℝ)*δ j :=
      le_antisymm (min_le_left _ _) (he ▸ (hp j).2)
    refine ⟨(j,true),?_,hp,?_⟩
    · simp only [cartesianClippedPhysicalFaces,Finset.mem_filter,Finset.mem_univ,true_and,ite_true]
      exact hb
    · simpa only [mem_ofPred_eq,ite_true,hb] using he
  · have he : x j=o j := le_antisymm (le_of_not_gt hl) (hS j).1
    have hb : cartesianClippedPatchLower o δ N i j=o j :=
      le_antisymm (he ▸ (hp j).1) (le_max_left _ _)
    refine ⟨(j,false),?_,hp,?_⟩
    · simp only [cartesianClippedPhysicalFaces,Finset.mem_filter,Finset.mem_univ,true_and,Bool.false_eq_true,ite_false]
      exact hb
    · simpa only [mem_ofPred_eq,Bool.false_eq_true,ite_false,hb] using he

theorem cartesianPhysicalFace_zero_on_boundaryCell (o δ : Fin (d+1) → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin (d+1) → ℕ) (i : CartesianCellIndex N) (p : SpatialCoordinates (d+1) → ℝ)
    (hp : ∀ f ∈ cartesianClippedPhysicalFaces o δ N i, ∀ y ∈
      coordinateClosedFace f.1 (cartesianClippedPatchLower o δ N i) (cartesianClippedPatchUpper o δ N i) f.2, p y=0)
    {x : SpatialCoordinates (d+1)} (hx : x ∈ simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)
    (hn : x ∉ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) : p x=0 := by
  obtain ⟨f,hf,hy⟩ := cartesianCell_boundary_in_physicalFace o δ hδ N i hx hn
  exact hp f hf x hy

end Carleman
