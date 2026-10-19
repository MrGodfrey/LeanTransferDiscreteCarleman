module

public import Carleman.Geometry.FiniteCartesianKuhnCover
public import Mathlib.Order.Preorder.Finite

/-! Actual interior separation of the Cartesian Kuhn cells. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman

theorem linear_strict_of_mem_interior_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E →L[ℝ] ℝ) (v : E) (hv : 0 < f v)
    {S : Set E} {c : ℝ} (hS : ∀ y ∈ S, f y ≤ c) {x : E}
    (hx : x ∈ interior S) : f x < c := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  let a : ℝ := ε/(‖v‖+1)
  have hd : 0 < ‖v‖+1 := by positivity
  have ha : 0 < a := div_pos hε hd
  have hab : a*‖v‖ < ε := by
    have he : a*(‖v‖+1)=ε := div_mul_cancel₀ ε hd.ne'
    nlinarith
  have hm : x+a • v ∈ S := hball (by
    rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
      abs_of_pos ha]
    exact hab)
  have hl := hS (x+a • v) hm
  rw [map_add,map_smul] at hl
  change f x+a*f v ≤ c at hl
  nlinarith [mul_pos ha hv]

variable {d : ℕ}

theorem cartesianKuhnSimplex_interior_box (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) {x : SpatialCoordinates d}
    (hx : x ∈ interior (simplicialCell (cartesianKuhnSimplex o δ hδ z π).points)) :
    ∀ j, o j+(z j:ℝ)*δ j < x j ∧ x j < o j+((z j:ℝ)+1)*δ j := by
  intro j
  have hb := cartesianKuhnSimplex_cell_subset_box o δ hδ z π
  constructor
  · have h := linear_strict_of_mem_interior_le (-(EuclideanSpace.proj j))
      (-(EuclideanSpace.basisFun (Fin d) ℝ j)) (by simp)
      (c := -(o j+(z j:ℝ)*δ j)) (fun y hy => by
        change -y j ≤ -(o j+(z j:ℝ)*δ j)
        exact neg_le_neg ((hb hy j).1)) hx
    change -x j < -(o j+(z j:ℝ)*δ j) at h
    linarith
  · exact linear_strict_of_mem_interior_le (EuclideanSpace.proj j)
      (EuclideanSpace.basisFun (Fin d) ℝ j) (by simp)
      (fun y hy => (hb hy j).2) hx

theorem cartesianKuhnSimplex_interior_strictAnti (o δ : Fin d → ℝ)
    (hδ : ∀ j, 0 < δ j) (z : Fin d → ℤ) (π : Equiv.Perm (Fin d))
    {x : SpatialCoordinates d}
    (hx : x ∈ interior (simplicialCell (cartesianKuhnSimplex o δ hδ z π).points)) :
    StrictAnti (fun k => (x (π k)-o (π k))/δ (π k)-(z (π k):ℝ)) := by
  intro k l hkl
  have hne : π k ≠ π l := fun he => (ne_of_lt hkl) (π.injective he)
  let f : SpatialCoordinates d →L[ℝ] ℝ :=
    (δ (π l))⁻¹ • EuclideanSpace.proj (π l) -
      (δ (π k))⁻¹ • EuclideanSpace.proj (π k)
  let c : ℝ := o (π l)/δ (π l)+(z (π l):ℝ)-
    (o (π k)/δ (π k)+(z (π k):ℝ))
  have hv : 0 < f (EuclideanSpace.basisFun (Fin d) ℝ (π l)) := by
    simp [f,hne,inv_pos.mpr (hδ (π l))]
  have hbound : ∀ y ∈ simplicialCell (cartesianKuhnSimplex o δ hδ z π).points,
      f y ≤ c := by
    intro y hy
    have ha := ((cartesianKuhnSimplex_mem_iff o δ hδ z π y).mp hy).2 hkl.le
    change (δ (π l))⁻¹*y (π l)-(δ (π k))⁻¹*y (π k) ≤ c
    dsimp [c]
    simp only [div_eq_mul_inv] at ha ⊢
    nlinarith
  have hs := linear_strict_of_mem_interior_le f _ hv hbound hx
  change (δ (π l))⁻¹*x (π l)-(δ (π k))⁻¹*x (π k) < c at hs
  dsimp [c] at hs
  simp only [div_eq_mul_inv] at hs ⊢
  nlinarith

theorem cartesianKuhnSimplex_common_interior_origin (o δ : Fin d → ℝ)
    (hδ : ∀ j, 0 < δ j) (z z' : Fin d → ℤ) (π π' : Equiv.Perm (Fin d))
    {x : SpatialCoordinates d}
    (hx : x ∈ interior (simplicialCell (cartesianKuhnSimplex o δ hδ z π).points))
    (hx' : x ∈ interior (simplicialCell (cartesianKuhnSimplex o δ hδ z' π').points)) :
    z=z' := by
  funext j
  have h := cartesianKuhnSimplex_interior_box o δ hδ z π hx j
  have h' := cartesianKuhnSimplex_interior_box o δ hδ z' π' hx' j
  by_contra he
  rcases lt_or_gt_of_ne he with hlt | hgt
  · have hi : z j+1 ≤ z' j := by omega
    have hr : (z j:ℝ)+1 ≤ (z' j:ℝ) := by exact_mod_cast hi
    have hm := mul_le_mul_of_nonneg_right hr (hδ j).le
    linarith
  · have hi : z' j+1 ≤ z j := by omega
    have hr : (z' j:ℝ)+1 ≤ (z j:ℝ) := by exact_mod_cast hi
    have hm := mul_le_mul_of_nonneg_right hr (hδ j).le
    linarith

theorem strictAnti_permutation_unique (f : Fin d → ℝ) (π π' : Equiv.Perm (Fin d))
    (hπ : StrictAnti (fun k => f (π k))) (hπ' : StrictAnti (fun k => f (π' k))) :
    π=π' := by
  have hm : StrictMono (fun k => π.symm (π' k)) := by
    intro i j hij
    by_contra hn
    have hh := hπ.antitone (le_of_not_gt hn)
    simp only [π.apply_symm_apply] at hh
    exact (not_le_of_gt (hπ' hij)) hh
  apply Equiv.ext
  intro k
  have he := congrArg π (hm.apply_eq (x := k))
  simpa only [π.apply_symm_apply] using he.symm

theorem cartesianKuhnSimplex_interiors_disjoint (o δ : Fin d → ℝ)
    (hδ : ∀ j, 0 < δ j) :
    Pairwise fun i j : (Fin d → ℤ) × Equiv.Perm (Fin d) =>
      Disjoint (interior (simplicialCell (cartesianKuhnSimplex o δ hδ i.1 i.2).points))
        (interior (simplicialCell (cartesianKuhnSimplex o δ hδ j.1 j.2).points)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hz := cartesianKuhnSimplex_common_interior_origin o δ hδ i.1 j.1 i.2 j.2 hxi hxj
  have hi := cartesianKuhnSimplex_interior_strictAnti o δ hδ i.1 i.2 hxi
  have hj := cartesianKuhnSimplex_interior_strictAnti o δ hδ j.1 j.2 hxj
  rw [← hz] at hj
  have hπ := strictAnti_permutation_unique
    (fun k => (x k-o k)/δ k-(i.1 k:ℝ)) i.2 j.2 hi hj
  exact hij (Prod.ext hz hπ)

theorem cartesianFiniteSimplex_interiors_disjoint (o δ : Fin d → ℝ)
    (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ) :
    Pairwise fun i j : CartesianCellIndex N =>
      Disjoint (interior (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points))
        (interior (simplicialCell (cartesianFiniteSimplex o δ hδ N j).points)) := by
  intro i j hij
  exact cartesianKuhnSimplex_interiors_disjoint o δ hδ
    (fun he => hij (cartesianCellLatticeIndex_injective N he))

theorem cartesianFiniteSimplex_ae_partition (o δ : Fin d → ℝ)
    (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ) :
    ∀ᵐ x ∂volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)),
      ∃ i : CartesianCellIndex N,
        x ∈ simplicialCell (cartesianFiniteSimplex o δ hδ N i).points ∧
        ∀ j, x ∈ simplicialCell (cartesianFiniteSimplex o δ hδ N j).points → j=i :=
  simplicialCells_ae_partition (fun i => (cartesianFiniteSimplex o δ hδ N i).points) _
    (cartesianFiniteSimplex_cover o δ hδ N)
    (cartesianFiniteSimplex_interiors_disjoint o δ hδ N)
    (openCoordinateBox_isOpen _ _).measurableSet

end Carleman
