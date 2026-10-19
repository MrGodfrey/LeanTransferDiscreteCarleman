module

public import Carleman.Geometry.KuhnBarycentricCoordinates
public import Mathlib.Data.Fin.Tuple.Sort

/-! The reference Kuhn cell is exactly the unit cube sector with decreasing
coordinates; every physical grid box is covered by its permutation cells. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

def kuhnOrderedCube (d : ℕ) : Set (SpatialCoordinates d) :=
  {x | (∀ j, 0 ≤ x j ∧ x j ≤ 1) ∧ Antitone (fun j => x j)}

theorem kuhnOrderedCube_convex (d : ℕ) : Convex ℝ (kuhnOrderedCube d) := by
  intro x hx y hy a b ha hb hab
  refine ⟨closedCoordinateBox_convex (fun _ => 0) (fun _ => 1) hx.1 hy.1 ha hb hab,?_⟩
  intro i j hij
  change a*x j+b*y j ≤ a*x i+b*y i
  exact add_le_add (mul_le_mul_of_nonneg_left (hx.2 hij) ha)
    (mul_le_mul_of_nonneg_left (hy.2 hij) hb)

theorem kuhnReferenceSimplex_cell_eq_ordered :
    simplicialCell (kuhnReferenceSimplex d).points=kuhnOrderedCube d := by
  apply Subset.antisymm
  · apply convexHull_min ?_ (kuhnOrderedCube_convex d)
    rintro x ⟨k,rfl⟩
    constructor
    · intro j
      rw [kuhnReferenceSimplex_points]
      split_ifs <;> norm_num
    · intro i j hij
      change (kuhnReferenceSimplex d).points k j ≤ (kuhnReferenceSimplex d).points k i
      rw [kuhnReferenceSimplex_points,kuhnReferenceSimplex_points]
      have hij' : i.val ≤ j.val := hij
      split_ifs <;> norm_num
      omega
  · intro x hx
    exact kuhnReferenceSimplex_mem_of_ordered x hx.1 hx.2

def cartesianKuhnChart (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) :
    SpatialCoordinates d ≃ᵃ[ℝ] SpatialCoordinates d :=
  affineChangeEquiv ((coordinatePermutation π).trans (coordinateDilation δ hδ))
    (WithLp.toLp 2 (fun j => o j+(z j:ℝ)*δ j))

theorem cartesianKuhnChart_apply (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) (x : SpatialCoordinates d) (j : Fin d) :
    cartesianKuhnChart o δ hδ z π x j=o j+((z j:ℝ)+x (π.symm j))*δ j := by
  rw [cartesianKuhnChart,affineChangeEquiv_apply,affineChange_apply]
  change δ j*x (π.symm j)+(o j+(z j:ℝ)*δ j)=_
  ring

theorem cartesianKuhnChart_symm_apply (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) (x : SpatialCoordinates d) (j : Fin d) :
    (cartesianKuhnChart o δ hδ z π).symm x j=
      (x (π j)-o (π j))/δ (π j)-(z (π j):ℝ) := by
  have he := congrArg (fun y : SpatialCoordinates d => y (π j))
    ((cartesianKuhnChart o δ hδ z π).apply_symm_apply x)
  rw [cartesianKuhnChart_apply,π.symm_apply_apply] at he
  apply (eq_sub_iff_add_eq).mpr
  apply (eq_div_iff (hδ (π j)).ne').mpr
  nlinarith

theorem cartesianKuhnSimplex_cell_eq_chart (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) :
    simplicialCell (cartesianKuhnSimplex o δ hδ z π).points =
      cartesianKuhnChart o δ hδ z π '' kuhnOrderedCube d := by
  rw [cartesianKuhnSimplex,affineSimplex_cell,kuhnReferenceSimplex_cell_eq_ordered]
  congr 1
  funext x
  exact (affineChangeEquiv_apply _ _ x).symm

theorem cartesianKuhnSimplex_mem_iff (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) (x : SpatialCoordinates d) :
    x ∈ simplicialCell (cartesianKuhnSimplex o δ hδ z π).points ↔
      (∀ j, 0 ≤ (x j-o j)/δ j-(z j:ℝ) ∧ (x j-o j)/δ j-(z j:ℝ) ≤ 1) ∧
      Antitone (fun k => (x (π k)-o (π k))/δ (π k)-(z (π k):ℝ)) := by
  rw [cartesianKuhnSimplex_cell_eq_chart]
  have he : x ∈ cartesianKuhnChart o δ hδ z π '' kuhnOrderedCube d ↔
      (cartesianKuhnChart o δ hδ z π).symm x ∈ kuhnOrderedCube d := by
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa only [AffineEquiv.symm_apply_apply] using hy
    · intro hx
      exact ⟨(cartesianKuhnChart o δ hδ z π).symm x,hx,AffineEquiv.apply_symm_apply _ _⟩
  rw [he]
  change (∀ j, 0 ≤ (cartesianKuhnChart o δ hδ z π).symm x j ∧
    (cartesianKuhnChart o δ hδ z π).symm x j ≤ 1) ∧
    Antitone (fun j => (cartesianKuhnChart o δ hδ z π).symm x j) ↔ _
  simp_rw [cartesianKuhnChart_symm_apply]
  apply and_congr ?_ Iff.rfl
  constructor
  · intro h j
    simpa only [π.apply_symm_apply] using h (π.symm j)
  · intro h j
    exact h (π j)

theorem cartesianKuhnSimplex_cover_box (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) :
    closedCoordinateBox (fun j => o j+(z j:ℝ)*δ j) (fun j => o j+((z j:ℝ)+1)*δ j) ⊆
      ⋃ π : Equiv.Perm (Fin d), simplicialCell (cartesianKuhnSimplex o δ hδ z π).points := by
  intro x hx
  let y : Fin d → ℝ := fun j => (x j-o j)/δ j-(z j:ℝ)
  let π := Tuple.sort (α := OrderDual ℝ) y
  apply mem_iUnion.mpr
  refine ⟨π,(cartesianKuhnSimplex_mem_iff o δ hδ z π x).mpr ⟨?_,?_⟩⟩
  · intro j
    have hlo : (z j:ℝ) ≤ (x j-o j)/δ j := (le_div_iff₀ (hδ j)).mpr (by linarith [(hx j).1])
    have hup : (x j-o j)/δ j ≤ (z j:ℝ)+1 := (div_le_iff₀ (hδ j)).mpr (by linarith [(hx j).2])
    constructor <;> linarith
  · exact Tuple.monotone_sort (α := OrderDual ℝ) y

end Carleman
