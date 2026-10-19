module

public import Carleman.Geometry.CoordinateBoxChart
public import Carleman.Spatial.L2FiniteOverlap
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Perm

/-! Actual rectangular patches on an anisotropic Cartesian lattice have
uniform finite overlap, independently of the mesh spacing and extent. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

def cartesianPatch (o δ : Fin d → ℝ) (r : ℕ) (z : Fin d → ℤ) :
    Set (SpatialCoordinates d) :=
  openCoordinateBox (fun j => o j+((z j:ℝ)-r)*δ j)
    (fun j => o j+((z j:ℝ)+r+1)*δ j)

theorem cartesianPatch_isOpen (o δ : Fin d → ℝ) (r : ℕ) (z : Fin d → ℤ) :
    IsOpen (cartesianPatch o δ r z) := openCoordinateBox_isOpen _ _

theorem cartesianPatch_index_bound (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (r : ℕ) (z : Fin d → ℤ) {x : SpatialCoordinates d}
    (hx : x ∈ cartesianPatch o δ r z) (j : Fin d) :
    z j ∈ Finset.Icc (⌊(x j-o j)/δ j⌋-(r:ℤ)) (⌊(x j-o j)/δ j⌋+(r:ℤ)) := by
  have hl : (z j:ℝ)-r < (x j-o j)/δ j :=
    (lt_div_iff₀ (hδ j)).mpr (by linarith [(hx j).1])
  have hu : (x j-o j)/δ j < (z j:ℝ)+r+1 :=
    (div_lt_iff₀ (hδ j)).mpr (by linarith [(hx j).2])
  have hfl := Int.floor_le ((x j-o j)/δ j)
  have hfu := Int.lt_floor_add_one ((x j-o j)/δ j)
  have hi₁ : ⌊(x j-o j)/δ j⌋ < z j+(r:ℤ)+1 := by
    apply (Int.cast_lt (R := ℝ)).mp
    push_cast
    exact hfl.trans_lt hu
  have hi₂ : z j-(r:ℤ) < ⌊(x j-o j)/δ j⌋+1 := by
    apply (Int.cast_lt (R := ℝ)).mp
    push_cast
    exact hl.trans hfu
  exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩

theorem cartesianPatch_window_card (r : ℕ) (k : Fin d → ℤ) :
    (Fintype.piFinset (fun j => Finset.Icc (k j-(r:ℤ)) (k j+(r:ℤ)))).card = (2*r+1)^d := by
  have hc (j : Fin d) : (Finset.Icc (k j-(r:ℤ)) (k j+(r:ℤ))).card=2*r+1 := by
    rw [Int.card_Icc]
    omega
  simp only [Fintype.card_piFinset,hc,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

/-- An injective cell-and-label index permits a fixed finite number of
simplex labels in each lattice cell. Patches may be clipped to the domain. -/
theorem cartesianPatch_multiplicity_le {ι L : Type*} [Fintype ι] [Fintype L]
    (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (r : ℕ)
    (index : ι → (Fin d → ℤ) × L) (hinj : Function.Injective index)
    (A : ι → Set (SpatialCoordinates d))
    (hA : ∀ i, A i ⊆ cartesianPatch o δ r (index i).1) (x : SpatialCoordinates d) :
    finiteCoverMultiplicity A x ≤ (2*r+1)^d*Fintype.card L := by
  classical
  let window := Fintype.piFinset
    (fun j => Finset.Icc (⌊(x j-o j)/δ j⌋-(r:ℤ)) (⌊(x j-o j)/δ j⌋+(r:ℤ)))
  have hb := Finset.card_le_card_of_injOn index
    (s := Finset.univ.filter (fun i => x ∈ A i))
    (t := window ×ˢ (Finset.univ : Finset L))
    (by
      intro i hi
      apply Finset.mem_product.mpr
      refine ⟨Fintype.mem_piFinset.mpr (fun j => ?_),Finset.mem_univ _⟩
      exact cartesianPatch_index_bound o δ hδ r (index i).1
        (hA i (Finset.mem_filter.mp hi).2) j)
    (fun _ _ _ _ he => hinj he)
  simpa only [finiteCoverMultiplicity,Finset.card_product,Finset.card_univ,
    window,cartesianPatch_window_card] using hb

theorem cartesianPatch_permutation_multiplicity_le {ι : Type*} [Fintype ι]
    (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (r : ℕ)
    (index : ι → (Fin d → ℤ) × Equiv.Perm (Fin d)) (hinj : Function.Injective index)
    (A : ι → Set (SpatialCoordinates d))
    (hA : ∀ i, A i ⊆ cartesianPatch o δ r (index i).1) (x : SpatialCoordinates d) :
    finiteCoverMultiplicity A x ≤ (2*r+1)^d*d.factorial := by
  simpa only [Fintype.card_perm,Fintype.card_fin] using
    cartesianPatch_multiplicity_le o δ hδ r index hinj A hA x

end Carleman
