module

public import Carleman.Geometry.KuhnOrderedCell
public import Carleman.Geometry.KuhnVertexStars

/-! The finite Kuhn family on an actual rectangular grid covers the whole
open box. Its grid and permutation indices are concrete and injective. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

abbrev CartesianCellIndex (N : Fin d → ℕ) := (∀ j, Fin (N j)) × Equiv.Perm (Fin d)

def cartesianCellLatticeIndex (N : Fin d → ℕ) (i : CartesianCellIndex N) :
    (Fin d → ℤ) × Equiv.Perm (Fin d) := ((fun j => (i.1 j).val),i.2)

theorem cartesianCellLatticeIndex_injective (N : Fin d → ℕ) :
    Function.Injective (cartesianCellLatticeIndex N) := by
  intro i k he
  apply Prod.ext
  · funext j
    apply Fin.ext
    have hj := congrArg (fun p : (Fin d → ℤ) × Equiv.Perm (Fin d) => p.1 j) he
    change ((i.1 j).val:ℤ)=((k.1 j).val:ℤ) at hj
    exact_mod_cast hj
  · exact congrArg (fun p : (Fin d → ℤ) × Equiv.Perm (Fin d) => p.2) he

theorem cartesianCellIndex_card (N : Fin d → ℕ) :
    Fintype.card (CartesianCellIndex N)=(∏ j, N j)*d.factorial := by
  simp [CartesianCellIndex,Fintype.card_perm]

def cartesianFiniteSimplex (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (i : CartesianCellIndex N) : Affine.Simplex ℝ (SpatialCoordinates d) d :=
  cartesianKuhnSimplex o δ hδ (cartesianCellLatticeIndex N i).1 i.2

theorem cartesianFiniteSimplex_cover (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) :
    openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j) ⊆
      ⋃ i : CartesianCellIndex N, simplicialCell (cartesianFiniteSimplex o δ hδ N i).points := by
  intro x hx
  let q : Fin d → ℝ := fun j => (x j-o j)/δ j
  have hq0 (j : Fin d) : 0 ≤ q j := div_nonneg (sub_nonneg.mpr (hx j).1.le) (hδ j).le
  have hqN (j : Fin d) : q j < N j := (div_lt_iff₀ (hδ j)).mpr (by linarith [(hx j).2])
  let a : ∀ j, Fin (N j) := fun j => ⟨Nat.floor (q j),(Nat.floor_lt (hq0 j)).mpr (hqN j)⟩
  let z : Fin d → ℤ := fun j => (a j).val
  have hb : x ∈ closedCoordinateBox (fun j => o j+(z j:ℝ)*δ j)
      (fun j => o j+((z j:ℝ)+1)*δ j) := by
    intro j
    have hl := (le_div_iff₀ (hδ j)).mp (Nat.floor_le (hq0 j))
    have hu := (div_lt_iff₀ (hδ j)).mp (Nat.lt_floor_add_one (q j))
    change o j+((Nat.floor (q j):ℕ):ℝ)*δ j ≤ x j ∧
      x j ≤ o j+(((Nat.floor (q j):ℕ):ℝ)+1)*δ j
    constructor <;> linarith
  obtain ⟨π,hπ⟩ := mem_iUnion.mp (cartesianKuhnSimplex_cover_box o δ hδ z hb)
  exact mem_iUnion.mpr ⟨⟨a,π⟩,hπ⟩

theorem cartesianFiniteSimplex_ae_cover (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) :
    ∀ᵐ x ∂volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)),
      ∃ i : CartesianCellIndex N, x ∈ simplicialCell (cartesianFiniteSimplex o δ hδ N i).points := by
  filter_upwards [ae_restrict_mem (openCoordinateBox_isOpen _ _).measurableSet] with x hx
  exact mem_iUnion.mp (cartesianFiniteSimplex_cover o δ hδ N hx)

theorem cartesianFiniteStar_multiplicity_le (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (x : SpatialCoordinates d) :
    finiteCoverMultiplicity (fun i : CartesianCellIndex N =>
      cartesianKuhnStarPatch o δ hδ (cartesianCellLatticeIndex N i).1 i.2) x ≤ 5^d*d.factorial :=
  cartesianKuhnStarPatch_multiplicity_le o δ hδ (cartesianCellLatticeIndex N)
    (cartesianCellLatticeIndex_injective N) x

end Carleman
