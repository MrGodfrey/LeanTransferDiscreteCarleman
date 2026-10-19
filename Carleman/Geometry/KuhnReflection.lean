module

public import Carleman.Spatial.CartesianKuhnHatSupport
public import Carleman.Spatial.SimplexAffineRelabel
public import Mathlib.Data.Fin.Rev

/-! Reflection about an actual grid node sends every Kuhn cell to the
oppositely ordered Kuhn cell, with the vertices in reverse order. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

def kuhnReflectedOrigin (a z : Fin d → ℤ) : Fin d → ℤ := fun j => 2*a j-z j-1

def kuhnReflectedPermutation (π : Equiv.Perm (Fin d)) : Equiv.Perm (Fin d) :=
  Fin.revPerm.trans π

theorem kuhnVertexIndex_reflection (a z : Fin d → ℤ) (π : Equiv.Perm (Fin d))
    (k : Fin (d+1)) (j : Fin d) :
    kuhnVertexIndex (kuhnReflectedOrigin a z) (kuhnReflectedPermutation π) k.rev j=
      2*a j-kuhnVertexIndex z π k j := by
  have he : ((kuhnReflectedPermutation π).symm j).val < k.rev.val ↔
      ¬(π.symm j).val < k.val := by
    change (π.symm j).rev.val < k.rev.val ↔ ¬(π.symm j).val < k.val
    simp only [Fin.val_rev]
    have hj := (π.symm j).isLt
    have hk := k.isLt
    omega
  simp only [kuhnVertexIndex,kuhnReflectedOrigin,he]
  split_ifs <;> omega

theorem cartesianKuhnSimplex_reflection_vertex (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (a z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) (k : Fin (d+1)) :
    AffineEquiv.pointReflection ℝ (cartesianGridPoint o δ a)
      ((cartesianKuhnSimplex o δ hδ z π).points k)=
      (cartesianKuhnSimplex o δ hδ (kuhnReflectedOrigin a z) (kuhnReflectedPermutation π)).points k.rev := by
  rw [cartesianKuhnSimplex_points_eq_gridPoint,cartesianKuhnSimplex_points_eq_gridPoint,
    AffineEquiv.pointReflection_apply]
  apply PiLp.ext
  intro j
  change (o j+(a j:ℝ)*δ j)-(o j+(kuhnVertexIndex z π k j:ℝ)*δ j)+(o j+(a j:ℝ)*δ j)=
    o j+(kuhnVertexIndex (kuhnReflectedOrigin a z) (kuhnReflectedPermutation π) k.rev j:ℝ)*δ j
  rw [kuhnVertexIndex_reflection]
  push_cast
  ring

theorem cartesianKuhnSimplex_reflection_cell (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (a z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) :
    AffineEquiv.pointReflection ℝ (cartesianGridPoint o δ a) ''
      simplicialCell (cartesianKuhnSimplex o δ hδ z π).points =
      simplicialCell (cartesianKuhnSimplex o δ hδ
        (kuhnReflectedOrigin a z) (kuhnReflectedPermutation π)).points :=
  simplex_cell_affine_relabel _ _ _ Fin.revPerm
    (cartesianKuhnSimplex_reflection_vertex o δ hδ a z π)

theorem cartesianKuhn_incident_finite_index (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ)
    (ha : cartesianGridPoint o δ a ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d))
    (hvertex : cartesianGridPoint o δ a ∈ Set.range (cartesianKuhnSimplex o δ hδ z π).points) :
    ∃ i : CartesianCellIndex N, cartesianCellLatticeIndex N i=(z,π) := by
  obtain ⟨k,hk⟩ := hvertex
  have hidx (j : Fin d) : kuhnVertexIndex z π k j=a j := by
    have he := congrArg (cartesianGridCoordinate o δ j) hk
    rw [cartesianGridCoordinate_vertex,cartesianGridCoordinate_point o δ hδ] at he
    exact_mod_cast he
  have hz (j : Fin d) : 0 ≤ z j ∧ z j < (N j:ℤ) := by
    have hp : 0 < (a j:ℝ)*δ j := by have h := (ha j).1; change o j < o j+(a j:ℝ)*δ j at h; linarith
    have hr0 : 0 < (a j:ℝ) := (mul_pos_iff_of_pos_right (hδ j)).mp hp
    have hrN : (a j:ℝ) < (N j:ℝ) := by
      apply (mul_lt_mul_iff_left₀ (hδ j)).mp
      have h := (ha j).2
      change o j+(a j:ℝ)*δ j < o j+(N j:ℝ)*δ j at h
      linarith
    have h0 : 0 < a j := by exact_mod_cast hr0
    have hN : a j < (N j:ℤ) := by exact_mod_cast hrN
    have he := hidx j
    simp only [kuhnVertexIndex] at he
    split_ifs at he <;> omega
  let b : ∀ j, Fin (N j) := fun j => ⟨(z j).toNat,by have h := hz j; omega⟩
  refine ⟨⟨b,π⟩,?_⟩
  apply Prod.ext
  · funext j
    exact Int.toNat_of_nonneg (hz j).1
  · rfl

theorem cartesianFiniteSimplex_of_latticeIndex (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (i : CartesianCellIndex N) (z : Fin d → ℤ) (π : Equiv.Perm (Fin d))
    (he : cartesianCellLatticeIndex N i=(z,π)) :
    cartesianFiniteSimplex o δ hδ N i=cartesianKuhnSimplex o δ hδ z π := by
  change cartesianKuhnSimplex o δ hδ (cartesianCellLatticeIndex N i).1
    (cartesianCellLatticeIndex N i).2=_
  rw [he]

theorem cartesianFiniteSimplex_reflected_incident (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ)
    (ha : cartesianGridPoint o δ a ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))
    (i : CartesianCellIndex N)
    (hv : cartesianGridPoint o δ a ∈ Set.range (cartesianFiniteSimplex o δ hδ N i).points) :
    ∃ j : CartesianCellIndex N, ∀ k : Fin (d+1),
      AffineEquiv.pointReflection ℝ (cartesianGridPoint o δ a)
        ((cartesianFiniteSimplex o δ hδ N i).points k)=
        (cartesianFiniteSimplex o δ hδ N j).points k.rev := by
  let z := (cartesianCellLatticeIndex N i).1
  obtain ⟨k,hk⟩ := hv
  change (cartesianKuhnSimplex o δ hδ z i.2).points k=cartesianGridPoint o δ a at hk
  have hr := cartesianKuhnSimplex_reflection_vertex o δ hδ a z i.2 k
  rw [hk,AffineEquiv.pointReflection_self] at hr
  obtain ⟨j,hj⟩ := cartesianKuhn_incident_finite_index o δ hδ N a ha
    (kuhnReflectedOrigin a z) (kuhnReflectedPermutation i.2) ⟨k.rev,hr.symm⟩
  refine ⟨j,?_⟩
  intro l
  rw [cartesianFiniteSimplex_of_latticeIndex o δ hδ N j _ _ hj]
  exact cartesianKuhnSimplex_reflection_vertex o δ hδ a z i.2 l

end Carleman
