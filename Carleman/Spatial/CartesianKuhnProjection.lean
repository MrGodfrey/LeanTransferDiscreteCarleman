module

public import Carleman.Spatial.CartesianKuhnMomentBounds
public import Carleman.Spatial.CartesianKuhnLpNorm

/-! The actual moment reconstruction Q_h=R_h J_h is local and L²-stable
on any patch containing the supports of the active interior-node hats. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

def cartesianKuhnProjection (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ)
    (u : Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))) :
    SpatialCoordinates d → ℝ :=
  cartesianKuhnReconstruction o δ hδ N (cartesianKuhnMoment o δ hδ N u)

def cartesianKuhnProjectionLp (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ)
    (u : Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))) :
    Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))) :=
  cartesianKuhnReconstructionLp o δ hδ N (cartesianKuhnMoment o δ hδ N u)

theorem cartesianKuhn_cell_volume_le (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (i : CartesianCellIndex N) :
    volume.real (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points) ≤ ∏ j, δ j := by
  change volume.real (simplicialCell (cartesianKuhnSimplex o δ hδ _ i.2).points) ≤ _
  rw [cartesianKuhnSimplex_volume_translation,← cartesianKuhnSimplex_sum_permutation_volume o δ hδ]
  exact Finset.single_le_sum
    (f := fun π => volume.real (simplicialCell (cartesianKuhnSimplex o δ hδ 0 π).points))
    (fun _ _ => measureReal_nonneg) (Finset.mem_univ i.2)

theorem cartesianKuhnProjection_local_sq_bound (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ)
    (u : Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))))
    (i : CartesianCellIndex N) (B : Set (SpatialCoordinates d))
    (hBS : B ⊆ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))
    (hs : ∀ a : CartesianInteriorIndex N,
      cartesianInteriorPoint o δ N a ∈ Set.range (cartesianFiniteSimplex o δ hδ N i).points →
      Function.support (cartesianKuhnHat o δ hδ N (cartesianInteriorLatticeIndex N a)) ⊆ B) :
    (∫ x in simplicialCell (cartesianFiniteSimplex o δ hδ N i).points,
      (cartesianKuhnProjection o δ hδ N u x)^2) ≤ ∫ x in B, (u x)^2 := by
  classical
  let T := cartesianFiniteSimplex o δ hδ N i
  let c : Fin (d+1) → ℝ := fun k => cartesianInteriorData o δ N (cartesianKuhnMoment o δ hδ N u) (T.points k)
  let I := ∫ x in B, (u x)^2
  let ω := ∏ j, δ j
  have hω : 0 < ω := Finset.prod_pos (fun j _ => hδ j)
  have hI : 0 ≤ I := integral_nonneg (fun x => sq_nonneg (u x))
  have hk (k : Fin (d+1)) : ω*(c k)^2 ≤ I := by
    by_cases hn : ∃ a : CartesianInteriorIndex N, cartesianInteriorPoint o δ N a=T.points k
    · obtain ⟨a,ha⟩ := hn
      dsimp only [c]
      rw [← ha,cartesianInteriorData_at_node o δ hδ N]
      exact cartesianKuhnMoment_local_sq_bound o δ hδ N u a B hBS (hs a ⟨k,ha.symm⟩)
    · have hz : c k=0 := by
        apply Finset.sum_eq_zero
        intro a _
        exact ite_eq_right (fun ha => hn ⟨a,ha⟩)
      rw [hz,sq,zero_mul,mul_zero]
      exact hI
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin (d+1)))) => hk k)
  simp only [← Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] at hsum
  have hlocal := (cartesianKuhnReconstruction_cell_sq_bounds o δ hδ N
    (cartesianKuhnMoment o δ hδ N u) i).2
  have hV := cartesianKuhn_cell_volume_le o δ hδ N i
  have hm : 0 ≤ volume.real (simplicialCell T.points)/(d+1:ℝ) := by positivity
  have hd : (d+1:ℝ) ≠ 0 := by positivity
  apply (mul_le_mul_iff_right₀ hω).mp
  calc
    _ ≤ ω*((volume.real (simplicialCell T.points)/(d+1:ℝ))*∑ k, (c k)^2) :=
      mul_le_mul_of_nonneg_left hlocal hω.le
    _ = (volume.real (simplicialCell T.points)/(d+1:ℝ))*(ω*∑ k, (c k)^2) := by ring
    _ ≤ (volume.real (simplicialCell T.points)/(d+1:ℝ))*((d+1:ℝ)*I) :=
      mul_le_mul_of_nonneg_left hsum hm
    _ = volume.real (simplicialCell T.points)*I := by field_simp
    _ ≤ ω*I := mul_le_mul_of_nonneg_right hV hI

theorem cartesianKuhnProjection_local_congr (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ)
    (u v : Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))))
    (i : CartesianCellIndex N) (B : Set (SpatialCoordinates d))
    (hBS : B ⊆ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))
    (hs : ∀ a : CartesianInteriorIndex N,
      cartesianInteriorPoint o δ N a ∈ Set.range (cartesianFiniteSimplex o δ hδ N i).points →
      Function.support (cartesianKuhnHat o δ hδ N (cartesianInteriorLatticeIndex N a)) ⊆ B)
    (he : u =ᵐ[volume.restrict B] v) {x : SpatialCoordinates d}
    (hx : x ∈ simplicialCell (cartesianFiniteSimplex o δ hδ N i).points) :
    cartesianKuhnProjection o δ hδ N u x=cartesianKuhnProjection o δ hδ N v x := by
  classical
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : cartesianInteriorPoint o δ N a ∈ Set.range (cartesianFiniteSimplex o δ hδ N i).points
  · rw [cartesianKuhnMoment_local_congr o δ hδ N u v a B hBS (hs a ha) he]
  · rw [cartesianKuhnHat_zero_on_nonincidentCell o δ hδ N _ i ha hx,mul_zero,mul_zero]

theorem cartesianKuhnProjection_local_norm_bound (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ)
    (u : Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))))
    (i : CartesianCellIndex N) (B : Set (SpatialCoordinates d))
    (hBS : B ⊆ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))
    (hs : ∀ a : CartesianInteriorIndex N,
      cartesianInteriorPoint o δ N a ∈ Set.range (cartesianFiniteSimplex o δ hδ N i).points →
      Function.support (cartesianKuhnHat o δ hδ N (cartesianInteriorLatticeIndex N a)) ⊆ B) :
    bochnerL2Norm (volume.restrict (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points))
      (cartesianKuhnProjection o δ hδ N u) ≤ bochnerL2Norm (volume.restrict B) u := by
  have hQ : MemLp (cartesianKuhnProjection o δ hδ N u) 2
      (volume.restrict (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)) :=
    (cartesianKuhnReconstruction_memLp o δ hδ N (cartesianKuhnMoment o δ hδ N u)).mono_measure Measure.restrict_le_self
  have hu := (Lp.memLp u).mono_measure (Measure.restrict_mono hBS le_rfl)
  apply (sq_le_sq₀ (bochnerL2Norm_nonneg _) (bochnerL2Norm_nonneg _)).mp
  rw [← integral_sq_eq_bochnerL2Norm_sq hQ,← integral_sq_eq_bochnerL2Norm_sq hu]
  exact cartesianKuhnProjection_local_sq_bound o δ hδ N u i B hBS hs

end Carleman
