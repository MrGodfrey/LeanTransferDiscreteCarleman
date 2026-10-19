module

public import Carleman.Geometry.KuhnReferenceSimplex
public import Carleman.Geometry.CoordinateBoxScaling
public import Carleman.Geometry.CartesianPatchOverlap

/-! Every physical Kuhn simplex is the actual affine image of the prefix
simplex under coordinate permutation, positive grid scaling and translation. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

def coordinatePermutation (π : Equiv.Perm (Fin d)) :
    SpatialCoordinates d ≃L[ℝ] SpatialCoordinates d :=
  (show SpatialCoordinates d ≃ₗ[ℝ] SpatialCoordinates d from
    { toFun := fun x => WithLp.toLp 2 (fun j => x (π.symm j))
      invFun := fun x => WithLp.toLp 2 (fun j => x (π j))
      left_inv := fun x => by apply PiLp.ext; intro j; exact congrArg x (π.symm_apply_apply j)
      right_inv := fun x => by apply PiLp.ext; intro j; exact congrArg x (π.apply_symm_apply j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toContinuousLinearEquiv

theorem coordinatePermutation_apply (π : Equiv.Perm (Fin d)) (x : SpatialCoordinates d) (j : Fin d) :
    coordinatePermutation π x j=x (π.symm j) := rfl

def cartesianKuhnSimplex (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) : Affine.Simplex ℝ (SpatialCoordinates d) d :=
  affineSimplex (kuhnReferenceSimplex d) ((coordinatePermutation π).trans (coordinateDilation δ hδ))
    (WithLp.toLp 2 (fun j => o j+(z j:ℝ)*δ j))

theorem cartesianKuhnSimplex_points (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) (k : Fin (d+1)) (j : Fin d) :
    (cartesianKuhnSimplex o δ hδ z π).points k j =
      o j+((z j:ℝ)+(if (π.symm j).val < k.val then 1 else 0))*δ j := by
  rw [cartesianKuhnSimplex,affineSimplex_points,affineChange_apply]
  change δ j*(coordinatePermutation π ((kuhnReferenceSimplex d).points k) j)+
    (o j+(z j:ℝ)*δ j) = _
  rw [coordinatePermutation_apply,kuhnReferenceSimplex_points]
  ring

theorem cartesianKuhnSimplex_points_step (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) (k : Fin d) :
    (cartesianKuhnSimplex o δ hδ z π).points k.succ-
      (cartesianKuhnSimplex o δ hδ z π).points k.castSucc =
      δ (π k) • EuclideanSpace.basisFun (Fin d) ℝ (π k) := by
  apply PiLp.ext
  intro j
  change (cartesianKuhnSimplex o δ hδ z π).points k.succ j-
    (cartesianKuhnSimplex o δ hδ z π).points k.castSucc j =
    δ (π k)*(EuclideanSpace.basisFun (Fin d) ℝ (π k) j)
  rw [cartesianKuhnSimplex_points,cartesianKuhnSimplex_points]
  by_cases he : j=π k
  · subst j
    simp only [Equiv.symm_apply_apply,Fin.val_succ,Fin.val_castSucc,Nat.lt_succ_self,
      lt_self_iff_false,ite_true,ite_false,add_zero,EuclideanSpace.basisFun_apply]
    simp
    ring
  · have hn : π.symm j ≠ k := fun ht => he (by rw [← ht,π.apply_symm_apply])
    have hc : π.symm j ≤ k ↔ π.symm j < k :=
      ⟨fun h => lt_of_le_of_ne h hn,le_of_lt⟩
    simp [EuclideanSpace.basisFun_apply,he,hc]

theorem closedCoordinateBox_convex (a b : Fin d → ℝ) : Convex ℝ (closedCoordinateBox a b) := by
  have he : closedCoordinateBox a b = ⋂ j, (EuclideanSpace.proj j) ⁻¹' Icc (a j) (b j) := by
    ext x
    simp only [closedCoordinateBox,mem_ofPred_eq,mem_iInter,mem_preimage,mem_Icc]
    rfl
  rw [he]
  exact convex_iInter fun j => (convex_Icc (a j) (b j)).linear_preimage (EuclideanSpace.proj j).toLinearMap

theorem cartesianKuhnSimplex_cell_subset_box (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) :
    simplicialCell (cartesianKuhnSimplex o δ hδ z π).points ⊆
      closedCoordinateBox (fun j => o j+(z j:ℝ)*δ j) (fun j => o j+((z j:ℝ)+1)*δ j) := by
  apply convexHull_min ?_ (closedCoordinateBox_convex _ _)
  rintro x ⟨k,rfl⟩ j
  rw [cartesianKuhnSimplex_points]
  split_ifs <;> constructor <;> linarith [hδ j]

theorem cartesianKuhnSimplex_cell_subset_patch (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) :
    simplicialCell (cartesianKuhnSimplex o δ hδ z π).points ⊆ cartesianPatch o δ 1 z := by
  intro x hx j
  have hb := cartesianKuhnSimplex_cell_subset_box o δ hδ z π hx j
  change o j+((z j:ℝ)-(1:ℕ))*δ j < x j ∧ x j < o j+((z j:ℝ)+(1:ℕ)+1)*δ j
  constructor <;> norm_num at * <;> linarith [hδ j]

end Carleman
