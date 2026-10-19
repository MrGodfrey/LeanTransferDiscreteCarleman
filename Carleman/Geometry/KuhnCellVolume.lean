module

public import Carleman.Geometry.KuhnReflection
public import Carleman.Spatial.SimplicialIntegrals
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Exact box volume and translation invariance of the actual Kuhn cells.
The sum of permutation-cell volumes is the volume of one grid box. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

theorem openCoordinateBox_volume_real (a b : Fin d → ℝ) (hab : ∀ j, a j ≤ b j) :
    volume.real (openCoordinateBox a b)=∏ j, (b j-a j) := by
  have hm := (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    (s := Set.pi Set.univ (fun j => Set.Ioo (a j) (b j)))
    ((MeasurableSet.univ_pi fun j => measurableSet_Ioo).nullMeasurableSet)
  have he : WithLp.ofLp ⁻¹' (Set.pi Set.univ (fun j => Set.Ioo (a j) (b j)))=
      openCoordinateBox a b := by
    ext x
    simp only [mem_preimage,mem_pi,mem_univ,true_implies,mem_Ioo,openCoordinateBox,mem_ofPred_eq]
  rw [he] at hm
  change (volume (openCoordinateBox a b)).toReal=_
  rw [hm,Real.volume_pi_Ioo_toReal hab]

theorem cartesianKuhnSimplex_translation_vertex (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) (k : Fin (d+1)) :
    affineChangeEquiv (ContinuousLinearEquiv.refl ℝ (SpatialCoordinates d))
      (WithLp.toLp 2 (fun j => (z j:ℝ)*δ j))
      ((cartesianKuhnSimplex o δ hδ 0 π).points k)=
      (cartesianKuhnSimplex o δ hδ z π).points k := by
  rw [affineChangeEquiv_apply,affineChange_apply]
  apply PiLp.ext
  intro j
  change (cartesianKuhnSimplex o δ hδ 0 π).points k j+(z j:ℝ)*δ j=_
  rw [cartesianKuhnSimplex_points,cartesianKuhnSimplex_points]
  simp only [Pi.zero_apply,Int.cast_zero,zero_add]
  ring

theorem cartesianKuhnSimplex_volume_translation (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) :
    volume.real (simplicialCell (cartesianKuhnSimplex o δ hδ z π).points)=
      volume.real (simplicialCell (cartesianKuhnSimplex o δ hδ 0 π).points) := by
  let b : SpatialCoordinates d := WithLp.toLp 2 (fun j => (z j:ℝ)*δ j)
  have he := simplex_cell_affine_relabel (cartesianKuhnSimplex o δ hδ 0 π)
    (cartesianKuhnSimplex o δ hδ z π)
    (affineChangeEquiv (ContinuousLinearEquiv.refl ℝ (SpatialCoordinates d)) b)
    (Equiv.refl _) (cartesianKuhnSimplex_translation_vertex o δ hδ z π)
  have hfun : (affineChangeEquiv (ContinuousLinearEquiv.refl ℝ (SpatialCoordinates d)) b :
      SpatialCoordinates d → SpatialCoordinates d)=(fun x => x+b) := by
    funext x
    rw [affineChangeEquiv_apply,affineChange_apply]
    rfl
  rw [hfun] at he
  have hm := (measurePreserving_add_right (volume : Measure (SpatialCoordinates d)) b).measure_preimage
    (simplicialCell_measurable (cartesianKuhnSimplex o δ hδ z π).points).nullMeasurableSet
  rw [← he,Set.preimage_image_eq _ (add_left_injective b),he] at hm
  exact congrArg ENNReal.toReal hm.symm

theorem cartesianKuhnSimplex_sum_permutation_volume (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) :
    (∑ π : Equiv.Perm (Fin d), volume.real (simplicialCell (cartesianKuhnSimplex o δ hδ 0 π).points))=
      ∏ j, δ j := by
  have h := (cartesianKuhnPartition o δ hδ (fun _ => 1)).integral_eq_sum_cells
    (openCoordinateBox_isOpen _ _) (openCoordinateBox_convex _ _) (fun _ => 1) (integrable_const 1)
  simp only [integral_const,smul_eq_mul,mul_one,Nat.cast_one,one_mul,Measure.real,
    Measure.restrict_apply_univ] at h
  change volume.real (openCoordinateBox o (fun j => o j+δ j))=
    ∑ i, volume.real ((cartesianKuhnPartition o δ hδ (fun _ => 1)).cell i) at h
  rw [openCoordinateBox_volume_real o (fun j => o j+δ j) (fun j => by linarith [hδ j])] at h
  simp only [add_sub_cancel_left] at h
  have hzero (b : ∀ _j : Fin d, Fin 1) : (fun j => ((b j).val:ℤ))=0 := by
    funext j
    have hb : b j=0 := Fin.eq_zero _
    simp only [hb,Fin.val_zero,Nat.cast_zero,Pi.zero_apply]
  simpa only [CartesianCellIndex,Fintype.sum_prod_type,cartesianKuhnPartition,
    SimplicialPartition.cell,cartesianFiniteSimplex,cartesianCellLatticeIndex,hzero,
    Finset.sum_const,Finset.card_univ,Fintype.card_pi,Fintype.card_fin,Finset.prod_const_one,
    Nat.cast_one,one_smul] using h.symm

end Carleman
