module

public import Carleman.Spatial.AffineChangeVolume
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Genuine barycentric superlevel sets and their Lebesgue volumes. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} (T : Affine.Simplex ℝ (SpatialCoordinates d) d)

theorem mem_simplexCell_iff_barycentric {x : SpatialCoordinates d} :
    x ∈ simplicialCell T.points ↔ ∀ i, 0 ≤ simplexBarycentric T i x := by
  have h := (simplexAffineBasis T).convexHull_eq_nonneg_coord
  change simplicialCell T.points = _ at h
  rw [h]
  rfl

theorem simplexBarycentric_homothety (i j : Fin (d+1)) (r : ℝ) (x : SpatialCoordinates d) :
    simplexBarycentric T j (AffineMap.homothety (T.points i) r x) =
      r*simplexBarycentric T j x+(1-r)*(if j=i then 1 else 0) := by
  rw [AffineMap.homothety_apply,AffineMap.map_vadd,map_smul,AffineMap.linear_apply_vsub]
  simp only [vsub_eq_sub,vadd_eq_add,smul_eq_mul,simplexBarycentric_vertex]
  ring

theorem simplexBarycentric_superlevel_image (i : Fin (d+1)) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) :
    AffineMap.homothety (T.points i) (1-t) '' simplicialCell T.points =
      simplicialCell T.points ∩ {x | t ≤ simplexBarycentric T i x} := by
  have hr : 0 < 1-t := sub_pos.mpr ht1
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    constructor
    · apply (mem_simplexCell_iff_barycentric T).mpr
      intro j
      rw [simplexBarycentric_homothety]
      have hj := simplexBarycentric_nonneg T hy j
      split_ifs <;> nlinarith [mul_nonneg hr.le hj]
    · change t ≤ _
      rw [simplexBarycentric_homothety,ite_eq_left rfl]
      nlinarith [mul_nonneg hr.le (simplexBarycentric_nonneg T hy i)]
  · rintro ⟨hx,hxt⟩
    refine ⟨AffineMap.homothety (T.points i) (1-t)⁻¹ x,?_,?_⟩
    · apply (mem_simplexCell_iff_barycentric T).mpr
      intro j
      rw [simplexBarycentric_homothety]
      by_cases hj : j=i
      · subst j
        rw [ite_eq_left rfl,mul_one]
        have he : (1-t)⁻¹*simplexBarycentric T i x+(1-(1-t)⁻¹) =
            (simplexBarycentric T i x-t)/(1-t) := by field_simp; ring
        rw [he]
        exact div_nonneg (sub_nonneg.mpr hxt) hr.le
      · rw [ite_eq_right hj,mul_zero,add_zero]
        exact mul_nonneg (inv_nonneg.mpr hr.le) (simplexBarycentric_nonneg T hx j)
    · rw [← AffineMap.homothety_mul_apply,mul_inv_cancel₀ hr.ne',AffineMap.homothety_one]
      rfl

theorem simplexBarycentric_superlevel_volume (i : Fin (d+1)) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) :
    volume (simplicialCell T.points ∩ {x | t ≤ simplexBarycentric T i x}) =
      ENNReal.ofReal ((1-t)^d)*volume (simplicialCell T.points) := by
  rw [← simplexBarycentric_superlevel_image T i ht ht1,Measure.addHaar_image_homothety]
  simp only [SpatialCoordinates,finrank_euclideanSpace,Fintype.card_fin,abs_of_nonneg (pow_nonneg (sub_nonneg.mpr ht1.le) d)]

theorem simplexBarycentric_superlevel_real (i : Fin (d+1)) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) :
    (volume.restrict (simplicialCell T.points)).real {x | t ≤ simplexBarycentric T i x} =
      (1-t)^d*volume.real (simplicialCell T.points) := by
  rw [Measure.real_def,Measure.restrict_apply
    (measurableSet_le measurable_const (simplexBarycentric T i).continuous_of_finiteDimensional.measurable),
    inter_comm,simplexBarycentric_superlevel_volume T i ht ht1,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg (sub_nonneg.mpr ht1.le) d)]
  rfl

theorem simplexBarycentric_le_one (i : Fin (d+1)) {x : SpatialCoordinates d}
    (hx : x ∈ simplicialCell T.points) : simplexBarycentric T i x ≤ 1 := by
  rw [← simplexBarycentric_sum T x]
  exact Finset.single_le_sum (fun j _ => simplexBarycentric_nonneg T hx j) (Finset.mem_univ i)

theorem integral_simplexBarycentric (i : Fin (d+1)) :
    (∫ x in simplicialCell T.points, simplexBarycentric T i x) =
      volume.real (simplicialCell T.points)/(d+1:ℝ) := by
  have hint : Integrable (simplexBarycentric T i) (volume.restrict (simplicialCell T.points)) :=
    (simplexBarycentric T i).continuous_of_finiteDimensional.continuousOn.integrableOn_compact (simplicialCell_compact _)
  have hnonneg : 0 ≤ᵐ[volume.restrict (simplicialCell T.points)] simplexBarycentric T i := by
    filter_upwards [ae_restrict_mem (simplicialCell_measurable T.points)] with x hx
    exact simplexBarycentric_nonneg T hx i
  have hle : simplexBarycentric T i ≤ᵐ[volume.restrict (simplicialCell T.points)] (fun _ => 1) := by
    filter_upwards [ae_restrict_mem (simplicialCell_measurable T.points)] with x hx
    exact simplexBarycentric_le_one T i hx
  rw [hint.integral_eq_integral_Ioc_meas_le hnonneg hle]
  have he : (∫ t in Set.Ioc (0:ℝ) 1,
      (volume.restrict (simplicialCell T.points)).real {x | t ≤ simplexBarycentric T i x}) =
      ∫ t in Set.Ioc (0:ℝ) 1, (1-t)^d*volume.real (simplicialCell T.points) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (Measure.ae_ne (volume : Measure ℝ) 1).filter_mono ae_restrict_le] with t ht hne
    exact simplexBarycentric_superlevel_real T i ht.1.le (lt_of_le_of_ne ht.2 hne)
  rw [he,integral_mul_const,← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^d) 1]
  norm_num only [sub_self,sub_zero]
  rw [integral_pow]
  simp only [one_pow,zero_pow (Nat.succ_ne_zero d),sub_zero]
  ring

end Carleman
