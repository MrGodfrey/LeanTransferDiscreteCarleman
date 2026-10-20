module

public import Carleman.Spatial.MollifiedConeTranslation
public import Carleman.Spatial.StrongMollifierLimit
public import Carleman.Spatial.WeakDirections
public import Carleman.Spatial.AffineWeakTransport
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter Metric
open scoped Topology Convolution
@[expose] public noncomputable section
namespace Carleman
variable {d : ℕ}

def spatialTranslationLp (z : SpatialCoordinates d) :
    Lp ℝ 2 (volume : Measure (SpatialCoordinates d)) →ₗᵢ[ℝ]
      Lp ℝ 2 (volume : Measure (SpatialCoordinates d)) :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x => x+z) (measurePreserving_add_right volume z)

theorem spatialTranslationLp_ae (z : SpatialCoordinates d)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    spatialTranslationLp z u =ᵐ[volume] (fun x => u (x+z)) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_add_right volume z)

theorem spatialTranslationLp_norm (z : SpatialCoordinates d)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) : ‖spatialTranslationLp z u‖=‖u‖ :=
  (spatialTranslationLp z).norm_map u

theorem spatialTranslationLp_zero (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    spatialTranslationLp 0 u=u := by
  apply Lp.ext
  filter_upwards [spatialTranslationLp_ae 0 u] with x hx
  simpa only [add_zero] using hx

theorem spatialTranslationLp_add (z w : SpatialCoordinates d)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    spatialTranslationLp z (spatialTranslationLp w u)=spatialTranslationLp (z+w) u := by
  change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ u)=Lp.compMeasurePreserving _ _ u
  rw [← Lp.compMeasurePreserving_comp_apply]
  congr 2
  funext x
  exact (add_assoc x z w)

theorem spatialTranslationLp_inner (z : SpatialCoordinates d)
    (u v : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    inner ℝ (spatialTranslationLp z u) v=inner ℝ u (spatialTranslationLp (-z) v) := by
  have h := (spatialTranslationLp z).inner_map_map u (spatialTranslationLp (-z) v)
  simpa only [spatialTranslationLp_add,add_neg_cancel,spatialTranslationLp_zero] using h

theorem mollified_full_translation_bound (z : SpatialCoordinates d) {t : ℝ} (ht : 0 ≤ t)
    {u v : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))}
    (hw : IsWeakSpatialDerivative volume univ z u v) (n : ℕ) :
    ‖spatialTranslationLp (t • z) (spatialMollificationLp n u)-spatialMollificationLp n u‖ ≤ t*‖v‖ := by
  let κ := spatialMollifier d n
  obtain ⟨ε,hε⟩ := κ.compact.isBounded.subset_closedBall (0 : SpatialCoordinates d)
  let p : InwardConePatch (univ : Set (SpatialCoordinates d)) :=
    { region := univ
      open_region := isOpen_univ
      direction := z
      height := t+1
      height_pos := by linarith
      inward := fun _ _ _ _ _ _ => subset_univ _ }
  have h := mollified_cone_translation_l2 p MeasurableSet.univ
    (fun x _ => by simpa only [p,inter_univ] using subset_univ (closedBall x ε))
    (by simp only [p,sub_self,norm_zero]; norm_num) ht (by dsimp [p]; linarith)
    hw κ hε (spatialMollifier_nonneg n) (spatialMollifier_integral n)
  simp only [Measure.restrict_univ] at h
  have hshift := (measurePreserving_add_right volume (t • z)).quasiMeasurePreserving.ae_eq_comp
    (spatialMollificationLp_ae n u)
  have hae : (spatialTranslationLp (t • z) (spatialMollificationLp n u)-spatialMollificationLp n u :
      Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) =ᵐ[volume]
      (fun x => (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) (x+t • z)-
        (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) x) := by
    filter_upwards [Lp.coeFn_sub (spatialTranslationLp (t • z) (spatialMollificationLp n u))
      (spatialMollificationLp n u),spatialTranslationLp_ae (t • z) (spatialMollificationLp n u),
      hshift,spatialMollificationLp_ae n u] with x h1 h2 h3 h4
    simp only [Function.comp_apply] at h3
    rw [h1,Pi.sub_apply,h2,h3,h4]
  rw [← bochnerL2Norm_coe,bochnerL2Norm_congr_ae hae]
  exact h.2

theorem IsWeakSpatialDerivative.translation_bound_nonneg
    {z : SpatialCoordinates d} {u v : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))}
    (hw : IsWeakSpatialDerivative volume univ z u v) {t : ℝ} (ht : 0 ≤ t) :
    ‖spatialTranslationLp (t • z) u-u‖ ≤ t*‖v‖ := by
  have hconv := (((spatialTranslationLp (t • z)).continuous.tendsto u).comp
    (spatialMollificationLp_tendsto u)).sub (spatialMollificationLp_tendsto u)
  exact le_of_tendsto hconv.norm (Eventually.of_forall (mollified_full_translation_bound z ht hw))

theorem IsWeakSpatialDerivative.translation_bound
    {z : SpatialCoordinates d} {u v : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))}
    (hw : IsWeakSpatialDerivative volume univ z u v) (t : ℝ) :
    ‖spatialTranslationLp (t • z) u-u‖ ≤ |t| *‖v‖ := by
  by_cases ht : 0 ≤ t
  · simpa only [abs_of_nonneg ht] using hw.translation_bound_nonneg ht
  · have ht' : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge ht)
    have hn : IsWeakSpatialDerivative volume univ (-z) u (-v) := by
      simpa only [neg_one_smul] using hw.direction_smul (-1)
    simpa only [neg_smul,smul_neg,neg_neg,norm_neg,abs_of_neg (lt_of_not_ge ht)] using
      hn.translation_bound_nonneg ht'

def spatialDifferenceQuotient (z : SpatialCoordinates d) (h : ℝ) :
    Lp ℝ 2 (volume : Measure (SpatialCoordinates d)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (SpatialCoordinates d)) :=
  h⁻¹ • ((spatialTranslationLp (h • z)).toContinuousLinearMap-ContinuousLinearMap.id ℝ _)

theorem spatialDifferenceQuotient_apply (z : SpatialCoordinates d) (h : ℝ)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    spatialDifferenceQuotient z h u=h⁻¹ • (spatialTranslationLp (h • z) u-u) := rfl

theorem IsWeakSpatialDerivative.differenceQuotient_bound
    {z : SpatialCoordinates d} {u v : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))}
    (hw : IsWeakSpatialDerivative volume univ z u v) (h : ℝ) :
    ‖spatialDifferenceQuotient z h u‖ ≤ ‖v‖ := by
  by_cases hh : h=0
  · subst h
    simp only [spatialDifferenceQuotient_apply,inv_zero,zero_smul,norm_zero,norm_nonneg]
  rw [spatialDifferenceQuotient_apply,norm_smul,Real.norm_eq_abs,abs_inv]
  calc
    _ ≤ |h|⁻¹*(|h| *‖v‖) := mul_le_mul_of_nonneg_left (hw.translation_bound h) (inv_nonneg.mpr (abs_nonneg h))
    _ = ‖v‖ := by rw [← mul_assoc,inv_mul_cancel₀ (abs_ne_zero.mpr hh),one_mul]

theorem spatialDifferenceQuotient_inner (z : SpatialCoordinates d) (h : ℝ)
    (u v : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    inner ℝ (spatialDifferenceQuotient z h u) v = -inner ℝ u (spatialDifferenceQuotient z (-h) v) := by
  simp only [spatialDifferenceQuotient_apply,real_inner_smul_left,real_inner_smul_right,
    inner_sub_left,inner_sub_right,spatialTranslationLp_inner,neg_smul,inv_neg,inner_neg_right]
  ring

theorem IsWeakSpatialDerivative.translation
    {e : SpatialCoordinates d} {u v : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))}
    (hw : IsWeakSpatialDerivative volume univ e u v) (z : SpatialCoordinates d) :
    IsWeakSpatialDerivative volume univ e (spatialTranslationLp z u) (spatialTranslationLp z v) := by
  let A := ContinuousLinearEquiv.refl ℝ (SpatialCoordinates d)
  have hm : MeasurePreserving (affineSpatialChart A (-z)) volume volume :=
    measurePreserving_add_right volume (-z)
  have he (f : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
      affineTransportLp A (-z) hm f=spatialTranslationLp z f := by
    apply Lp.ext
    filter_upwards [affineTransportLp_ae A (-z) hm f,spatialTranslationLp_ae z f] with x h1 h2
    rw [h1,h2]
    have hx : (affineSpatialChart A (-z)).symm x=x+z := by
      apply (affineSpatialChart A (-z)).injective
      rw [(affineSpatialChart A (-z)).apply_symm_apply,affineSpatialChart_apply]
      change x=(x+z)+(-z)
      abel
    simp only [Function.comp_apply,hx]
  have ht := hw.affine_transport (T := univ) A (-z) hm (subset_univ _)
  rw [he,he] at ht
  exact ht

theorem IsWeakSpatialDerivative.differenceQuotient
    {e : SpatialCoordinates d} {u v : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))}
    (hw : IsWeakSpatialDerivative volume univ e u v) (z : SpatialCoordinates d) (h : ℝ) :
    IsWeakSpatialDerivative volume univ e (spatialDifferenceQuotient z h u)
      (spatialDifferenceQuotient z h v) := by
  have ht := ((hw.translation (h • z)).add (hw.smul (-1))).smul h⁻¹
  simpa only [neg_one_smul,← sub_eq_add_neg,spatialDifferenceQuotient_apply] using ht

end Carleman
