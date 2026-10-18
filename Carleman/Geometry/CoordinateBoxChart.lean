module

public import Carleman.Geometry.EuclideanCoordinateSplit
public import Carleman.Spatial.AffineWeakTransport
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Group.Prod

/-! Arbitrarily located coordinate boxes, with their actual product chart and
restricted Lebesgue measures. No coordinate side is normalized by scaling. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

def openCoordinateBox (a b : Fin d → ℝ) : Set (SpatialCoordinates d) :=
  {x | ∀ j, a j < x j ∧ x j < b j}

theorem openCoordinateBox_isOpen (a b : Fin d → ℝ) : IsOpen (openCoordinateBox a b) := by
  have he : openCoordinateBox a b = ⋂ j, {x : SpatialCoordinates d | a j < x j ∧ x j < b j} := by
    ext x
    simp [openCoordinateBox]
  rw [he]
  exact isOpen_iInter_of_finite fun j => (isOpen_lt continuous_const (EuclideanSpace.proj j).continuous).inter
    (isOpen_lt (EuclideanSpace.proj j).continuous continuous_const)

theorem openCoordinateBox_isBounded (a b : Fin d → ℝ) :
    Bornology.IsBounded (openCoordinateBox a b) := by
  have hc := (isCompact_Icc : IsCompact (Icc a b)).image (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))
  apply hc.isBounded.subset
  intro x hx
  exact ⟨WithLp.ofLp x,⟨fun j => (hx j).1.le,fun j => (hx j).2.le⟩,rfl⟩

instance openCoordinateBox_finite (a b : Fin d → ℝ) :
    IsFiniteMeasure (volume.restrict (openCoordinateBox a b)) :=
  ⟨by simpa using (openCoordinateBox_isBounded a b).measure_lt_top (μ := volume)⟩

def coordinateBoxChart (i : Fin (d+1)) (a : ℝ) :
    SpatialCoordinates (d+1) ≃ₜ SpatialCoordinates d × ℝ :=
  affineSpatialChart (coordinateSplit i) (0,-a)

theorem coordinateBoxChart_apply (i : Fin (d+1)) (a : ℝ) (x : SpatialCoordinates (d+1)) :
    coordinateBoxChart i a x=(WithLp.toLp 2 (fun j => x (i.succAbove j)),x i-a) := by
  simp [coordinateBoxChart,affineSpatialChart_apply,coordinateSplit_apply,sub_eq_add_neg]

theorem coordinateBoxChart_symm_apply (i : Fin (d+1)) (a : ℝ) (x : SpatialCoordinates d × ℝ) :
    (coordinateBoxChart i a).symm x=WithLp.toLp 2 (i.insertNth (x.2+a) (fun j => x.1 j)) := by
  apply (coordinateBoxChart i a).injective
  rw [Homeomorph.apply_symm_apply,coordinateBoxChart_apply]
  simp only [Fin.insertNth_apply_succAbove,Fin.insertNth_apply_same,
    add_sub_cancel_right]

theorem coordinateBoxChart_preimage (i : Fin (d+1)) (a b : Fin (d+1) → ℝ) :
    (coordinateBoxChart i (a i)) ⁻¹'
      (openCoordinateBox (a ∘ i.succAbove) (b ∘ i.succAbove) ×ˢ Ioo 0 (b i-a i)) =
        openCoordinateBox a b := by
  ext x
  simp only [mem_preimage,coordinateBoxChart_apply,mem_prod,openCoordinateBox,mem_ofPred_eq,
    Function.comp_apply,mem_Ioo]
  rw [Fin.forall_iff_succAbove i]
  constructor
  · rintro ⟨h,ht⟩
    exact ⟨by constructor <;> linarith [ht.1,ht.2],h⟩
  · rintro ⟨ht,h⟩
    exact ⟨h,by constructor <;> linarith [ht.1,ht.2]⟩

theorem coordinateBoxChart_image (i : Fin (d+1)) (a b : Fin (d+1) → ℝ) :
    coordinateBoxChart i (a i) '' openCoordinateBox a b =
      openCoordinateBox (a ∘ i.succAbove) (b ∘ i.succAbove) ×ˢ Ioo 0 (b i-a i) := by
  rw [← coordinateBoxChart_preimage i a b]
  exact image_preimage_eq _ (coordinateBoxChart i (a i)).surjective

theorem coordinateBoxChart_measurePreserving (i : Fin (d+1)) (a : ℝ) :
    MeasurePreserving (coordinateBoxChart i a) volume volume := by
  have hm := ((MeasurePreserving.id (volume : Measure (SpatialCoordinates d))).prod
    (measurePreserving_add_right (volume : Measure ℝ) (-a))).comp (coordinateSplit_measurePreserving i)
  convert hm using 1
  funext x
  simp [coordinateBoxChart_apply,coordinateSplit_apply,Function.comp_apply,sub_eq_add_neg]

theorem coordinateBoxChart_restrict (i : Fin (d+1)) (a b : Fin (d+1) → ℝ) :
    MeasurePreserving (coordinateBoxChart i (a i)) (volume.restrict (openCoordinateBox a b))
      ((volume.restrict (openCoordinateBox (a ∘ i.succAbove) (b ∘ i.succAbove))).prod
        (volume.restrict (Ioo 0 (b i-a i)))) := by
  have h := (coordinateBoxChart_measurePreserving i (a i)).restrict_image_emb
    (coordinateBoxChart i (a i)).toMeasurableEquiv.measurableEmbedding (openCoordinateBox a b)
  rw [coordinateBoxChart_image] at h
  change MeasurePreserving _ _ ((volume.prod volume).restrict _) at h
  rw [← Measure.prod_restrict] at h
  exact h

end Carleman
