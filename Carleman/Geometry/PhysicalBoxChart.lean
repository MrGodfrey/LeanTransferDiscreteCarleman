module

public import Carleman.Geometry.CoordinateBoxScaling

/-! Exact reference-to-physical box geometry and integration, including closed
faces and their lower-dimensional Jacobians. All lengths are strictly positive. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

def physicalBoxChart (a ℓ : Fin d → ℝ) (hℓ : ∀ i, 0 < ℓ i) :
    SpatialCoordinates d ≃ₜ SpatialCoordinates d :=
  affineChange (coordinateDilation ℓ hℓ) (WithLp.toLp 2 a)

theorem physicalBoxChart_apply (a ℓ : Fin d → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (x : SpatialCoordinates d) (i : Fin d) : physicalBoxChart a ℓ hℓ x i=a i+ℓ i*x i := by
  change ℓ i*x i+a i=a i+ℓ i*x i
  ring

theorem physicalBoxChart_preimage_open (a ℓ : Fin d → ℝ) (hℓ : ∀ i, 0 < ℓ i) :
    physicalBoxChart a ℓ hℓ ⁻¹' openCoordinateBox a (fun i => a i+ℓ i) =
      openCoordinateBox (fun _ => 0) (fun _ => 1) := by
  ext x
  simp only [mem_preimage,openCoordinateBox,mem_ofPred_eq,physicalBoxChart_apply]
  apply forall_congr'
  intro i
  constructor
  · rintro ⟨h1,h2⟩
    constructor <;> nlinarith [hℓ i]
  · rintro ⟨h1,h2⟩
    constructor <;> nlinarith [hℓ i]

theorem physicalBoxChart_image_open (a ℓ : Fin d → ℝ) (hℓ : ∀ i, 0 < ℓ i) :
    physicalBoxChart a ℓ hℓ '' openCoordinateBox (fun _ => 0) (fun _ => 1) =
      openCoordinateBox a (fun i => a i+ℓ i) := by
  rw [← physicalBoxChart_preimage_open a ℓ hℓ]
  exact image_preimage_eq _ (physicalBoxChart a ℓ hℓ).surjective

theorem physicalBoxChart_preimage_closed (a ℓ : Fin d → ℝ) (hℓ : ∀ i, 0 < ℓ i) :
    physicalBoxChart a ℓ hℓ ⁻¹' closedCoordinateBox a (fun i => a i+ℓ i) =
      closedCoordinateBox (fun _ => 0) (fun _ => 1) := by
  ext x
  simp only [mem_preimage,closedCoordinateBox,mem_ofPred_eq,physicalBoxChart_apply]
  apply forall_congr'
  intro i
  constructor
  · rintro ⟨h1,h2⟩
    constructor <;> nlinarith [hℓ i]
  · rintro ⟨h1,h2⟩
    constructor <;> nlinarith [hℓ i]

theorem physicalBoxChart_preimage_face (i : Fin (d+1)) (a ℓ : Fin (d+1) → ℝ)
    (hℓ : ∀ j, 0 < ℓ j) (upper : Bool) :
    physicalBoxChart a ℓ hℓ ⁻¹' coordinateClosedFace i a (fun j => a j+ℓ j) upper =
      coordinateClosedFace i (fun _ => 0) (fun _ => 1) upper := by
  rw [coordinateClosedFace,preimage_inter,physicalBoxChart_preimage_closed]
  congr 1
  ext x
  simp only [mem_preimage,mem_ofPred_eq,physicalBoxChart_apply]
  cases upper <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;>
    constructor <;> intro h <;> nlinarith [hℓ i]

theorem physicalBoxChart_image_face (i : Fin (d+1)) (a ℓ : Fin (d+1) → ℝ)
    (hℓ : ∀ j, 0 < ℓ j) (upper : Bool) :
    physicalBoxChart a ℓ hℓ '' coordinateClosedFace i (fun _ => 0) (fun _ => 1) upper =
      coordinateClosedFace i a (fun j => a j+ℓ j) upper := by
  rw [← physicalBoxChart_preimage_face i a ℓ hℓ upper]
  exact image_preimage_eq _ (physicalBoxChart a ℓ hℓ).surjective

theorem physicalBoxChart_facePoint (i : Fin (d+1)) (a ℓ : Fin (d+1) → ℝ)
    (hℓ : ∀ j, 0 < ℓ j) (upper : Bool) (x : SpatialCoordinates d) :
    physicalBoxChart a ℓ hℓ
      (WithLp.toLp 2 (i.insertNth (if upper then 1 else 0) (fun j => x j))) =
      WithLp.toLp 2 (i.insertNth (if upper then a i+ℓ i else a i)
        (fun j => physicalBoxChart (a ∘ i.succAbove) (ℓ ∘ i.succAbove)
          (fun j => hℓ (i.succAbove j)) x j)) := by
  apply PiLp.ext
  intro j
  induction j using Fin.succAboveCases i with
  | x =>
    rw [physicalBoxChart_apply]
    simp only [Fin.insertNth_apply_same]
    cases upper <;> simp
  | p j =>
    simp only [physicalBoxChart_apply,Fin.insertNth_apply_succAbove,Function.comp_apply]

theorem integral_physicalBoxChart (a ℓ : Fin d → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (f : SpatialCoordinates d → ℝ) :
    (∫ x in openCoordinateBox a (fun i => a i+ℓ i), f x) =
      (∏ i, ℓ i) * ∫ y in openCoordinateBox (fun _ => 0) (fun _ => 1), f (physicalBoxChart a ℓ hℓ y) := by
  have h := integral_comp_affineChange (coordinateDilation ℓ hℓ) (WithLp.toLp 2 a)
    (openCoordinateBox (fun _ => 0) (fun _ => 1)) f
  change (∫ y in openCoordinateBox (fun _ => 0) (fun _ => 1), f (physicalBoxChart a ℓ hℓ y)) =
    (affineJacobian (coordinateDilation ℓ hℓ))⁻¹ *
      ∫ x in physicalBoxChart a ℓ hℓ '' openCoordinateBox (fun _ => 0) (fun _ => 1), f x at h
  rw [physicalBoxChart_image_open,coordinateDilation_jacobian] at h
  rw [h,← mul_assoc,mul_inv_cancel₀ (Finset.prod_pos fun i _ => hℓ i).ne',one_mul]

theorem physicalBoxChart_face_jacobian (i : Fin (d+1)) (ℓ : Fin (d+1) → ℝ)
    (hℓ : ∀ j, 0 < ℓ j) :
    (∏ j : Fin d, ℓ (i.succAbove j))=(∏ j, ℓ j)/ℓ i := by
  rw [Fin.prod_univ_succAbove _ i]
  field_simp [(hℓ i).ne']

end Carleman
