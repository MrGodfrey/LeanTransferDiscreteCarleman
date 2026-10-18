module

public import Carleman.Spatial.AffineBoundaryCorrection

/-! Genuine affine H¹ jets form a linear map, and their weak face traces
are exactly the already constructed affine face maps. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

def affineBoxJetLinearMap (a b : Fin d → ℝ) :
    AffineCoefficients d →ₗ[ℝ] WeakSobolevJet d 1 (volume.restrict (openCoordinateBox a b))
      (openCoordinateBox a b) where
  toFun := affineBoxJet a b
  map_add' p q := by
    apply WeakSobolevJet.value_injective (openCoordinateBox_isOpen a b)
      (ae_restrict_mem (openCoordinateBox_isOpen a b).measurableSet)
    rw [map_add,affineBoxJet_value,affineBoxJet_value,affineBoxJet_value,map_add]
  map_smul' r p := by
    simp only [RingHom.id_apply]
    apply WeakSobolevJet.value_injective (openCoordinateBox_isOpen a b)
      (ae_restrict_mem (openCoordinateBox_isOpen a b).measurableSet)
    rw [map_smul,affineBoxJet_value,affineBoxJet_value,map_smul]

theorem affineBoxJetLinearMap_apply (a b : Fin d → ℝ) (p : AffineCoefficients d) :
    affineBoxJetLinearMap a b p=affineBoxJet a b p := rfl

theorem weakJetBoxFaceLinearMap_affine (i : Fin (d+1)) (a b : Fin (d+1) → ℝ)
    (hi : a i < b i) (upper : Bool) (p : AffineCoefficients (d+1)) :
    weakJetBoxFaceLinearMap i a b hi upper (affineBoxJet a b p)=affineBoxFaceMap i a b hi upper p := by
  change coordinateBoxFaceTrace i a b hi upper (WeakSobolevJet.value (affineBoxJet a b p))
    (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 (affineBoxJet a b p)))= _
  rw [affineBoxJet_value,affineBoxJet_gradient]
  have hcomp : derivativeComponent (Sym.cons i Sym.nil) (affineBoxGradientMap a b p)=
      affineBoxDerivativeMap a b i p := firstGradientAssembly_component _ i
  rw [hcomp]
  rfl

theorem unitCubeFace_norm_le (i : Fin (d+1)) (upper : Bool)
    (u : WeakSobolevJet (d+1) 1 (volume.restrict (openCoordinateBox (fun _ => 0) (fun _ => 1)))
      (openCoordinateBox (fun _ => 0) (fun _ => 1))) :
    ‖weakJetBoxFaceLinearMap i (fun _ => 0) (fun _ => 1) zero_lt_one upper u‖ ≤
      2*(‖WeakSobolevJet.value u‖+‖WeakSobolevJet.field 1 u‖) := by
  have h := weakJetBoxFaceTrace_norm_sq i (fun _ => 0) (fun _ => 1) zero_lt_one upper u
  simp only [sub_zero,div_one,mul_one] at h
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  change ‖weakJetBoxFaceTrace i (fun _ => 0) (fun _ => 1) zero_lt_one upper u‖^2 ≤ _
  nlinarith [norm_nonneg (WeakSobolevJet.value u),norm_nonneg (WeakSobolevJet.field 1 u),
    mul_nonneg (norm_nonneg (WeakSobolevJet.value u)) (norm_nonneg (WeakSobolevJet.field 1 u))]

theorem h1_value_gradient_add_bound {S : Set (SpatialCoordinates d)}
    (u v : WeakSobolevJet d 1 (volume.restrict S) S) :
    ‖WeakSobolevJet.value (u+v)‖+‖WeakSobolevJet.field 1 (u+v)‖ ≤
      (‖WeakSobolevJet.value u‖+‖WeakSobolevJet.field 1 u‖)+
        (‖WeakSobolevJet.value v‖+‖WeakSobolevJet.field 1 v‖) := by
  rw [map_add,map_add]
  linarith [norm_add_le (WeakSobolevJet.value u) (WeakSobolevJet.value v),
    norm_add_le (WeakSobolevJet.field 1 u) (WeakSobolevJet.field 1 v)]

end Carleman
