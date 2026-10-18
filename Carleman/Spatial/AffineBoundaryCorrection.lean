module

public import Carleman.Spatial.AffineBoundaryKernel
public import Carleman.Spatial.CoordinateFirstJet

/-! Finite-face affine correction in actual bulk L² and full-gradient norms.
For the unit cube one constant depends only on dimension, uniformly over all
subsets of its closed faces. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem affineCoefficientPolynomial_surjective :
    Function.Surjective (affineCoefficientPolynomial : AffineCoefficients d → (SpatialCoordinates d →ᵃ[ℝ] ℝ)) := by
  intro p
  refine ⟨(p 0,affineScalarDerivative p),?_⟩
  ext x
  rw [affineCoefficientPolynomial_apply]
  have h : p x-p 0=affineScalarDerivative p (x-0) := (p.linear_apply_vsub x 0).symm
  rw [sub_zero] at h
  change p 0+affineScalarDerivative p x=p x
  linarith

def affineBoxGradientMap (a b : Fin d → ℝ) :
    AffineCoefficients d →ₗ[ℝ] Lp (DerivativeFiber d 1) 2 (volume.restrict (openCoordinateBox a b)) :=
  firstGradientAssembly.toLinearMap.comp (LinearMap.pi (affineBoxDerivativeMap a b))

def affineBoxJet (a b : Fin d → ℝ) (p : AffineCoefficients d) :
    WeakSobolevJet d 1 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b) :=
  coordinateFirstJet (affineBoxValueMap a b p) (fun i => affineBoxDerivativeMap a b i p)
    (fun i => affineBoxDerivativeMap_weak a b i p)

theorem affineBoxJet_value (a b : Fin d → ℝ) (p : AffineCoefficients d) :
    WeakSobolevJet.value (affineBoxJet a b p)=affineBoxValueMap a b p := coordinateFirstJet_value _ _ _

theorem affineBoxJet_gradient (a b : Fin d → ℝ) (p : AffineCoefficients d) :
    WeakSobolevJet.field 1 (affineBoxJet a b p)=affineBoxGradientMap a b p := rfl

theorem affineBox_bulk_norm_bound (a b : Fin d → ℝ) :
    ∃ C > 0, ∀ p : AffineCoefficients d,
      ‖affineBoxValueMap a b p‖+‖affineBoxGradientMap a b p‖ ≤ C*‖p‖ := by
  let V := (affineBoxValueMap a b).toContinuousLinearMap
  let G := (affineBoxGradientMap a b).toContinuousLinearMap
  refine ⟨1+‖V‖+‖G‖,by positivity,?_⟩
  intro p
  have hv := V.le_opNorm p
  have hg := G.le_opNorm p
  change ‖affineBoxValueMap a b p‖ ≤ ‖V‖*‖p‖ at hv
  change ‖affineBoxGradientMap a b p‖ ≤ ‖G‖*‖p‖ at hg
  nlinarith [norm_nonneg p]

theorem affineBox_uniform_h1_correction (a b : Fin (d+1) → ℝ) (hpos : ∀ j, a j < b j) :
    ∃ C > 0, ∀ J : Finset (Fin (d+1) × Bool), ∀ p : AffineCoefficients (d+1),
      ∃ q : AffineCoefficients (d+1),
        (∀ f ∈ J, ∀ y ∈ coordinateClosedFace f.1 a b f.2, affineCoefficientPolynomial q y=0) ∧
        ‖WeakSobolevJet.value (affineBoxJet a b (p-q))‖+
          ‖WeakSobolevJet.field 1 (affineBoxJet a b (p-q))‖ ≤
            C*‖affineBoxSelectedFaceMap a b hpos J p‖ := by
  obtain ⟨K,hK,hcorr⟩ := affineBox_uniform_kernel_correction a b hpos
  obtain ⟨B,hB,hbound⟩ := affineBox_bulk_norm_bound a b
  refine ⟨B*K,mul_pos hB hK,?_⟩
  intro J p
  obtain ⟨q,hq,he⟩ := hcorr J p
  refine ⟨q,hq,?_⟩
  rw [affineBoxJet_value,affineBoxJet_gradient]
  calc
    _ ≤ B*‖p-q‖ := hbound (p-q)
    _ ≤ B*(K*‖affineBoxSelectedFaceMap a b hpos J p‖) := mul_le_mul_of_nonneg_left he hB.le
    _ = _ := by ring

theorem affineBox_uniform_h1_correction_rss (a b : Fin (d+1) → ℝ) (hpos : ∀ j, a j < b j) :
    ∃ C > 0, ∀ J : Finset (Fin (d+1) × Bool), ∀ p : AffineCoefficients (d+1),
      ∃ q : AffineCoefficients (d+1),
        (∀ f ∈ J, ∀ y ∈ coordinateClosedFace f.1 a b f.2, affineCoefficientPolynomial q y=0) ∧
        ‖WeakSobolevJet.value (affineBoxJet a b (p-q))‖+
          ‖WeakSobolevJet.field 1 (affineBoxJet a b (p-q))‖ ≤
            C*Real.sqrt (∑ f ∈ J, ‖affineBoxFaceMap f.1 a b (hpos f.1) f.2 p‖^2) := by
  obtain ⟨C,hC,hcorr⟩ := affineBox_uniform_h1_correction a b hpos
  refine ⟨C,hC,?_⟩
  intro J p
  obtain ⟨q,hq,he⟩ := hcorr J p
  exact ⟨q,hq,he.trans (mul_le_mul_of_nonneg_left (affineBoxSelectedFaceMap_norm_le_rss a b hpos J p) hC.le)⟩

theorem unitCube_uniform_affine_correction (d : ℕ) :
    ∃ C > 0, ∀ J : Finset (Fin (d+1) × Bool), ∀ p : AffineCoefficients (d+1),
      ∃ q : AffineCoefficients (d+1),
        (∀ f ∈ J, ∀ y ∈ coordinateClosedFace f.1 (fun _ => 0) (fun _ => 1) f.2,
          affineCoefficientPolynomial q y=0) ∧
        ‖WeakSobolevJet.value (affineBoxJet (fun _ => 0) (fun _ => 1) (p-q))‖+
          ‖WeakSobolevJet.field 1 (affineBoxJet (fun _ => 0) (fun _ => 1) (p-q))‖ ≤
            C*Real.sqrt (∑ f ∈ J,
              ‖affineBoxFaceMap f.1 (fun _ => 0) (fun _ => 1) zero_lt_one f.2 p‖^2) :=
  affineBox_uniform_h1_correction_rss (fun _ => 0) (fun _ => 1) (fun _ => zero_lt_one)

end Carleman
