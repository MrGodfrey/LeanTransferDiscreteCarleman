module

public import Carleman.Spatial.AffineBoxTraceMap
public import Carleman.Spatial.FiniteKernelCorrection
public import Carleman.Geometry.ClosedCoordinateFaces

/-! The kernel of the actual affine face-trace map is exactly the space of
polynomials vanishing on all selected closed faces. One correction constant
works for every subset of faces of a fixed box. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem affineBoxFaceMap_eq_zero_iff (i : Fin (d+1)) (a b : Fin (d+1) → ℝ)
    (hpos : ∀ j, a j < b j) (upper : Bool) (p : AffineCoefficients (d+1)) :
    affineBoxFaceMap i a b (hpos i) upper p=0 ↔
      ∀ y ∈ coordinateClosedFace i a b upper, affineCoefficientPolynomial p y=0 := by
  let f : SpatialCoordinates d → ℝ := fun x => affineCoefficientPolynomial p
    (WithLp.toLp 2 (i.insertNth (if upper then b i else a i) (fun j => x j)))
  have hf : Continuous f := (affineCoefficientPolynomial p).continuous_of_finiteDimensional.comp
    (coordinateFacePoint_continuous i _)
  have ha := affineBoxFaceMap_ae i a b (hpos i) upper p
  constructor
  · intro hz
    have hae : f =ᵐ[volume.restrict (openCoordinateBox (a ∘ i.succAbove) (b ∘ i.succAbove))] (fun _ => 0) := by
      apply ha.symm.trans
      rw [hz]
      exact Lp.coeFn_zero _ _ _
    have hp := Measure.eqOn_open_of_ae_eq hae
      (openCoordinateBox_isOpen (a ∘ i.succAbove) (b ∘ i.succAbove)) hf.continuousOn continuousOn_const
    have hc := hp.closure hf continuous_const
    rw [closure_openCoordinateBox (a ∘ i.succAbove) (b ∘ i.succAbove)
      (fun j => hpos (i.succAbove j))] at hc
    intro y hy
    rw [coordinateClosedFace_eq_image i a b (hpos i) upper] at hy
    obtain ⟨x,hx,rfl⟩ := hy
    exact hc hx
  · intro hp
    apply Lp.ext
    filter_upwards [ha,Lp.coeFn_zero ℝ 2 (volume.restrict (openCoordinateBox (a ∘ i.succAbove) (b ∘ i.succAbove))),
      ae_restrict_mem (openCoordinateBox_isOpen (a ∘ i.succAbove) (b ∘ i.succAbove)).measurableSet]
      with x hx hz hmem
    rw [hx,hz]
    apply hp
    rw [coordinateClosedFace_eq_image i a b (hpos i) upper]
    exact ⟨x,fun j => ⟨(hmem j).1.le,(hmem j).2.le⟩,rfl⟩

def affineBoxSelectedFaceMap (a b : Fin (d+1) → ℝ) (hpos : ∀ j, a j < b j)
    (J : Finset (Fin (d+1) × Bool)) :
    AffineCoefficients (d+1) →ₗ[ℝ]
      (∀ f : Fin (d+1) × Bool,
        Lp ℝ 2 (volume.restrict (openCoordinateBox (a ∘ f.1.succAbove) (b ∘ f.1.succAbove)))) := by
  classical
  exact LinearMap.pi fun f => if f ∈ J then affineBoxFaceMap f.1 a b (hpos f.1) f.2 else 0

theorem affineBoxSelectedFaceMap_apply (a b : Fin (d+1) → ℝ) (hpos : ∀ j, a j < b j)
    (J : Finset (Fin (d+1) × Bool)) (p : AffineCoefficients (d+1)) (f : Fin (d+1) × Bool) :
    affineBoxSelectedFaceMap a b hpos J p f =
      if f ∈ J then affineBoxFaceMap f.1 a b (hpos f.1) f.2 p else 0 := by
  classical
  simp only [affineBoxSelectedFaceMap,LinearMap.pi_apply]
  split_ifs <;> rfl

theorem affineBoxSelectedFaceMap_kernel (a b : Fin (d+1) → ℝ) (hpos : ∀ j, a j < b j)
    (J : Finset (Fin (d+1) × Bool)) (p : AffineCoefficients (d+1)) :
    affineBoxSelectedFaceMap a b hpos J p=0 ↔
      ∀ f ∈ J, ∀ y ∈ coordinateClosedFace f.1 a b f.2, affineCoefficientPolynomial p y=0 := by
  classical
  constructor
  · intro h f hf
    apply (affineBoxFaceMap_eq_zero_iff f.1 a b hpos f.2 p).mp
    have he := congrFun h f
    simpa only [affineBoxSelectedFaceMap_apply,ite_eq_left hf,Pi.zero_apply] using he
  · intro h
    funext f
    rw [affineBoxSelectedFaceMap_apply]
    by_cases hf : f ∈ J
    · rw [ite_eq_left hf]
      exact (affineBoxFaceMap_eq_zero_iff f.1 a b hpos f.2 p).mpr (h f hf)
    · rw [ite_eq_right hf]
      rfl

theorem affineBox_uniform_kernel_correction (a b : Fin (d+1) → ℝ) (hpos : ∀ j, a j < b j) :
    ∃ C > 0, ∀ J : Finset (Fin (d+1) × Bool), ∀ p : AffineCoefficients (d+1),
      ∃ q : AffineCoefficients (d+1),
        (∀ f ∈ J, ∀ y ∈ coordinateClosedFace f.1 a b f.2, affineCoefficientPolynomial q y=0) ∧
        ‖p-q‖ ≤ C*‖affineBoxSelectedFaceMap a b hpos J p‖ := by
  obtain ⟨C,hC,hcorr⟩ := finiteFamily_kernel_correction (affineBoxSelectedFaceMap a b hpos)
  refine ⟨C,hC,?_⟩
  intro J p
  obtain ⟨q,hq,he⟩ := hcorr J p
  exact ⟨q,(affineBoxSelectedFaceMap_kernel a b hpos J q).mp hq,he⟩

theorem affineBoxSelectedFaceMap_norm_le_rss (a b : Fin (d+1) → ℝ) (hpos : ∀ j, a j < b j)
    (J : Finset (Fin (d+1) × Bool)) (p : AffineCoefficients (d+1)) :
    ‖affineBoxSelectedFaceMap a b hpos J p‖ ≤
      Real.sqrt (∑ f ∈ J, ‖affineBoxFaceMap f.1 a b (hpos f.1) f.2 p‖^2) := by
  classical
  rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro f
  rw [affineBoxSelectedFaceMap_apply]
  by_cases hf : f ∈ J
  · rw [ite_eq_left hf]
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (Finset.sum_nonneg fun f _ =>
      sq_nonneg ‖affineBoxFaceMap f.1 a b (hpos f.1) f.2 p‖)]
    exact Finset.single_le_sum (fun f _ =>
      sq_nonneg ‖affineBoxFaceMap f.1 a b (hpos f.1) f.2 p‖) hf
  · rw [ite_eq_right hf,norm_zero]
    exact Real.sqrt_nonneg _

end Carleman
