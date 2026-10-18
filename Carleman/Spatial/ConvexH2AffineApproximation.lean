module

public import Carleman.Spatial.H2MeanGradient
public import Carleman.Spatial.MeanAffinePolynomial
public import Carleman.Spatial.CoordinateFirstJet

/-! Homogeneous affine approximation for every genuine weak H² state on a
bounded open convex domain. The affine slope is the mean weak gradient and
the residual has mean zero. No pointwise representative or boundary trace
is assumed. Physical-face trace correction is a separate step. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

def h2MeanAffine (u : WeakSobolevJet d 2 (volume.restrict S) S) :
    SpatialCoordinates d →ᵃ[ℝ] ℝ :=
  meanAffinePolynomial (WeakSobolevJet.value u) (coordinateFunctional (weakGradientMean u))

def h2AffineResidualCoordinates [IsFiniteMeasure (volume.restrict S)]
    (u : WeakSobolevJet d 2 (volume.restrict S) S) (i : Fin d) : Lp ℝ 2 (volume.restrict S) :=
  derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)-
    scalarConstantLp (volume.restrict S) (weakGradientMean u i)

theorem h2AffineResidual_weak [IsFiniteMeasure (volume.restrict S)]
    (hb : Bornology.IsBounded S) (u : WeakSobolevJet d 2 (volume.restrict S) S) (i : Fin d) :
    IsWeakSpatialDerivative (volume.restrict S) S (EuclideanSpace.basisFun (Fin d) ℝ i)
      (WeakSobolevJet.value u-boundedAffineLp hb (h2MeanAffine u))
      (h2AffineResidualCoordinates u i) := by
  have hp := boundedAffineLp_weak hb (h2MeanAffine u) (EuclideanSpace.basisFun (Fin d) ℝ i)
  rw [h2MeanAffine,meanAffinePolynomial_derivative,coordinateFunctional_basis] at hp
  exact (WeakSobolevJet.field_weak_derivative u (0 : Fin 2) Sym.nil i).sub hp

def h2AffineResidual [IsFiniteMeasure (volume.restrict S)]
    (hb : Bornology.IsBounded S) (u : WeakSobolevJet d 2 (volume.restrict S) S) :
    WeakSobolevJet d 1 (volume.restrict S) S :=
  coordinateFirstJet (WeakSobolevJet.value u-boundedAffineLp hb (h2MeanAffine u))
    (h2AffineResidualCoordinates u) (h2AffineResidual_weak hb u)

theorem h2AffineResidual_value [IsFiniteMeasure (volume.restrict S)]
    (hb : Bornology.IsBounded S) (u : WeakSobolevJet d 2 (volume.restrict S) S) :
    WeakSobolevJet.value (h2AffineResidual hb u)=
      WeakSobolevJet.value u-boundedAffineLp hb (h2MeanAffine u) := coordinateFirstJet_value _ _ _

theorem h2AffineResidual_value_ae [IsFiniteMeasure (volume.restrict S)]
    (hb : Bornology.IsBounded S) (u : WeakSobolevJet d 2 (volume.restrict S) S) :
    WeakSobolevJet.value (h2AffineResidual hb u) =ᵐ[volume.restrict S]
      (fun x => WeakSobolevJet.value u x-h2MeanAffine u x) := by
  rw [h2AffineResidual_value]
  exact meanAffinePolynomial_residual_ae hb _ _

theorem h2AffineResidual_gradient_component [IsFiniteMeasure (volume.restrict S)]
    (hb : Bornology.IsBounded S) (u : WeakSobolevJet d 2 (volume.restrict S) S) (i : Fin d) :
    derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 (h2AffineResidual hb u))=
      derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)-
        scalarConstantLp (volume.restrict S)
          (affineScalarDerivative (h2MeanAffine u) (EuclideanSpace.basisFun (Fin d) ℝ i)) := by
  rw [h2MeanAffine,meanAffinePolynomial_derivative,coordinateFunctional_basis]
  exact firstGradientAssembly_component _ i

theorem h2AffineResidual_mean [IsFiniteMeasure (volume.restrict S)]
    (hb : Bornology.IsBounded S) (hvol : 0 < volume.real S)
    (u : WeakSobolevJet d 2 (volume.restrict S) S) :
    (∫ x in S, WeakSobolevJet.value (h2AffineResidual hb u) x)=0 := by
  rw [h2AffineResidual_value]
  exact meanAffinePolynomial_mean_residual hb hvol _ _

theorem h2AffineResidual_gradient_bound [IsFiniteMeasure (volume.restrict S)]
    (hS : IsOpen S) (hc : Convex ℝ S) (hb : Bornology.IsBounded S) (hvol : 0 < volume.real S)
    (u : WeakSobolevJet d 2 (volume.restrict S) S)
    {D : ℝ} (hD : 0 ≤ D) (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D) :
    ‖WeakSobolevJet.field 1 (h2AffineResidual hb u)‖^2 ≤
      (2:ℝ)^d/2*D^2*(d:ℝ)^2*‖WeakSobolevJet.field 2 u‖^2 := by
  rw [h2AffineResidual,coordinateFirstJet_gradient_norm_sq]
  exact h2_gradient_mean_bound hS hc hb hvol u hD hdiam

theorem h2AffineResidual_value_bound [IsFiniteMeasure (volume.restrict S)]
    (hS : IsOpen S) (hc : Convex ℝ S) (hb : Bornology.IsBounded S) (hvol : 0 < volume.real S)
    (u : WeakSobolevJet d 2 (volume.restrict S) S)
    {D : ℝ} (hD : 0 ≤ D) (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D) :
    ‖WeakSobolevJet.value (h2AffineResidual hb u)‖^2 ≤
      ((2:ℝ)^d/2)^2*D^4*(d:ℝ)^2*‖WeakSobolevJet.field 2 u‖^2 := by
  have he := convex_weakJet_mean_poincare hS hc hb hvol (h2AffineResidual hb u) hD hdiam
  rw [h2AffineResidual_mean hb hvol,zero_div] at he
  simp only [sub_zero] at he
  rw [← scalarLp_norm_sq] at he
  exact he.trans ((mul_le_mul_of_nonneg_left
    (h2AffineResidual_gradient_bound hS hc hb hvol u hD hdiam)
    (by positivity : 0 ≤ (2:ℝ)^d/2*D^2)).trans_eq (by ring))

theorem h2AffineResidual_homogeneous_bound [IsFiniteMeasure (volume.restrict S)]
    (hS : IsOpen S) (hc : Convex ℝ S) (hb : Bornology.IsBounded S) (hvol : 0 < volume.real S)
    (u : WeakSobolevJet d 2 (volume.restrict S) S)
    {D : ℝ} (hD : 0 ≤ D) (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D) :
    ‖WeakSobolevJet.value (h2AffineResidual hb u)‖+
      D*‖WeakSobolevJet.field 1 (h2AffineResidual hb u)‖ ≤
      ((2:ℝ)^d+1)*(d:ℝ)*D^2*‖WeakSobolevJet.field 2 u‖ := by
  let P : ℝ := (2:ℝ)^d/2
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hv : ‖WeakSobolevJet.value (h2AffineResidual hb u)‖ ≤
      P*(d:ℝ)*D^2*‖WeakSobolevJet.field 2 u‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    exact (h2AffineResidual_value_bound hS hc hb hvol u hD hdiam).trans_eq (by dsimp [P]; ring)
  have hg : ‖WeakSobolevJet.field 1 (h2AffineResidual hb u)‖ ≤
      (P+1)*(d:ℝ)*D*‖WeakSobolevJet.field 2 u‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    have hpp : P ≤ (P+1)^2 := by nlinarith [sq_nonneg P]
    calc
      _ ≤ P*D^2*(d:ℝ)^2*‖WeakSobolevJet.field 2 u‖^2 :=
        h2AffineResidual_gradient_bound hS hc hb hvol u hD hdiam
      _ ≤ (P+1)^2*(D^2*(d:ℝ)^2*‖WeakSobolevJet.field 2 u‖^2) := by
        nlinarith only [mul_le_mul_of_nonneg_right hpp
          (by positivity : 0 ≤ D^2*(d:ℝ)^2*‖WeakSobolevJet.field 2 u‖^2)]
      _ = _ := by ring
  exact (add_le_add hv (mul_le_mul_of_nonneg_left hg hD)).trans_eq (by dsimp [P]; ring)

theorem exists_convex_h2_affine_approximation
    (hS : IsOpen S) (hc : Convex ℝ S) (hb : Bornology.IsBounded S) (hvol : 0 < volume.real S)
    (u : WeakSobolevJet d 2 (volume.restrict S) S)
    {D : ℝ} (hD : 0 ≤ D) (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D) :
    ∃ (p : SpatialCoordinates d →ᵃ[ℝ] ℝ) (r : WeakSobolevJet d 1 (volume.restrict S) S),
      (WeakSobolevJet.value r =ᵐ[volume.restrict S] (fun x => WeakSobolevJet.value u x-p x)) ∧
      ‖WeakSobolevJet.value r‖+D*‖WeakSobolevJet.field 1 r‖ ≤
        ((2:ℝ)^d+1)*(d:ℝ)*D^2*‖WeakSobolevJet.field 2 u‖ := by
  let : IsFiniteMeasure (volume.restrict S) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hb.measure_lt_top (μ := volume)⟩
  exact ⟨h2MeanAffine u,h2AffineResidual hb u,h2AffineResidual_value_ae hb u,
    h2AffineResidual_homogeneous_bound hS hc hb hvol u hD hdiam⟩

end Carleman
