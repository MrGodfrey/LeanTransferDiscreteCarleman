module

public import Carleman.Spatial.CartesianReconstructionInterface

/-! The original (2d+1)-point Dirichlet Laplacian as a continuous operator
on the same full physical Hilbert space, with its exact original form identity. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem cartesianInteriorData_add (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (f g : CartesianInteriorIndex N → ℝ) (x : SpatialCoordinates d) :
    cartesianInteriorData o δ N (fun a => f a+g a) x=
      cartesianInteriorData o δ N f x+cartesianInteriorData o δ N g x := by
  classical
  simp only [cartesianInteriorData,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  split <;> simp_all only [add_zero]

theorem cartesianInteriorData_smul (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (c : ℝ) (f : CartesianInteriorIndex N → ℝ) (x : SpatialCoordinates d) :
    cartesianInteriorData o δ N (fun a => c*f a) x=c*cartesianInteriorData o δ N f x := by
  classical
  simp only [cartesianInteriorData,Finset.mul_sum,mul_ite,mul_zero]

def cartesianPhysicalLaplacian (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) : CartesianPhysicalState δ hδ N →L[ℝ] CartesianPhysicalState δ hδ N :=
  LinearMap.toContinuousLinearMap {
    toFun := fun f => PhysicalFiniteSpace.valuesEquiv.symm
      (cartesianFiniteDifferenceLaplacian o δ N (fun a => f a))
    map_add' := by
      intro f g
      apply PhysicalFiniteSpace.valuesEquiv.injective
      funext a
      change cartesianFiniteDifferenceLaplacian o δ N (fun a => f a+g a) a=
        cartesianFiniteDifferenceLaplacian o δ N (fun a => f a) a+
          cartesianFiniteDifferenceLaplacian o δ N (fun a => g a) a
      simp only [cartesianFiniteDifferenceLaplacian,cartesianLatticeData,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [cartesianInteriorData_add o δ N (fun a => f a) (fun a => g a),
        cartesianInteriorData_add o δ N (fun a => f a) (fun a => g a)]
      ring
    map_smul' := by
      intro c f
      apply PhysicalFiniteSpace.valuesEquiv.injective
      funext a
      change cartesianFiniteDifferenceLaplacian o δ N (fun a => c*f a) a=
        c*cartesianFiniteDifferenceLaplacian o δ N (fun a => f a) a
      simp only [cartesianFiniteDifferenceLaplacian,cartesianLatticeData,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [cartesianInteriorData_smul o δ N c (fun a => f a),
        cartesianInteriorData_smul o δ N c (fun a => f a)]
      ring }

theorem cartesianPhysicalLaplacian_values (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianPhysicalState δ hδ N) :
    ⇑(cartesianPhysicalLaplacian o δ hδ N f)=
      cartesianFiniteDifferenceLaplacian o δ N (fun a => f a) := rfl

theorem cartesianPhysicalLaplacian_stiffness (hd : 0 < d)
    (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (f g : CartesianPhysicalState δ hδ N) :
    inner ℝ (cartesianPhysicalLaplacian o δ hδ N f) g=
      (boundedDirichletOriginalForm (openCoordinateBox_isOpen _ _) hd
        (openCoordinateBox_isBounded o (fun j => o j+(N j:ℝ)*δ j))).scalarForm
        ((cartesianReconstruction o δ hδ N).R f) ((cartesianReconstruction o δ hδ N).R g) := by
  rw [cartesianPhysicalState_inner]
  change cartesianPhysicalInner δ N (cartesianFiniteDifferenceLaplacian o δ N (fun a => f a))
    (fun a => g a)=_
  exact cartesianFiniteDifferenceLaplacian_stiffness hd o δ hδ N (fun a => f a) (fun a => g a)

theorem cartesianPhysicalLaplacian_symmetric (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f g : CartesianPhysicalState δ hδ N) :
    inner ℝ (cartesianPhysicalLaplacian o δ hδ N f) g=
      inner ℝ f (cartesianPhysicalLaplacian o δ hδ N g) := by
  conv_rhs => rw [real_inner_comm]
  rw [cartesianPhysicalState_inner,cartesianPhysicalState_inner]
  change cartesianPhysicalInner δ N (cartesianFiniteDifferenceLaplacian o δ N (fun a => f a))
    (fun a => g a)=cartesianPhysicalInner δ N
      (cartesianFiniteDifferenceLaplacian o δ N (fun a => g a)) (fun a => f a)
  rw [cartesianFiniteDifferenceLaplacian_pairing_edges o δ hδ N,
    cartesianFiniteDifferenceLaplacian_pairing_edges o δ hδ N]
  simp only [mul_comm]

theorem cartesianPhysicalLaplacian_adjoint (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) :
    (cartesianPhysicalLaplacian o δ hδ N).adjoint=cartesianPhysicalLaplacian o δ hδ N := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (cartesianPhysicalLaplacian_symmetric o δ hδ N f g).symm

theorem cartesianPhysicalLaplacian_nonneg (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianPhysicalState δ hδ N) :
    0 ≤ inner ℝ (cartesianPhysicalLaplacian o δ hδ N f) f := by
  rw [cartesianPhysicalState_inner]
  change 0 ≤ cartesianPhysicalInner δ N
    (cartesianFiniteDifferenceLaplacian o δ N (fun a => f a)) (fun a => f a)
  rw [cartesianFiniteDifferenceLaplacian_pairing_edges o δ hδ N]
  exact mul_nonneg (Finset.prod_nonneg (fun j _ => (hδ j).le))
    (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)))

end Carleman
