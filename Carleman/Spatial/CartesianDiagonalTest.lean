module

public import Carleman.Spatial.CartesianFiniteDifference
public import Carleman.Spatial.SimplicialNodalOperator

/-! The original physical diagonal test on the full finite nodal space,
including its exact weighted pairing and true nodal reconstruction. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

def cartesianNodalMultiplier (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (ω : SpatialCoordinates d → ℝ) :
    (CartesianInteriorIndex N → ℝ) →ₗ[ℝ] (CartesianInteriorIndex N → ℝ) where
  toFun := fun f a => ω (cartesianInteriorPoint o δ N a)*f a
  map_add' := by intro f g; funext a; exact mul_add _ _ _
  map_smul' := by intro c f; funext a; change _*(c*_)=c*(_*_); ring

def cartesianSquaredWeightTest (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (σ : SpatialCoordinates d → ℝ) :
    (CartesianInteriorIndex N → ℝ) →ₗ[ℝ] (CartesianInteriorIndex N → ℝ) :=
  cartesianNodalMultiplier o δ N (fun x => (σ x)^2)

def cartesianWeightedNodeEnergy (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (σ : SpatialCoordinates d → ℝ) (f : CartesianInteriorIndex N → ℝ) : ℝ :=
  (∏ j, δ j)*∑ a, (σ (cartesianInteriorPoint o δ N a)*f a)^2

theorem cartesianNodalMultiplier_selfadjoint (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (ω : SpatialCoordinates d → ℝ) (f g : CartesianInteriorIndex N → ℝ) :
    cartesianPhysicalInner δ N (cartesianNodalMultiplier o δ N ω f) g=
      cartesianPhysicalInner δ N f (cartesianNodalMultiplier o δ N ω g) := by
  unfold cartesianPhysicalInner
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  change (ω (cartesianInteriorPoint o δ N a)*f a)*g a=f a*(ω (cartesianInteriorPoint o δ N a)*g a)
  ring

theorem cartesianSquaredWeightTest_pairing (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (σ : SpatialCoordinates d → ℝ) (f : CartesianInteriorIndex N → ℝ) :
    cartesianPhysicalInner δ N f (cartesianSquaredWeightTest o δ N σ f)=
      cartesianWeightedNodeEnergy o δ N σ f := by
  unfold cartesianPhysicalInner cartesianWeightedNodeEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  change f a*((σ (cartesianInteriorPoint o δ N a))^2*f a)=(σ (cartesianInteriorPoint o δ N a)*f a)^2
  ring

theorem cartesianWeightedNodeEnergy_nonneg (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (σ : SpatialCoordinates d → ℝ) (f : CartesianInteriorIndex N → ℝ) :
    0 ≤ cartesianWeightedNodeEnergy o δ N σ f :=
  mul_nonneg (Finset.prod_nonneg (fun j _ => (hδ j).le)) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem cartesianWeightedNodeEnergy_eq_zero_iff (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (σ : SpatialCoordinates d → ℝ)
    (hσ : ∀ a : CartesianInteriorIndex N, σ (cartesianInteriorPoint o δ N a) ≠ 0)
    (f : CartesianInteriorIndex N → ℝ) : cartesianWeightedNodeEnergy o δ N σ f=0 ↔ f=0 := by
  have hp : (∏ j, δ j) ≠ 0 := ne_of_gt (Finset.prod_pos (fun j _ => hδ j))
  rw [cartesianWeightedNodeEnergy,mul_eq_zero,or_iff_right hp,
    Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
  constructor
  · intro hz
    funext a
    have he := hz a (Finset.mem_univ a)
    exact (mul_eq_zero.mp (sq_eq_zero_iff.mp he)).resolve_left (hσ a)
  · intro hf a _
    rw [hf,Pi.zero_apply,mul_zero,zero_pow (by decide)]

theorem cartesianSquaredWeightTest_positive (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (σ : SpatialCoordinates d → ℝ)
    (hσ : ∀ a : CartesianInteriorIndex N, σ (cartesianInteriorPoint o δ N a) ≠ 0)
    (f : CartesianInteriorIndex N → ℝ) (hf : f ≠ 0) :
    0 < cartesianPhysicalInner δ N f (cartesianSquaredWeightTest o δ N σ f) := by
  rw [cartesianSquaredWeightTest_pairing]
  exact lt_of_le_of_ne (cartesianWeightedNodeEnergy_nonneg o δ hδ N σ f)
    (Ne.symm (fun he => hf ((cartesianWeightedNodeEnergy_eq_zero_iff o δ hδ N σ hσ f).mp he)))

theorem cartesianSquaredWeightTest_inverse_energy (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (σ : SpatialCoordinates d → ℝ)
    (hσ : ∀ a : CartesianInteriorIndex N, σ (cartesianInteriorPoint o δ N a) ≠ 0)
    (f : CartesianInteriorIndex N → ℝ) :
    cartesianWeightedNodeEnergy o δ N (fun x => (σ x)⁻¹) (cartesianSquaredWeightTest o δ N σ f)=
      cartesianWeightedNodeEnergy o δ N σ f := by
  unfold cartesianWeightedNodeEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  change ((σ (cartesianInteriorPoint o δ N a))⁻¹*((σ (cartesianInteriorPoint o δ N a))^2*f a))^2=
    (σ (cartesianInteriorPoint o δ N a)*f a)^2
  field_simp [hσ a]

theorem cartesianInteriorData_multiplier (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (ω : SpatialCoordinates d → ℝ) (f : CartesianInteriorIndex N → ℝ) :
    cartesianInteriorData o δ N (cartesianNodalMultiplier o δ N ω f)=
      fun x => ω x*cartesianInteriorData o δ N f x := by
  classical
  funext x
  simp only [cartesianInteriorData,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : cartesianInteriorPoint o δ N a=x
  · simp only [ite_eq_left ha]
    change ω (cartesianInteriorPoint o δ N a)*f a=ω x*f a
    rw [ha]
  · simp only [ite_eq_right ha,mul_zero]

theorem cartesianKuhnReconstruction_multiplier_nodal (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ω : SpatialCoordinates d → ℝ) (f : CartesianInteriorIndex N → ℝ) :
    cartesianKuhnReconstruction o δ hδ N (cartesianNodalMultiplier o δ N ω f)=
      (cartesianKuhnPartition o δ hδ N).nodalFunction (fun x => ω x*cartesianKuhnReconstruction o δ hδ N f x) := by
  rw [cartesianKuhnReconstruction_eq_nodal,cartesianInteriorData_multiplier]
  apply (cartesianKuhnPartition o δ hδ N).nodalFunction_congr
  intro i k
  rw [cartesianKuhnReconstruction_eq_nodal,
    (cartesianKuhnPartition o δ hδ N).nodalFunction_vertex (cartesianKuhnPartition_faceMatching o δ hδ N)]

theorem cartesianKuhnReconstructionLp_multiplier_nodal (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ω : SpatialCoordinates d → ℝ) (f : CartesianInteriorIndex N → ℝ) :
    cartesianKuhnReconstructionLp o δ hδ N (cartesianNodalMultiplier o δ N ω f)=
      (cartesianKuhnPartition o δ hδ N).nodalLp (openCoordinateBox_isOpen _ _).measurableSet
        (cartesianKuhnPartition_faceMatching o δ hδ N) (fun x => ω x*cartesianKuhnReconstruction o δ hδ N f x) := by
  rw [cartesianKuhnReconstructionLp_eq_nodal,cartesianInteriorData_multiplier]
  apply (cartesianKuhnPartition o δ hδ N).nodalLp_congr
  intro i k
  rw [cartesianKuhnReconstruction_eq_nodal,
    (cartesianKuhnPartition o δ hδ N).nodalFunction_vertex (cartesianKuhnPartition_faceMatching o δ hδ N)]

end Carleman
