module

public import Carleman.Spatial.CartesianPhysicalSpaces
public import Carleman.Spatial.CartesianKuhnReconstructionJet

/-! The original hat reconstruction as an injective continuous linear map
from the complete physical nodal Hilbert space into the actual L² space. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

theorem cartesianKuhnReconstructionLp_eq_sum (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) :
    cartesianKuhnReconstructionLp o δ hδ N f=
      ∑ a, f a • cartesianKuhnHatLp o δ hδ N (cartesianInteriorLatticeIndex N a) := by
  apply Lp.ext
  filter_upwards [cartesianKuhnReconstructionLp_ae o δ hδ N f,
    Lp.coeFn_finsetSum Finset.univ (fun a => f a • cartesianKuhnHatLp o δ hδ N (cartesianInteriorLatticeIndex N a)),
    ae_all_iff.mpr (fun a => Lp.coeFn_smul (f a) (cartesianKuhnHatLp o δ hδ N (cartesianInteriorLatticeIndex N a))),
    ae_all_iff.mpr (fun a : CartesianInteriorIndex N => cartesianKuhnHatLp_ae o δ hδ N (cartesianInteriorLatticeIndex N a))]
    with x hx hs hm hh
  rw [hx,hs]
  simp only [cartesianKuhnReconstruction,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [hm a]
  change _=f a*cartesianKuhnHatLp o δ hδ N (cartesianInteriorLatticeIndex N a) x
  rw [hh a]

def cartesianPhysicalReconstructionLp (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) : CartesianPhysicalState δ hδ N →L[ℝ]
      Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun f => cartesianKuhnReconstructionLp o δ hδ N (fun a => f a)
    map_add' := by
      intro f g
      change cartesianKuhnReconstructionLp o δ hδ N (fun a => f a+g a)=
        cartesianKuhnReconstructionLp o δ hδ N (fun a => f a)+cartesianKuhnReconstructionLp o δ hδ N (fun a => g a)
      simp only [cartesianKuhnReconstructionLp_eq_sum]
      simp only [add_smul,Finset.sum_add_distrib]
    map_smul' := by
      intro c f
      change cartesianKuhnReconstructionLp o δ hδ N (fun a => c*f a)=
        c • cartesianKuhnReconstructionLp o δ hδ N (fun a => f a)
      simp only [cartesianKuhnReconstructionLp_eq_sum]
      simp only [mul_smul,Finset.smul_sum] }

theorem cartesianPhysicalReconstructionLp_apply (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianPhysicalState δ hδ N) :
    cartesianPhysicalReconstructionLp o δ hδ N f=cartesianKuhnReconstructionLp o δ hδ N f := rfl

theorem cartesianPhysicalReconstructionLp_injective (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) : Function.Injective (cartesianPhysicalReconstructionLp o δ hδ N) := by
  intro f g he
  have hz : cartesianKuhnReconstructionLp o δ hδ N (⇑(f-g))=0 := by
    change cartesianPhysicalReconstructionLp o δ hδ N (f-g)=0
    rw [map_sub,he,sub_self]
  have hb := (cartesianKuhnReconstructionLp_norm_sq_bounds o δ hδ N (⇑(f-g))).1
  rw [← PhysicalFiniteSpace.norm_sq (f-g)] at hb
  rw [hz,norm_zero,zero_pow (by decide : 2 ≠ 0)] at hb
  have hp : 0 < (d+2:ℝ)⁻¹ := by positivity
  have hn : ‖f-g‖^2 ≤ 0 := nonpos_of_mul_nonpos_right hb hp
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (f-g)]

end Carleman
