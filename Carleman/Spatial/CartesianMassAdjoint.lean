module

public import Carleman.Spatial.CartesianReconstructionLinear

/-! The actual normalized hat moments are exactly the Hilbert mass adjoint
of the original reconstruction in the physical state inner product. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

theorem cartesianKuhnMoment_eq_inner (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ)
    (u : Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))))
    (a : CartesianInteriorIndex N) :
    cartesianKuhnMoment o δ hδ N u a=(∏ j, δ j)⁻¹*
      inner ℝ u (cartesianKuhnHatLp o δ hδ N (cartesianInteriorLatticeIndex N a)) := by
  rw [cartesianKuhnMoment,L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [cartesianKuhnHatLp_ae o δ hδ N (cartesianInteriorLatticeIndex N a)] with x hx
  rw [hx]
  simp only [real_inner_comm]
  rfl

theorem cartesianKuhnMoment_pairing (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ)
    (u : Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))))
    (f : CartesianInteriorIndex N → ℝ) :
    cartesianPhysicalInner δ N (cartesianKuhnMoment o δ hδ N u) f=
      inner ℝ u (cartesianKuhnReconstructionLp o δ hδ N f) := by
  have hm : (∏ j, δ j) ≠ 0 := (Finset.prod_pos (fun j _ => hδ j)).ne'
  rw [cartesianPhysicalInner,cartesianKuhnReconstructionLp_eq_sum]
  simp only [cartesianKuhnMoment_eq_inner,inner_sum,real_inner_smul_right,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  field_simp

def cartesianPhysicalMoment (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ) :
    Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))) →L[ℝ]
      CartesianPhysicalState δ hδ N := (cartesianPhysicalReconstructionLp o δ hδ N).adjoint

theorem cartesianPhysicalMoment_values (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ)
    (u : Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))) :
    ⇑(cartesianPhysicalMoment o δ hδ N u)=cartesianKuhnMoment o δ hδ N u := by
  have he : cartesianPhysicalMoment o δ hδ N u=
      PhysicalFiniteSpace.valuesEquiv.symm (cartesianKuhnMoment o δ hδ N u) := by
    apply ext_inner_right ℝ
    intro f
    rw [cartesianPhysicalMoment,ContinuousLinearMap.adjoint_inner_left,cartesianPhysicalState_inner]
    exact (cartesianKuhnMoment_pairing o δ hδ N u f).symm
  exact congrArg (fun f : CartesianPhysicalState δ hδ N => fun a => f a) he

theorem cartesianPhysicalMoment_load_right_inverse (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianPhysicalState δ hδ N) :
    cartesianPhysicalMoment o δ hδ N (cartesianKuhnLoadLiftLp o δ hδ N f)=f := by
  apply PhysicalFiniteSpace.valuesEquiv.injective
  exact (cartesianPhysicalMoment_values o δ hδ N (cartesianKuhnLoadLiftLp o δ hδ N (fun a => f a))).trans
    (cartesianKuhnLoadLiftLp_right_inverse o δ hδ N (fun a => f a))

end Carleman
