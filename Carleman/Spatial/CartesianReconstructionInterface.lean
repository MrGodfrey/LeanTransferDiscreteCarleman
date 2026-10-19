module

public import Carleman.Spatial.CartesianMassAdjoint
public import Carleman.Spatial.CartesianKuhnProjection
public import Carleman.Transfer.Load

/-! The original Cartesian R/J/Q/G and actual load lift satisfy the same
mass and load interfaces used by the transfer theorem. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

def cartesianReconstruction (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ) :
    Reconstruction (dirichletSubspace (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))
      (CartesianPhysicalState δ hδ N) where
  R := (cartesianPhysicalReconstructionLp o δ hδ N).toLinearMap.codRestrict _
    (fun f => cartesianKuhnReconstructionLp_mem_dirichlet o δ hδ N (fun a => f a))
  J := (cartesianPhysicalMoment o δ hδ N).toLinearMap
  mass_adjoint u f := (cartesianPhysicalReconstructionLp o δ hδ N).adjoint_inner_left f u

theorem cartesianReconstruction_RH (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianPhysicalState δ hδ N) :
    (cartesianReconstruction o δ hδ N).RH f=cartesianKuhnReconstructionLp o δ hδ N (fun a => f a) := rfl

theorem cartesianReconstruction_J_values (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ)
    (u : Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))) :
    ⇑((cartesianReconstruction o δ hδ N).J u)=cartesianKuhnMoment o δ hδ N u :=
  cartesianPhysicalMoment_values o δ hδ N u

theorem cartesianReconstruction_QH (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ)
    (u : Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))) :
    (cartesianReconstruction o δ hδ N).QH u=cartesianKuhnProjectionLp o δ hδ N u :=
  congrArg (cartesianKuhnReconstructionLp o δ hδ N) (cartesianPhysicalMoment_values o δ hδ N u)

theorem cartesianReconstruction_G_values (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianPhysicalState δ hδ N) :
    ⇑((cartesianReconstruction o δ hδ N).G f)=
      cartesianKuhnMoment o δ hδ N (cartesianKuhnReconstructionLp o δ hδ N (fun a => f a)) :=
  cartesianPhysicalMoment_values o δ hδ N _

theorem cartesianReconstruction_injective (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) : Function.Injective (cartesianReconstruction o δ hδ N).R := by
  intro f g he
  apply cartesianPhysicalReconstructionLp_injective o δ hδ N
  exact congrArg Subtype.val he

def cartesianLoadInterface (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ) :
    LoadInterface (cartesianReconstruction o δ hδ N) (CartesianPhysicalState δ hδ N) where
  Γ := id
  lift := fun f => cartesianKuhnLoadLiftLp o δ hδ N (fun a => f a)
  compatible := cartesianPhysicalMoment_load_right_inverse o δ hδ N

theorem cartesianLoadInterface_Γ (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianPhysicalState δ hδ N) :
    (cartesianLoadInterface o δ hδ N).Γ f=f := rfl

theorem cartesianLoadInterface_lift (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianPhysicalState δ hδ N) :
    (cartesianLoadInterface o δ hδ N).lift f=cartesianKuhnLoadLiftLp o δ hδ N (fun a => f a) := rfl

theorem cartesianLoadInterface_right_inverse (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) : Function.RightInverse id (cartesianLoadInterface o δ hδ N).Γ := fun _ => rfl

end Carleman
