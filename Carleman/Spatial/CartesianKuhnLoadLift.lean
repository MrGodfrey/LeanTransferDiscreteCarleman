module

public import Carleman.Geometry.CartesianInteriorNodes
public import Carleman.Spatial.CartesianKuhnLoadMoment

/-! A genuine L² load lift on the original full finite interior-node
space, with its exact normalized-moment right inverse. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

def cartesianKuhnLoadLift (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) : SpatialCoordinates d → ℝ :=
  cartesianKuhnLoad o δ hδ N (cartesianInteriorData o δ N f)

theorem cartesianKuhnLoadLift_memLp (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) :
    MemLp (cartesianKuhnLoadLift o δ hδ N f) 2
      (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))) :=
  (cartesianKuhnLoad_memLp o δ hδ N _).mono_measure Measure.restrict_le_self

def cartesianKuhnLoadLiftLp (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) :
    Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))) :=
  (cartesianKuhnLoadLift_memLp o δ hδ N f).toLp (cartesianKuhnLoadLift o δ hδ N f)

theorem cartesianKuhnLoadLiftLp_ae (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) :
    cartesianKuhnLoadLiftLp o δ hδ N f =ᵐ[volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))]
      cartesianKuhnLoadLift o δ hδ N f :=
  (cartesianKuhnLoadLift_memLp o δ hδ N f).coeFn_toLp

def cartesianKuhnMoment (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ)
    (u : Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))) :
    CartesianInteriorIndex N → ℝ := fun a =>
  (∏ j, δ j)⁻¹*(∫ x in openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j),
    u x*cartesianKuhnHat o δ hδ N (cartesianInteriorLatticeIndex N a) x)

theorem cartesianKuhnMoment_integrable (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ)
    (u : Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))))
    (a : CartesianInteriorIndex N) :
    Integrable (fun x => u x*cartesianKuhnHat o δ hδ N (cartesianInteriorLatticeIndex N a) x)
      (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))) :=
  (Lp.memLp u).integrable_mul ((Lp.memLp (cartesianKuhnHatLp o δ hδ N _)).ae_eq
    (cartesianKuhnHatLp_ae o δ hδ N _))

theorem cartesianKuhnLoadLiftLp_right_inverse (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) :
    cartesianKuhnMoment o δ hδ N (cartesianKuhnLoadLiftLp o δ hδ N f)=f := by
  funext a
  change (∏ j, δ j)⁻¹*(∫ x in openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j),
    cartesianKuhnLoadLiftLp o δ hδ N f x*cartesianKuhnHat o δ hδ N (cartesianInteriorLatticeIndex N a) x)=f a
  have he := integral_congr_ae ((cartesianKuhnLoadLiftLp_ae o δ hδ N f).mono
    (fun x hx => congrArg (fun v => v*cartesianKuhnHat o δ hδ N (cartesianInteriorLatticeIndex N a) x) hx))
  rw [he]
  change (∏ j, δ j)⁻¹*(∫ x in openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j),
    cartesianKuhnLoad o δ hδ N (cartesianInteriorData o δ N f) x*
      cartesianKuhnHat o δ hδ N (cartesianInteriorLatticeIndex N a) x)=f a
  rw [cartesianKuhnLoad_moment_right_inverse o δ hδ N _ _ (cartesianInteriorPoint_mem o δ hδ N a)]
  exact cartesianInteriorData_at_node o δ hδ N f a

theorem cartesianKuhnMoment_surjective (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) : Function.Surjective (cartesianKuhnMoment o δ hδ N) := by
  intro f
  exact ⟨cartesianKuhnLoadLiftLp o δ hδ N f,cartesianKuhnLoadLiftLp_right_inverse o δ hδ N f⟩

end Carleman
