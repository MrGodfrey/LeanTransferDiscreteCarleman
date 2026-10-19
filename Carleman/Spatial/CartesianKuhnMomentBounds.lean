module

public import Carleman.Spatial.CartesianKuhnLoadLift
public import Carleman.Spatial.RealL2Integral

/-! Local Cauchy--Schwarz estimates for the original normalized moments.
Only the actual support of the interior hat enters the local L² data. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

theorem cartesianKuhnMoment_local_integral (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ)
    (u : Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))))
    (a : CartesianInteriorIndex N) (B : Set (SpatialCoordinates d))
    (hBS : B ⊆ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))
    (hs : Function.support (cartesianKuhnHat o δ hδ N (cartesianInteriorLatticeIndex N a)) ⊆ B) :
    cartesianKuhnMoment o δ hδ N u a=(∏ j, δ j)⁻¹*
      (∫ x in B, u x*cartesianKuhnHat o δ hδ N (cartesianInteriorLatticeIndex N a) x) := by
  unfold cartesianKuhnMoment
  congr 1
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (openCoordinateBox_isOpen _ _).measurableSet hBS
  intro x hx
  have hz : cartesianKuhnHat o δ hδ N (cartesianInteriorLatticeIndex N a) x=0 := by
    by_contra hn
    exact hx.2 (hs hn)
  rw [hz,mul_zero]

theorem cartesianKuhnMoment_local_sq_bound (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ)
    (u : Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))))
    (a : CartesianInteriorIndex N) (B : Set (SpatialCoordinates d))
    (hBS : B ⊆ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))
    (hs : Function.support (cartesianKuhnHat o δ hδ N (cartesianInteriorLatticeIndex N a)) ⊆ B) :
    (∏ j, δ j)*(cartesianKuhnMoment o δ hδ N u a)^2 ≤ ∫ x in B, (u x)^2 := by
  let φ := cartesianKuhnHat o δ hδ N (cartesianInteriorLatticeIndex N a)
  have hφ : MemLp φ 2 (volume.restrict B) :=
    ((Lp.memLp (cartesianKuhnHatLp o δ hδ N _)).ae_eq (cartesianKuhnHatLp_ae o δ hδ N _)).mono_measure
      (Measure.restrict_mono hBS le_rfl)
  have hφint : Integrable φ volume := cartesianKuhnHat_integrable o δ hδ N _ (cartesianInteriorPoint_mem o δ hδ N a)
  have hsq : (∫ x in B, φ x^2) ≤ ∏ j, δ j := by
    calc
      _ ≤ ∫ x in B, φ x := integral_mono hφ.integrable_sq hφint.integrableOn (fun x => by
        have h0 := cartesianKuhnHat_nonneg o δ hδ N (cartesianInteriorLatticeIndex N a) x
        have h1 := cartesianKuhnHat_le_one o δ hδ N (cartesianInteriorLatticeIndex N a) x
        change φ x^2 ≤ φ x
        dsimp only [φ] at *
        nlinarith)
      _ ≤ ∫ x in openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j), φ x :=
        setIntegral_mono_set hφint.integrableOn (Filter.Eventually.of_forall (fun x =>
          cartesianKuhnHat_nonneg o δ hδ N _ x)) (Filter.Eventually.of_forall hBS)
      _ = _ := cartesianKuhnHat_mass_domain o δ hδ N _ (cartesianInteriorPoint_mem o δ hδ N a)
  have hu := (Lp.memLp u).mono_measure (Measure.restrict_mono hBS le_rfl)
  have hcs := (integral_mul_sq_le hu hφ).trans
    (mul_le_mul_of_nonneg_left hsq (integral_nonneg (fun x => sq_nonneg (u x))))
  have hω : 0 < ∏ j, δ j := Finset.prod_pos (fun j _ => hδ j)
  rw [cartesianKuhnMoment_local_integral o δ hδ N u a B hBS hs]
  apply (mul_le_mul_iff_right₀ hω).mp
  calc
    _ = (∫ x in B, u x*φ x)^2 := by field_simp; ring
    _ ≤ _ := by simpa only [mul_comm] using hcs

theorem cartesianKuhnMoment_local_congr (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ)
    (u v : Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))))
    (a : CartesianInteriorIndex N) (B : Set (SpatialCoordinates d))
    (hBS : B ⊆ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))
    (hs : Function.support (cartesianKuhnHat o δ hδ N (cartesianInteriorLatticeIndex N a)) ⊆ B)
    (he : u =ᵐ[volume.restrict B] v) :
    cartesianKuhnMoment o δ hδ N u a=cartesianKuhnMoment o δ hδ N v a := by
  rw [cartesianKuhnMoment_local_integral o δ hδ N u a B hBS hs,
    cartesianKuhnMoment_local_integral o δ hδ N v a B hBS hs]
  congr 1
  exact integral_congr_ae (he.mono (fun x hx => congrArg (fun r => r*
    cartesianKuhnHat o δ hδ N (cartesianInteriorLatticeIndex N a) x) hx))

end Carleman
