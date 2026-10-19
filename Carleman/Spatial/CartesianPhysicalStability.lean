module

public import Carleman.Spatial.CartesianPhysicalNorms

/-! The original reconstruction, load and test norm estimates in the same
physical norm and mass/load interfaces, with a uniform allowed-weight constant. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem cartesianReconstruction_norm_sq_bounds (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianPhysicalState δ hδ N) :
    (d+2:ℝ)⁻¹*‖f‖^2 ≤ ‖(cartesianReconstruction o δ hδ N).RH f‖^2 ∧
      ‖(cartesianReconstruction o δ hδ N).RH f‖^2 ≤ ‖f‖^2 := by
  rw [PhysicalFiniteSpace.norm_sq,cartesianReconstruction_RH]
  exact cartesianKuhnReconstructionLp_norm_sq_bounds o δ hδ N (fun a => f a)

theorem allowed_weight_cartesian_physical_stability
    (hS : IsOpen S) (hc : Convex ℝ S) (hcompact : IsCompact (closure S))
    (ρ : SpatialProfile (volume.restrict S)) (hρ : ContDiffOn ℝ 1 ρ.value (closure S)) :
    ∃ C > (0:ℝ), ∀ (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
      (hTS : openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j) ⊆ S) (h : ℝ),
      0 < h → (∀ j, δ j ≤ h) →
    ∀ (w : TimeWeight) (τ t η : ℝ), |η|=1 → h*w.q t ≤ 1 →
    ∀ f : CartesianPhysicalState δ hδ N,
      let σ := (((ρ.scaled η).multiplier w τ t).onSubdomain hTS)
      let r := cartesianReconstruction o δ hδ N
      let p := cartesianStateSeminorm o δ hδ N σ.value
      (p f)^2 ≤ C*(σ.seminorm (r.RH f))^2 ∧
      (σ.seminorm (r.RH f))^2 ≤ C*(p f)^2 ∧
      (σ.seminorm ((cartesianLoadInterface o δ hδ N).lift f))^2 ≤ C*(p f)^2 ∧
      inner ℝ f (cartesianPhysicalTest o δ hδ N ρ.value w τ η t f) ≤ C*(σ.seminorm (r.RH f))^2 ∧
      (σ.seminorm (r.RH f))^2 ≤ C*inner ℝ f (cartesianPhysicalTest o δ hδ N ρ.value w τ η t f) := by
  obtain ⟨C,hC,hbound⟩ := allowed_weight_cartesianKuhn_stability hS hc hcompact ρ hρ
  refine ⟨C,hC,?_⟩
  intro o δ hδ N hTS h hh hupper w τ t η hη hsmall f
  dsimp only
  let σ := (((ρ.scaled η).multiplier w τ t).onSubdomain hTS)
  have hb := hbound o δ hδ N hTS h hh hupper w τ t η hη hsmall (fun a => f a)
  dsimp only at hb
  rw [cartesianStateSeminorm_apply,cartesianPhysicalStateWeight_norm_sq,
    cartesianReconstruction_RH,cartesianLoadInterface_lift,cartesianPhysicalTest_pairing]
  exact ⟨hb.1,hb.2.1,hb.2.2,hb.1,hb.2.1⟩

end Carleman
