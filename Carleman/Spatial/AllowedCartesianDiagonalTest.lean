module

public import Carleman.Spatial.CartesianDiagonalTest
public import Carleman.Spatial.AllowedCartesianKuhnStability
public import Carleman.Spatial.SimplicialProductResidual

/-! The original diagonal test has the full allowed-weight mass equivalence,
and its true reconstruction residual is exactly the nodal product residual. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem cartesianSquaredWeightTest_reconstruction (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (σ : SpatialCoordinates d → ℝ) (f : CartesianInteriorIndex N → ℝ) :
    cartesianKuhnReconstruction o δ hδ N (cartesianSquaredWeightTest o δ N σ f)=
      (cartesianKuhnPartition o δ hδ N).nodalFunction
        (fun x => (σ x)^2*cartesianKuhnReconstruction o δ hδ N f x) :=
  cartesianKuhnReconstruction_multiplier_nodal o δ hδ N (fun x => (σ x)^2) f

theorem cartesianSquaredWeightTest_residual (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (σ : SpatialCoordinates d → ℝ) (f : CartesianInteriorIndex N → ℝ) :
    (cartesianKuhnPartition o δ hδ N).nodalProductResidual (fun x => (σ x)^2) (cartesianInteriorData o δ N f)=
      fun x => (σ x)^2*cartesianKuhnReconstruction o δ hδ N f x-
        cartesianKuhnReconstruction o δ hδ N (cartesianSquaredWeightTest o δ N σ f) x := by
  funext x
  unfold SimplicialPartition.nodalProductResidual
  rw [cartesianKuhnReconstruction_eq_nodal,cartesianKuhnReconstruction_eq_nodal]
  change _-_=_-(cartesianKuhnPartition o δ hδ N).nodalFunction
    (cartesianInteriorData o δ N (cartesianNodalMultiplier o δ N (fun y => (σ y)^2) f)) x
  rw [cartesianInteriorData_multiplier]

theorem allowed_weight_cartesian_test_norm
    (hS : IsOpen S) (hc : Convex ℝ S) (hcompact : IsCompact (closure S))
    (ρ : SpatialProfile (volume.restrict S)) (hρ : ContDiffOn ℝ 1 ρ.value (closure S)) :
    ∃ C > 0, ∀ (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
      (hTS : openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j) ⊆ S)
      (h : ℝ), 0 < h → (∀ j, δ j ≤ h) →
      ∀ (w : TimeWeight) (τ t η : ℝ), |η|=1 → h*w.q t ≤ 1 →
      ∀ f : CartesianInteriorIndex N → ℝ,
      let σ := (((ρ.scaled η).multiplier w τ t).onSubdomain hTS)
      cartesianPhysicalInner δ N f (cartesianSquaredWeightTest o δ N σ.value f) ≤
        C*(σ.seminorm (cartesianKuhnReconstructionLp o δ hδ N f))^2 ∧
      (σ.seminorm (cartesianKuhnReconstructionLp o δ hδ N f))^2 ≤
        C*cartesianPhysicalInner δ N f (cartesianSquaredWeightTest o δ N σ.value f) := by
  obtain ⟨C,hC,hbound⟩ := allowed_weight_cartesianKuhn_stability hS hc hcompact ρ hρ
  refine ⟨C,hC,?_⟩
  intro o δ hδ N hTS h hh hstep w τ t η hη hsmall f
  dsimp only
  rw [cartesianSquaredWeightTest_pairing]
  have hb := hbound o δ hδ N hTS h hh hstep w τ t η hη hsmall f
  exact ⟨hb.1,hb.2.1⟩

end Carleman
