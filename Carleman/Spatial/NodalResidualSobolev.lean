module

public import Carleman.Spatial.SupportedLipschitzProduct
public import Carleman.Spatial.SimplicialProductResidual
public import Carleman.Spatial.CompactLipschitzSobolev
public import Carleman.Spatial.SobolevRestriction

/-! The actual squared-weight nodal residual belongs to full weak H¹,
and its weak gradient is the genuine almost-everywhere classical derivative. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem compactLipschitz_restricted_jet_exists {f : SpatialCoordinates d → ℝ} {C : ℝ≥0}
    (hC : LipschitzWith C f) (hf : HasCompactSupport f) :
    ∃ u : WeakSobolevJet d 1 (volume.restrict S) S,
      WeakSobolevJet.value u =ᵐ[volume.restrict S] f ∧
      WeakSobolevJet.field 1 u =ᵐ[volume.restrict S]
        (fun x => derivativeOneFiber (fderiv ℝ f x)) := by
  let u := compactLipschitzSobolevJet hC hf
  refine ⟨WeakSobolevJet.restrictDomain S u,?_,?_⟩
  · rw [WeakSobolevJet.restrictDomain_value,compactLipschitzSobolevJet_value]
    exact (Physical.restrictRegionLp_ae S _).trans ((compactLipschitzLp_ae hC hf).filter_mono ae_restrict_le)
  · change Physical.restrictRegionLp S ((OperatorMultiplier.const derivativeOneFiber).map
      (compactLipschitzDerivativeLp hC hf)) =ᵐ[volume.restrict S] _
    filter_upwards [Physical.restrictRegionLp_ae S ((OperatorMultiplier.const derivativeOneFiber).map
      (compactLipschitzDerivativeLp hC hf)),
      (OperatorMultiplier.const_map_ae derivativeOneFiber (compactLipschitzDerivativeLp hC hf)).filter_mono ae_restrict_le,
      (compactLipschitzDerivativeLp_ae hC hf).filter_mono ae_restrict_le] with x hx hy hz
    rw [hx,hy,hz]

namespace SimplicialPartition
variable {ι : Type*} [Fintype ι] (M : SimplicialPartition S ι)

theorem squared_nodal_residual_weak_jet (hS : IsOpen S) (hc : Convex ℝ S)
    (hcompact : IsCompact (closure S)) (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    {ρ : SpatialCoordinates d → ℝ} (hρ : ContDiffOn ℝ 2 ρ (closure S))
    (q τ η : ℝ) (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k)=0) :
    ∃ e : WeakSobolevJet d 1 (volume.restrict S) S,
      WeakSobolevJet.value e =ᵐ[volume.restrict S] M.nodalProductResidual (allowedSquaredWeight ρ q τ η) f ∧
      WeakSobolevJet.field 1 e =ᵐ[volume.restrict S]
        (fun x => derivativeOneFiber (fderiv ℝ (M.nodalProductResidual (allowedSquaredWeight ρ q τ η) f) x)) := by
  let w := allowedSquaredWeight ρ q τ η
  have hz : ∀ i k, (M.simplex i).points k ∈ frontier S →
      w ((M.simplex i).points k)*f ((M.simplex i).points k)=0 := by
    intro i k hk
    rw [hf i k hk,mul_zero]
  obtain ⟨L,hL⟩ := M.squared_nodal_product_lipschitz hS hc hcompact hM hB hρ q τ η f hf
  have he : LipschitzWith (L+M.nodalLipschitzConstant (fun x => w x*f x)) (M.nodalProductResidual w f) :=
    hL.sub (M.nodalFunction_lipschitzWith hS hM hB (fun x => w x*f x) hz)
  have hs : HasCompactSupport (M.nodalProductResidual w f) :=
    (M.nodalFunction_hasCompactSupport f).mul_left.sub (M.nodalFunction_hasCompactSupport (fun x => w x*f x))
  exact compactLipschitz_restricted_jet_exists he hs

end SimplicialPartition
end Carleman
