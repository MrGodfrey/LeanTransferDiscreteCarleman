module

public import Carleman.Spatial.ConvexSupportContraction
public import Carleman.Spatial.CompactLipschitzSobolev

/-! Actual inward contractions of boundary-zero nodal functions are
compactly supported strictly inside the convex domain and remain genuine H¹. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace Carleman
variable {d : ℕ}

theorem centeredDilation_lipschitz (a : SpatialCoordinates d) (r : ℝ) (hr : r ≠ 0) :
    LipschitzWith ‖r‖₊ (centeredDilation a r hr) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,dist_eq_norm]
  have he : centeredDilation a r hr x - centeredDilation a r hr y = r • (x-y) := by
    change (a+r • (x-a)) - (a+r • (y-a)) = r • (x-y)
    module
  rw [he,norm_smul]
  rfl

theorem contractedFunction_lipschitz (a : SpatialCoordinates d) (r : ℝ) (hr : r ≠ 0)
    {f : SpatialCoordinates d → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f) :
    LipschitzWith (C*‖r⁻¹‖₊) (contractedFunction a r hr f) :=
  hf.comp (centeredDilation_lipschitz a r⁻¹ (inv_ne_zero hr))

def contractedSobolevJet (a : SpatialCoordinates d) (r : ℝ) (hr : r ≠ 0)
    {f : SpatialCoordinates d → ℝ} {C : ℝ≥0} (hC : LipschitzWith C f) (hf : HasCompactSupport f) :
    WeakSobolevJet d 1 volume Set.univ :=
  compactLipschitzSobolevJet (contractedFunction_lipschitz a r hr hC)
    (contractedFunction_compact a r hr hf)

theorem contractedSobolevJet_value_ae (a : SpatialCoordinates d) (r : ℝ) (hr : r ≠ 0)
    {f : SpatialCoordinates d → ℝ} {C : ℝ≥0} (hC : LipschitzWith C f) (hf : HasCompactSupport f) :
    WeakSobolevJet.value (contractedSobolevJet a r hr hC hf) =ᵐ[volume] contractedFunction a r hr f := by
  rw [contractedSobolevJet,compactLipschitzSobolevJet_value]
  exact compactLipschitzLp_ae _ _

namespace SimplicialPartition
variable {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)} (M : SimplicialPartition S ι)

omit [Fintype ι] in
theorem nodalFunction_tsupport_subset (f : SpatialCoordinates d → ℝ) :
    tsupport (M.nodalFunction f) ⊆ closure S := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  exact hx (M.nodalFunction_zero_outside f hn)

theorem nodal_contraction_buffer (hS : IsOpen S) (hconv : Convex ℝ S)
    {a : SpatialCoordinates d} (ha : a ∈ S) {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (f : SpatialCoordinates d → ℝ) :
    ∃ δ > (0 : ℝ), Metric.cthickening δ
      (tsupport (contractedFunction a r hr.ne' (M.nodalFunction f))) ⊆ S :=
  contractedFunction_buffer hS hconv ha hr hr1
    (M.nodalFunction_hasCompactSupport f) (M.nodalFunction_tsupport_subset f)

def nodalContractedSobolevJet (hS : IsOpen S) (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k) = 0)
    (a : SpatialCoordinates d) (r : ℝ) (hr : r ≠ 0) : WeakSobolevJet d 1 volume Set.univ :=
  contractedSobolevJet a r hr (M.nodalFunction_lipschitzWith hS hM hB f hf)
    (M.nodalFunction_hasCompactSupport f)

theorem nodalContractedSobolevJet_value_ae (hS : IsOpen S) (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k) = 0)
    (a : SpatialCoordinates d) (r : ℝ) (hr : r ≠ 0) :
    WeakSobolevJet.value (M.nodalContractedSobolevJet hS hM hB f hf a r hr) =ᵐ[volume]
      contractedFunction a r hr (M.nodalFunction f) := contractedSobolevJet_value_ae _ _ _ _ _

end SimplicialPartition
end Carleman
