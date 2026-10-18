module

public import Carleman.Spatial.CompactLipschitzLimit
public import Carleman.Spatial.ContractionSequence

/-! The actual inward contractions of a boundary-zero conforming nodal
function converge to its genuine full-space H¹ jet. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)} (M : SimplicialPartition S ι)

include M in
theorem closure_isCompact : IsCompact (closure S) := by
  rw [← M.cells_union]
  exact isCompact_iUnion fun i => simplicialCell_compact (M.simplex i).points

theorem nodalCompactJet_eq (hS : IsOpen S) (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k) = 0) :
    compactLipschitzSobolevJet (M.nodalFunction_lipschitzWith hS hM hB f hf)
      (M.nodalFunction_hasCompactSupport f) = M.nodalGlobalSobolevJet hS hM hB f hf := by
  apply WeakSobolevJet.value_injective isOpen_univ (Filter.Eventually.of_forall fun _ => mem_univ _)
  rw [compactLipschitzSobolevJet_value,M.nodalGlobalSobolevJet_value]
  apply Lp.ext
  exact (compactLipschitzLp_ae _ _).trans (M.nodalGlobalLp_ae hS hM hB f hf).symm

theorem nodal_inward_tendsto_H1 (hS : IsOpen S) (hconv : Convex ℝ S)
    (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k) = 0)
    {a : SpatialCoordinates d} (ha : a ∈ S) :
    Tendsto (fun n => M.nodalContractedSobolevJet hS hM hB f hf a
      (inwardRatio n) (inwardRatio_pos n).ne') atTop
      (𝓝 (M.nodalGlobalSobolevJet hS hM hB f hf)) := by
  rw [← M.nodalCompactJet_eq hS hM hB f hf]
  let C := M.nodalLipschitzConstant f
  have hlip := M.nodalFunction_lipschitzWith hS hM hB f hf
  have hcomp := M.nodalFunction_hasCompactSupport f
  obtain ⟨B,hbound⟩ := hcomp.exists_bound_of_continuous hlip.continuous
  have hB0 : 0 ≤ B := (norm_nonneg (M.nodalFunction f 0)).trans (hbound 0)
  apply compactLipschitzSobolevJet_tendsto
    (fun n => contractedFunction_lipschitz a _ _ hlip) hlip
    (fun n => contractedFunction_compact a _ _ hcomp) hcomp
    (closure S) M.closure_isCompact
    (fun n => (contractedFunction_support_inside hS hconv ha
      (inwardRatio_pos n) (inwardRatio_lt_one n) (M.nodalFunction_tsupport_subset f)).trans subset_closure)
    (M.nodalFunction_tsupport_subset f) B hB0
    (fun n x => hbound ((centeredDilation a (inwardRatio n) (inwardRatio_pos n).ne').symm x))
    hbound (2*(C:ℝ)) (by positivity)
  · intro n
    change (C:ℝ)*‖(inwardRatio n)⁻¹‖ ≤ 2*(C:ℝ)
    rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (inwardRatio_pos n))]
    nlinarith [inwardRatio_inv_le_two n,C.coe_nonneg]
  · change (C:ℝ) ≤ 2*(C:ℝ)
    linarith [C.coe_nonneg]
  · exact inwardFunction_tendsto a hlip.continuous
  · exact M.nodal_inward_fderiv_tendsto_ae hM f a

end Carleman.SimplicialPartition
