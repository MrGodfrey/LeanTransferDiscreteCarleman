module

public import Carleman.Spatial.NodalDirichletMembership

/-! Strong H1 approximation by inward contractions for actual compact
Lipschitz functions that are C1 off a null set. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal
namespace Carleman
variable {d : ℕ}

theorem inward_fderiv_tendsto_of_contDiffAt (a x : SpatialCoordinates d)
    {f : SpatialCoordinates d → ℝ} (hf : ContDiffAt ℝ 1 f x) :
    Tendsto (fun n => fderiv ℝ
      (contractedFunction a (inwardRatio n) (inwardRatio_pos n).ne' f) x)
      atTop (𝓝 (fderiv ℝ f x)) := by
  have he : ∀ᶠ n in atTop, fderiv ℝ
      (contractedFunction a (inwardRatio n) (inwardRatio_pos n).ne' f) x =
      (inwardRatio n)⁻¹ • fderiv ℝ f ((centeredDilation a (inwardRatio n) (inwardRatio_pos n).ne').symm x) := by
    filter_upwards [(inverse_inward_tendsto a x).eventually (hf.eventually (by simp))] with n hn
    rw [(contractedFunction_hasFDerivAt a _ _ (hn.differentiableAt (by simp)).hasFDerivAt).fderiv]
    ext y
    simp
  have hr : Tendsto (fun n => (inwardRatio n)⁻¹) atTop (𝓝 (1:ℝ)) := by
    simpa using inwardRatio_tendsto.inv₀ (by norm_num)
  have hder := (hf.continuousAt_fderiv (by norm_num)).tendsto.comp (inverse_inward_tendsto a x)
  simpa only [one_smul] using (hr.smul hder).congr' (he.mono fun _ hn => hn.symm)

theorem compactLipschitz_inward_tendsto_H1 {S : Set (SpatialCoordinates d)}
    (hS : IsOpen S) (hconv : Convex ℝ S) (hb : Bornology.IsBounded S)
    {a : SpatialCoordinates d} (ha : a ∈ S) {f : SpatialCoordinates d → ℝ} {C : ℝ≥0}
    (hC : LipschitzWith C f) (hf : HasCompactSupport f) (hsupp : tsupport f ⊆ closure S)
    (hreg : ∀ᵐ x ∂volume, ContDiffAt ℝ 1 f x) :
    Tendsto (fun n => contractedSobolevJet a (inwardRatio n) (inwardRatio_pos n).ne' hC hf)
      atTop (𝓝 (compactLipschitzSobolevJet hC hf)) := by
  obtain ⟨B,hbound⟩ := hf.exists_bound_of_continuous hC.continuous
  have hB : 0 ≤ B := (norm_nonneg (f 0)).trans (hbound 0)
  apply compactLipschitzSobolevJet_tendsto
    (fun n => contractedFunction_lipschitz a _ _ hC) hC
    (fun n => contractedFunction_compact a _ _ hf) hf
    (closure S) hb.isCompact_closure
    (fun n => (contractedFunction_support_inside hS hconv ha
      (inwardRatio_pos n) (inwardRatio_lt_one n) hsupp).trans subset_closure)
    hsupp B hB
    (fun n x => hbound ((centeredDilation a (inwardRatio n) (inwardRatio_pos n).ne').symm x))
    hbound (2*(C:ℝ)) (by positivity)
  · intro n
    change (C:ℝ)*‖(inwardRatio n)⁻¹‖ ≤ 2*(C:ℝ)
    rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (inwardRatio_pos n))]
    nlinarith [inwardRatio_inv_le_two n,C.coe_nonneg]
  · linarith [C.coe_nonneg]
  · exact inwardFunction_tendsto a hC.continuous
  · exact hreg.mono fun x hx => inward_fderiv_tendsto_of_contDiffAt a x hx

theorem piecewiseSmooth_mem_dirichletJetSpace {S : Set (SpatialCoordinates d)}
    (hS : IsOpen S) (hconv : Convex ℝ S) (hb : Bornology.IsBounded S)
    {a : SpatialCoordinates d} (ha : a ∈ S) {f : SpatialCoordinates d → ℝ} {C : ℝ≥0}
    (hC : LipschitzWith C f) (hf : HasCompactSupport f) (hsupp : tsupport f ⊆ closure S)
    (hreg : ∀ᵐ x ∂volume, ContDiffAt ℝ 1 f x) :
    WeakSobolevJet.restrictDomain S (compactLipschitzSobolevJet hC hf) ∈ dirichletJetSpace S := by
  have ht := WeakSobolevJet.restrictDomain_tendsto (S := S)
    (compactLipschitz_inward_tendsto_H1 hS hconv hb ha hC hf hsupp hreg)
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto ht
  exact Filter.Eventually.of_forall fun n => compactLipschitz_mem_dirichletJetSpace hS
    (contractedFunction_lipschitz a _ _ hC) (contractedFunction_compact a _ _ hf)
    (contractedFunction_support_inside hS hconv ha (inwardRatio_pos n) (inwardRatio_lt_one n) hsupp)

end Carleman
