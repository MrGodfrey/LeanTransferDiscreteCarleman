module

public import Carleman.Weights.FullNodalWeakNorms
public import Carleman.Spatial.NodalMultiplierUniqueness

/-! The full weak residual estimates for the prescribed actual nodal data.
The interpolation operator is identified, not left as an existential test. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

set_option maxHeartbeats 800000 in
theorem allowed_prescribed_nodal_weak_norms
    {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hc : Convex ℝ S)
    (hcompact : IsCompact (closure S)) (ρ : SpatialProfile (volume.restrict S))
    (hρ : ContDiffOn ℝ 2 ρ.value (closure S)) {κ : ℝ} (hκ : 0 ≤ κ)
    [IsFiniteMeasure (volume.restrict S)] :
    ∃ C > (0:ℝ), ∀ {ι : Type*} [Fintype ι] (M : SimplicialPartition S ι),
    ∀ hM : M.FaceMatching, M.BoundaryFitted →
    ∀ (w : TimeWeight) (τ t η : ℝ), |η|=1 → M.maxDiameter*w.q t ≤ 1 →
    ∀ (a : ι → SpatialCoordinates d) (r : ι → ℝ),
      (∀ i, 0 < r i) → (∀ i, Metric.ball (a i) (r i) ⊆ M.cell i) →
      (∀ i, M.cellDiameter i ≤ κ*r i) →
    ∀ (u : WeakSobolevJet d 1 (volume.restrict S) S)
      (f : SpatialCoordinates d → ℝ),
      WeakSobolevJet.value u ∈ M.conformingSpace (dirichletSubspace S) →
      WeakSobolevJet.value u=M.nodalLp hS.measurableSet hM f →
    ∃ e : WeakSobolevJet d 1 (volume.restrict S) S,
      let σ := (ρ.scaled η).multiplier w τ t
      let ξ := (ρ.scaled (-η)).multiplier w (-τ) t
      let energy := (w.q t)^4*(σ.seminorm (WeakSobolevJet.value u))^2+
        (w.q t)^2*(σ.seminorm (WeakSobolevJet.field 1 u))^2
      WeakSobolevJet.value e=(σ.mul σ).map (WeakSobolevJet.value u)-
        M.nodalLp hS.measurableSet hM (fun x => (σ.mul σ).value x*f x) ∧
      (ξ.seminorm (WeakSobolevJet.value e))^2 ≤ C*M.maxDiameter^4*energy ∧
      (ξ.seminorm (WeakSobolevJet.field 1 e))^2 ≤ C*M.maxDiameter^2*energy := by
  obtain ⟨C,hC,hbound⟩ := allowedSquaredWeight_full_weak_residual hS hc hcompact hρ hκ
  refine ⟨C,hC,?_⟩
  intro ι _ M hM hB w τ t η hη hsmall a r hr hball hshape u f hu hf
  obtain ⟨g,e,hg,hval,he,_hI,hvalue,hgradient⟩ :=
    hbound M hM hB (w.q t) (w.lower t) τ η hη hsmall a r hr hball hshape u hu
  let σ := (ρ.scaled η).multiplier w τ t
  have hw : allowedSquaredWeight ρ.value (w.q t) τ η = (σ.mul σ).value := by
    funext x
    rw [allowedSquaredWeight_multiplier_value]
    change (σ.value x)^2=σ.value x*σ.value x
    ring
  have hmap : WeakSobolevJet.value e=(σ.mul σ).map (WeakSobolevJet.value u)-
      M.nodalLp hS.measurableSet hM (fun x => (σ.mul σ).value x*f x) := by
    rw [hw] at he
    have ht := M.nodalProductResidual_lp hS.measurableSet hM (σ.mul σ) g
      (WeakSobolevJet.value u) (WeakSobolevJet.value e) hval he
    rwa [M.nodalLp_multiplier_congr hS hc hM (σ.mul σ).value g f (hval.symm.trans hf)] at ht
  refine ⟨e,hmap,?_,?_⟩
  · rw [allowed_inverse_weight_sq_integral,allowed_weight_sq_integral,allowed_weight_sq_integral]
    simpa only [Real.norm_eq_abs,sq_abs] using hvalue
  · rw [allowed_inverse_weight_sq_integral,allowed_weight_sq_integral,allowed_weight_sq_integral]
    simpa only [Real.norm_eq_abs,sq_abs] using hgradient

end Carleman
