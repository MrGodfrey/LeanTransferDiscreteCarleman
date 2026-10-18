module

public import Carleman.Weights.FullWeakNodalResidual
public import Carleman.Weights.SquaredWeightNorm

/-! Genuine allowed-multiplier norms for a weak residual of the full original
conforming state, with an actual nodal test in the same Dirichlet space. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem allowed_full_nodal_weak_norms
    {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hc : Convex ℝ S)
    (hcompact : IsCompact (closure S)) (ρ : SpatialProfile (volume.restrict S))
    (hρ : ContDiffOn ℝ 2 ρ.value (closure S)) {κ : ℝ} (hκ : 0 ≤ κ)
    [IsFiniteMeasure (volume.restrict S)] :
    ∃ C > (0:ℝ), ∀ {ι : Type*} [Fintype ι] (M : SimplicialPartition S ι),
    M.FaceMatching → M.BoundaryFitted →
    ∀ (w : TimeWeight) (τ t η : ℝ), 1 ≤ w.q t → |η|=1 → M.maxDiameter*w.q t ≤ 1 →
    ∀ (a : ι → SpatialCoordinates d) (r : ι → ℝ),
      (∀ i, 0 < r i) → (∀ i, Metric.ball (a i) (r i) ⊆ M.cell i) →
      (∀ i, M.cellDiameter i ≤ κ*r i) →
    ∀ u : WeakSobolevJet d 1 (volume.restrict S) S,
      WeakSobolevJet.value u ∈ M.conformingSpace (dirichletSubspace S) →
    ∃ (I : Lp ℝ 2 (volume.restrict S)) (e : WeakSobolevJet d 1 (volume.restrict S) S),
      I ∈ M.conformingSpace (dirichletSubspace S) ∧
      let σ := (ρ.scaled η).multiplier w τ t
      let ξ := (ρ.scaled (-η)).multiplier w (-τ) t
      let energy := (w.q t)^4*(σ.seminorm (WeakSobolevJet.value u))^2+
        (w.q t)^2*(σ.seminorm (WeakSobolevJet.field 1 u))^2
      WeakSobolevJet.value e=(σ.mul σ).map (WeakSobolevJet.value u)-I ∧
      (ξ.seminorm (WeakSobolevJet.value e))^2 ≤ C*M.maxDiameter^4*energy ∧
      (ξ.seminorm (WeakSobolevJet.field 1 e))^2 ≤ C*M.maxDiameter^2*energy := by
  obtain ⟨C,hC,hbound⟩ := allowedSquaredWeight_full_weak_residual hS hc hcompact hρ hκ
  refine ⟨C,hC,?_⟩
  intro ι _ M hM hB w τ t η hq hη hsmall a r hr hball hshape u hu
  obtain ⟨f,e,hf,hval,he,hI,hvalue,hgradient⟩ :=
    hbound M hM hB (w.q t) hq τ η hη hsmall a r hr hball hshape u hu
  let σ := (ρ.scaled η).multiplier w τ t
  let I := M.nodalLp hS.measurableSet hM (fun x => allowedSquaredWeight ρ.value (w.q t) τ η x*f x)
  have hw : allowedSquaredWeight ρ.value (w.q t) τ η = (σ.mul σ).value := by
    funext x
    rw [allowedSquaredWeight_multiplier_value]
    change (σ.value x)^2=σ.value x*σ.value x
    ring
  have hmap : WeakSobolevJet.value e=(σ.mul σ).map (WeakSobolevJet.value u)-I := by
    rw [hw] at he
    simpa only [I,hw] using M.nodalProductResidual_lp hS.measurableSet hM (σ.mul σ) f
      (WeakSobolevJet.value u) (WeakSobolevJet.value e) hval he
  refine ⟨I,e,hI,hmap,?_,?_⟩
  · rw [allowed_inverse_weight_sq_integral,allowed_weight_sq_integral,allowed_weight_sq_integral]
    simpa only [Real.norm_eq_abs,sq_abs] using hvalue
  · rw [allowed_inverse_weight_sq_integral,allowed_weight_sq_integral,allowed_weight_sq_integral]
    simpa only [Real.norm_eq_abs,sq_abs] using hgradient

end Carleman
