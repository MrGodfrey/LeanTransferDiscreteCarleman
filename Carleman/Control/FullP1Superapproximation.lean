module

public import Carleman.Weights.FullProjectedSuperapproximation
public import Carleman.Control.GalerkinTestData

/-! The concrete full P1 spatial estimates discharge the original
GalerkinSuperapprox interface for the actual Pi_h(sigma² z) test. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman

theorem SpatialProfile.scaled_neg {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (ρ : SpatialProfile ν) (η : ℝ) : ρ.scaled (-η)=(ρ.scaled η).neg := by
  cases ρ
  simp only [scaled,neg,neg_mul,abs_neg,Pi.neg_def]

variable {d : ℕ}
set_option maxHeartbeats 1200000 in
theorem full_p1_galerkin_superapproximation
    {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hc : Convex ℝ S)
    (hcompact : IsCompact (closure S)) (ρ : SpatialProfile (volume.restrict S))
    (hρ : ContDiffOn ℝ 2 ρ.value (closure S))
    (κ c B γ : ℝ) (hκ : 0 < κ) (hcpos : 0 < c) (hBpos : 0 < B)
    (hγ : 1 ≤ γ) (hΓ : γ < p1GradingLimit d)
    [IsFiniteMeasure (volume.restrict S)] :
    ∃ δ > (0:ℝ), δ ≤ 1 ∧ ∃ C > (0:ℝ),
    ∀ {ι : Type*} [Fintype ι] (M : SimplicialPartition S ι),
    M.FaceMatching → M.BoundaryFitted →
    ∀ (a : ι → SpatialCoordinates d) (r ℓ : ι → ℝ),
      (∀ i, 0 < r i) → (∀ i, Metric.ball (a i) (r i) ⊆ M.cell i) →
      (∀ i, M.cellDiameter i ≤ κ*r i) → (∀ i, 0 < ℓ i) →
      (∀ i, c*M.cellDiameter i ≤ ℓ i) → (∀ i, ℓ i ≤ B*M.cellDiameter i) →
      (∀ i j, M.VertexNeighbors i j → ℓ j ≤ γ*ℓ i) →
    ∀ (w : TimeWeight), M.maxDiameter*w.max ≤ δ →
    ∀ (g : TimeGrid) (τ η : ℝ), |η|=1 →
    Physical.GalerkinSuperapprox hS (ae_restrict_mem hS.measurableSet) (dirichletSubspace_sobolev S)
      (M.conformingSpace (dirichletSubspace S)) (M.conformingSpace_le (dirichletSubspace S))
      g (ρ.scaled η) w τ C M.maxDiameter := by
  obtain ⟨δ,hδ,hd,C,hC,hbound⟩ := allowed_full_projected_superapproximation hS hc hcompact ρ hρ
    κ c B γ hκ hcpos hBpos hγ hΓ
  refine ⟨δ,hδ,hd,C,hC,?_⟩
  intro ι _ M hM hB a r ℓ hr hball hshape hℓ hlow hupp hg w hm g τ η hη t _ hw z
  let X := M.conformingSpace (dirichletSubspace S)
  let hX := M.conformingSpace_le (dirichletSubspace S)
  have hν : ∀ᵐ x ∂volume.restrict S, x ∈ S := ae_restrict_mem hS.measurableSet
  let hV := dirichletSubspace_sobolev S
  let σ := (ρ.scaled η).multiplier w τ t
  let u := domainSobolevJet hS hν hV (X.inclusion hX z)
  have huv : WeakSobolevJet.value u = (z : Lp ℝ 2 (volume.restrict S)) := domainSobolevJet_value hS hν hV (X.inclusion hX z)
  have hu : WeakSobolevJet.value u ∈ X := by
    rw [domainSobolevJet_value]
    exact z.property
  obtain ⟨e,he,henergy⟩ := hbound M hM hB a r ℓ hr hball hshape hℓ hlow hupp hg w hm τ t η hη u hu
  let v := X.inclusion hX (Physical.galerkinWeightedTest X (ρ.scaled η) w τ t z)-
    conformingWeight σ hw (conformingWeight σ hw (X.inclusion hX z))
  have hid : e=domainSobolevJet hS hν hV v := by
    apply WeakSobolevJet.value_injective hS hν
    rw [he,huv,domainSobolevJet_value]
    change (X.orthogonalProjectionOnto ((σ.mul σ).map (z : Lp ℝ 2 (volume.restrict S))) : Lp ℝ 2 (volume.restrict S))-
      (σ.mul σ).map (z : Lp ℝ 2 (volume.restrict S)) =
      (Physical.galerkinWeightedTest X (ρ.scaled η) w τ t z : Lp ℝ 2 (volume.restrict S))-
        σ.map (σ.map (z : Lp ℝ 2 (volume.restrict S)))
    rw [Physical.galerkinWeightedTest_apply,BoundedMultiplier.mul_map]
  rw [hid,SpatialProfile.scaled_neg] at henergy
  exact henergy

end Carleman
