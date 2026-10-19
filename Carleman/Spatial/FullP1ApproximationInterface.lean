module

public import Carleman.Spatial.WeakH2ProjectionApproximation
public import Carleman.Control.GalerkinNumericalData
public import Carleman.Weights.PrescribedNodalSuperapproximation

/-! The original N3 interface on every H² Dirichlet domain subspace, for
the actual full conforming P1 projection and inclusion reconstruction. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman

set_option maxHeartbeats 1600000 in
theorem full_p1_weightedApproximation_interface {d : ℕ} (hdim : d ≤ 3)
    {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hc : Convex ℝ S)
    (hcompact : IsCompact (closure S)) [IsFiniteMeasure (volume.restrict S)]
    (ρ : SpatialProfile (volume.restrict S)) (hρ : ContDiffOn ℝ 1 ρ.value (closure S))
    (κ c B γ : ℝ) (hκ : 0 < κ) (hcpos : 0 < c) (hBpos : 0 < B)
    (hγ : 1 ≤ γ) (hΓ : γ < p1GradingLimit d) :
    ∃ δ > (0:ℝ), δ ≤ 1 ∧ ∃ C > (0:ℝ),
    ∀ (ι : Type*) [Fintype ι] (M : SimplicialPartition S ι),
      M.FaceMatching → M.BoundaryFitted →
    ∀ (a : ι → SpatialCoordinates d) (r ℓ : ι → ℝ),
      (∀ i, 0 < r i) → (∀ i, Metric.ball (a i) (r i) ⊆ M.cell i) →
      (∀ i, M.cellDiameter i ≤ κ*r i) → (∀ i, 0 < ℓ i) →
      (∀ i, c*M.cellDiameter i ≤ ℓ i) → (∀ i, ℓ i ≤ B*M.cellDiameter i) →
      (∀ i j, M.VertexNeighbors i j → ℓ j ≤ γ*ℓ i) →
    ∀ (D : Submodule ℝ (Lp ℝ 2 (volume.restrict S)))
      (hD : D ≤ sobolevSubspace d (2*1) (volume.restrict S) S)
      (hDV : D ≤ dirichletSubspace S) (w : TimeWeight) (g : TimeGrid) (τ η : ℝ),
      |η|=1 → M.maxDiameter*w.max ≤ δ →
      Section4.WeightedApproximation hS (ae_restrict_mem hS.measurableSet)
        (dirichletSubspace_sobolev S) hD hDV
        (Physical.conformingReconstruction (dirichletSubspace S)
          (M.conformingSpace (dirichletSubspace S)) (M.conformingSpace_le (dirichletSubspace S)))
        g (ρ.scaled η) w τ (C*M.maxDiameter) (C*M.maxDiameter^2) := by
  obtain ⟨δ,hδ,hδ1,C,hC,hbound⟩ := weak_h2_allowed_projection_approximation hdim hS hc hcompact ρ hρ
    κ c B γ hκ hcpos hBpos hγ hΓ
  refine ⟨δ,hδ,hδ1,C,hC,?_⟩
  intro ι _ M hM hBnd a r ℓ hr hball hshape hℓ hlow hupp hg D hD hDV w g τ η hη hm
  let hν := ae_restrict_mem (μ := volume) hS.measurableSet
  let hV := dirichletSubspace_sobolev S
  let X := M.conformingSpace (dirichletSubspace S)
  let R := Physical.conformingReconstruction (dirichletSubspace S) X (M.conformingSpace_le (dirichletSubspace S))
  have hpoint (t : ℝ) (v : D) :
      conformingWeightedNorm hS hν hV (w.q t) ((ρ.scaled η).multiplier w τ t)
        (Submodule.inclusion hDV v-R.Q (v : Lp ℝ 2 (volume.restrict S))) ≤
        (C*M.maxDiameter)*conformingParameterNorm hS hν hD (w.q t) ((ρ.scaled η).multiplier w τ t) v ∧
      ((ρ.scaled η).multiplier w τ t).seminorm
        ((v : Lp ℝ 2 (volume.restrict S))-R.RH (R.J (v : Lp ℝ 2 (volume.restrict S)))) ≤
        (C*M.maxDiameter^2)*conformingParameterNorm hS hν hD (w.q t) ((ρ.scaled η).multiplier w τ t) v := by
    let u := domainSobolevJet hS hν hD v
    let σ := (ρ.scaled η).multiplier w τ t
    have hu : WeakSobolevJet.value u ∈ dirichletSubspace S := by
      rw [domainSobolevJet_value]
      exact hDV v.property
    obtain ⟨E,_,hE,hbounds⟩ := hbound ι M hM hBnd a r ℓ hr hball hshape hℓ hlow hupp hg u hu
    obtain ⟨hzero,henergy⟩ := hbounds w hm τ t η hη
    have htop : σ.seminorm (WeakSobolevJet.field 2 u) ≤ WeakSobolevJet.parameterNorm (w.q t) σ u := by
      have ht := WeakSobolevJet.parameterNorm_component (w.nonneg t) σ u 2
      change (w.q t)^0*σ.seminorm (WeakSobolevJet.field 2 u) ≤ _ at ht
      simpa only [pow_zero,one_mul] using ht
    have he : -E=domainSobolevJet hS hν hV (Submodule.inclusion hDV v-R.Q (v : Lp ℝ 2 (volume.restrict S))) := by
      apply WeakSobolevJet.value_injective hS hν
      rw [map_neg,hE,domainSobolevJet_value,domainSobolevJet_value]
      change -((X.orthogonalProjectionOnto (v : Lp ℝ 2 (volume.restrict S)):Lp ℝ 2 (volume.restrict S))-(v:Lp ℝ 2 (volume.restrict S)))=
        (v:Lp ℝ 2 (volume.restrict S))-(X.orthogonalProjectionOnto (v:Lp ℝ 2 (volume.restrict S)):Lp ℝ 2 (volume.restrict S))
      abel
    constructor
    · change WeakSobolevJet.weightedNorm (w.q t) σ
        (domainSobolevJet hS hν hV (Submodule.inclusion hDV v-R.Q (v : Lp ℝ 2 (volume.restrict S)))) ≤ _
      rw [← he,WeakSobolevJet.weightedNorm_neg]
      exact henergy.trans (mul_le_mul_of_nonneg_left htop (by positivity [M.maxDiameter_nonneg]))
    · have hv : ((v:Lp ℝ 2 (volume.restrict S))-R.RH (R.J (v:Lp ℝ 2 (volume.restrict S)))) = -WeakSobolevJet.value E := by
        rw [hE,domainSobolevJet_value]
        change (v:Lp ℝ 2 (volume.restrict S))-(X.orthogonalProjectionOnto (v:Lp ℝ 2 (volume.restrict S)):Lp ℝ 2 (volume.restrict S))=
          -((X.orthogonalProjectionOnto (v:Lp ℝ 2 (volume.restrict S)):Lp ℝ 2 (volume.restrict S))-(v:Lp ℝ 2 (volume.restrict S)))
        abel
      rw [hv,map_neg_eq_map]
      exact hzero.trans (mul_le_mul_of_nonneg_left htop (by positivity))
  exact ⟨fun t _ v => (hpoint t v).1,fun t _ v => (hpoint t v).2⟩

end Carleman
