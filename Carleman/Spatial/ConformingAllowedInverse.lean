module

public import Carleman.Spatial.ConformingWeightedInverse
public import Carleman.Spatial.SimplicialAllowedComparison

/-! The paper's actual allowed weights in the full conforming P1 inverse
estimate. Constants precede all meshes, times, powers, signs and states. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman

theorem conforming_allowed_weight_inverse {d : ℕ} {S : Set (SpatialCoordinates d)}
    (hS : IsOpen S) (hc : Convex ℝ S) (hcompact : IsCompact (closure S))
    [IsFiniteMeasure (volume.restrict S)] (ρ : SpatialProfile (volume.restrict S))
    (hρ : ContDiffOn ℝ 1 ρ.value (closure S)) (κ B : ℝ) (hκ : 0 < κ) (hB : 0 < B) :
    ∃ C > (0:ℝ), ∀ (ι : Type*) [Fintype ι] (M : SimplicialPartition S ι)
      (a : ι → SpatialCoordinates d) (r ℓ : ι → ℝ),
      (∀ i, 0 < r i) → (∀ i, 0 < ℓ i) →
      (∀ i, Metric.ball (a i) (r i) ⊆ M.cell i) →
      (∀ i, M.cellDiameter i ≤ κ*r i) → (∀ i, ℓ i ≤ B*M.cellDiameter i) →
    ∀ (w : TimeWeight) (τ t η : ℝ), |η|=1 → M.maxDiameter*w.q t ≤ 1 →
    ∀ (V : Submodule ℝ (Lp ℝ 2 (volume.restrict S)))
      (u : WeakSobolevJet d 1 (volume.restrict S) S),
      WeakSobolevJet.value u ∈ M.conformingSpace V →
      ((ρ.scaled η).multiplier w τ t).seminorm (WeakSobolevJet.field 1 u) ≤
        C*(M.inverseWeight ℓ ((ρ.scaled η).multiplier w τ t)).seminorm (WeakSobolevJet.value u) := by
  obtain ⟨L,hL,hLip⟩ := smooth_profile_lipschitz hS hc hcompact hρ
  obtain ⟨C,hC,hbound⟩ := conforming_weighted_inverse d (B*κ) (Real.exp L)
    (mul_pos hB hκ) (Real.exp_pos L)
  refine ⟨C,hC,?_⟩
  intro ι _ M a r ℓ hr hℓ hball hshape hscale w τ t η hη hm V u hu
  let σ := (ρ.scaled η).multiplier w τ t
  let xK : ι → SpatialCoordinates d := fun i => (M.simplex i).points 0
  have hxK (i : ι) : xK i ∈ M.cell i := subset_convexHull ℝ _ (Set.mem_range_self 0)
  have hw (i : ι) : ∀ᵐ x ∂volume.restrict (M.cell i),
      |σ.value x| ≤ Real.exp L*σ.value (xK i) ∧ σ.value (xK i) ≤ Real.exp L*|σ.value x| := by
    filter_upwards [ae_restrict_mem (simplicialCell_measurable (M.simplex i).points)] with x hx
    exact M.allowedWeight_cell_comparison ρ (zero_le_one.trans hL) hLip w τ t η hη hm i hx (hxK i)
  exact hbound ι S M hS hc a r ℓ hr hℓ hball (M.cellScale_le_inball hB.le r ℓ hshape hscale)
    σ (fun i => σ.value (xK i)) (fun i => ρ.scaled_multiplier_pos η w τ t (xK i)) hw V u hu

end Carleman
