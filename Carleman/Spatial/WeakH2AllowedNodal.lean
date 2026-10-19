module

public import Carleman.Spatial.WeakH2WeightedNodal
public import Carleman.Spatial.ConformingAllowedInverse

/-! The original allowed weights, both signs and every power and time,
in the full weak H²∩H¹₀ nodal interpolation estimates. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman

set_option maxHeartbeats 800000 in
theorem weak_h2_allowed_nodal_approximation {d : ℕ} (hd : d ≤ 3)
    {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hc : Convex ℝ S)
    (hcompact : IsCompact (closure S)) [IsFiniteMeasure (volume.restrict S)]
    (ρ : SpatialProfile (volume.restrict S)) (hρ : ContDiffOn ℝ 1 ρ.value (closure S))
    (κ B : ℝ) (hB : 0 < B) :
    ∃ C > (0:ℝ), ∀ (ι : Type*) [Fintype ι] (M : SimplicialPartition S ι)
      (hM : M.FaceMatching), M.BoundaryFitted →
    ∀ (a : ι → SpatialCoordinates d) (r ℓ : ι → ℝ),
      (∀ i, 0 < r i) → (∀ i, 0 < ℓ i) →
      (∀ i, Metric.ball (a i) (r i) ⊆ M.cell i) →
      (∀ i, M.cellDiameter i ≤ κ*r i) → (∀ i, M.cellDiameter i ≤ B*ℓ i) →
    ∀ (u : WeakSobolevJet d 2 (volume.restrict S) S),
      WeakSobolevJet.value u ∈ dirichletSubspace S →
    ∃ (f : SpatialCoordinates d → ℝ) (e : WeakSobolevJet d 1 (volume.restrict S) S),
      ContinuousOn f (closure S) ∧ f =ᵐ[volume.restrict S] WeakSobolevJet.value u ∧
      (∀ x ∈ frontier S, f x=0) ∧
      M.nodalLp hS.measurableSet hM f ∈ M.conformingSpace (dirichletSubspace S) ∧
      e ∈ dirichletJetSpace S ∧
      WeakSobolevJet.value e=WeakSobolevJet.value u-M.nodalLp hS.measurableSet hM f ∧
    ∀ (w : TimeWeight) (τ t η : ℝ), |η|=1 → M.maxDiameter*w.q t ≤ 1 →
      let σ := (ρ.scaled η).multiplier w τ t
      σ.seminorm (WeakSobolevJet.value e) ≤
        C*(M.cellWeight (fun i => (ℓ i)^2) σ).seminorm (WeakSobolevJet.field 2 u) ∧
      σ.seminorm (WeakSobolevJet.field 1 e)+(M.inverseWeight ℓ σ).seminorm (WeakSobolevJet.value e) ≤
        C*(M.cellWeight ℓ σ).seminorm (WeakSobolevJet.field 2 u) := by
  obtain ⟨L,hL,hLip⟩ := smooth_profile_lipschitz hS hc hcompact hρ
  obtain ⟨C,hC,hbound⟩ := weak_h2_weighted_nodal_approximation d hd κ B (Real.exp L) hB (Real.exp_pos L)
  refine ⟨C,hC,?_⟩
  intro ι _ M hM hBnd a r ℓ hr hℓ hball hshape hscale u hu
  obtain ⟨f,e,hf,hfu,hzero,hI,he,hev,hweight⟩ := hbound ι S M hS hc
    (hcompact.isBounded.subset subset_closure) hM hBnd a r ℓ hr hℓ hball hshape hscale u hu
  refine ⟨f,e,hf,hfu,hzero,hI,he,hev,?_⟩
  intro w τ t η hη hm
  let σ := (ρ.scaled η).multiplier w τ t
  let xK : ι → SpatialCoordinates d := fun i => (M.simplex i).points 0
  have hxK (i : ι) : xK i ∈ M.cell i := subset_convexHull ℝ _ (Set.mem_range_self 0)
  apply hweight σ (fun i => σ.value (xK i)) (fun i => ρ.scaled_multiplier_pos η w τ t (xK i))
  intro i
  filter_upwards [ae_restrict_mem (simplicialCell_measurable (M.simplex i).points)] with x hx
  exact M.allowedWeight_cell_comparison ρ (zero_le_one.trans hL) hLip w τ t η hη hm i hx (hxK i)

end Carleman
