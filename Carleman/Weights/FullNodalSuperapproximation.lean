module

public import Carleman.Weights.FullNodalScaledNorms
public import Carleman.Spatial.HeatNormSquare

/-! The two original Step 3 nodal residual estimates, with the actual weak
Sobolev norm and a constant uniform in all allowed weights and full states. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

set_option maxHeartbeats 800000 in
theorem allowed_full_nodal_superapproximation
    {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hc : Convex ℝ S)
    (hcompact : IsCompact (closure S)) (ρ : SpatialProfile (volume.restrict S))
    (hρ : ContDiffOn ℝ 2 ρ.value (closure S)) {κ c : ℝ} (hκ : 0 ≤ κ) (hcpos : 0 < c)
    [IsFiniteMeasure (volume.restrict S)] :
    ∃ C > (0:ℝ), ∀ {ι : Type*} [Fintype ι] (M : SimplicialPartition S ι),
    M.FaceMatching → M.BoundaryFitted →
    ∀ (w : TimeWeight) (τ t η : ℝ), 1 ≤ w.q t → |η|=1 → M.maxDiameter*w.q t ≤ 1 →
    ∀ (a : ι → SpatialCoordinates d) (r ℓ : ι → ℝ),
      (∀ i, 0 < r i) → (∀ i, Metric.ball (a i) (r i) ⊆ M.cell i) →
      (∀ i, M.cellDiameter i ≤ κ*r i) →
      (∀ i, 0 < ℓ i) → (∀ i, c*M.cellDiameter i ≤ ℓ i) →
    ∀ u : WeakSobolevJet d 1 (volume.restrict S) S,
      WeakSobolevJet.value u ∈ M.conformingSpace (dirichletSubspace S) →
    ∃ (I : Lp ℝ 2 (volume.restrict S)) (e : WeakSobolevJet d 1 (volume.restrict S) S),
      I ∈ M.conformingSpace (dirichletSubspace S) ∧
      let σ := (ρ.scaled η).multiplier w τ t
      let ξ := (ρ.scaled (-η)).multiplier w (-τ) t
      let N := WeakSobolevJet.weightedNorm (w.q t) σ u
      WeakSobolevJet.value e=(σ.mul σ).map (WeakSobolevJet.value u)-I ∧
      ξ.seminorm (WeakSobolevJet.field 1 e)+
        (M.inverseWeight ℓ ξ).seminorm (WeakSobolevJet.value e) ≤ C*M.maxDiameter*w.max*N ∧
      w.q t*ξ.seminorm (WeakSobolevJet.value e) ≤ C*M.maxDiameter^2*w.max^2*N := by
  obtain ⟨C,hC,hbound⟩ := allowed_full_nodal_scaled_norms hS hc hcompact ρ hρ hκ hcpos
  refine ⟨2*Real.sqrt C,by positivity,?_⟩
  intro ι _ M hM hB w τ t η hq hη hsmall a r ℓ hr hball hshape hℓ hscale u hu
  obtain ⟨I,e,hI,hmap,hzero,hfirst,hmesh⟩ :=
    hbound M hM hB w τ t η hq hη hsmall a r ℓ hr hball hshape hℓ hscale u hu
  let σ := (ρ.scaled η).multiplier w τ t
  let ξ := (ρ.scaled (-η)).multiplier w (-τ) t
  let N := WeakSobolevJet.weightedNorm (w.q t) σ u
  have hN : 0 ≤ N := WeakSobolevJet.weightedNorm_nonneg _ _ _
  have henergy : (w.q t)^4*(σ.seminorm (WeakSobolevJet.value u))^2+
      (w.q t)^2*(σ.seminorm (WeakSobolevJet.field 1 u))^2 = (w.q t)^2*N^2 := by
    dsimp only [N]
    rw [WeakSobolevJet.heat_weightedNorm_sq]
    ring
  change (ξ.seminorm (WeakSobolevJet.value e))^2 ≤ C*M.maxDiameter^4*(_) at hzero
  change (ξ.seminorm (WeakSobolevJet.field 1 e))^2 ≤ C*M.maxDiameter^2*(_) at hfirst
  change ((M.inverseWeight ℓ ξ).seminorm (WeakSobolevJet.value e))^2 ≤ C*M.maxDiameter^2*(_) at hmesh
  rw [henergy] at hzero hfirst hmesh
  have hb0 : ξ.seminorm (WeakSobolevJet.value e) ≤ Real.sqrt C*(M.maxDiameter^2*w.q t*N) := by
    apply nonneg_le_sqrt_mul_of_sq_le (apply_nonneg _ _) hC.le (by positivity [w.nonneg t])
    convert hzero using 1
    ring
  have hb1 : ξ.seminorm (WeakSobolevJet.field 1 e) ≤ Real.sqrt C*(M.maxDiameter*w.q t*N) := by
    apply nonneg_le_sqrt_mul_of_sq_le (apply_nonneg _ _) hC.le
      (mul_nonneg (mul_nonneg M.maxDiameter_nonneg (w.nonneg t)) hN)
    convert hfirst using 1
    ring
  have hbm : (M.inverseWeight ℓ ξ).seminorm (WeakSobolevJet.value e) ≤ Real.sqrt C*(M.maxDiameter*w.q t*N) := by
    apply nonneg_le_sqrt_mul_of_sq_le (apply_nonneg _ _) hC.le
      (mul_nonneg (mul_nonneg M.maxDiameter_nonneg (w.nonneg t)) hN)
    convert hmesh using 1
    ring
  refine ⟨I,e,hI,hmap,?_,?_⟩
  · calc
      _ ≤ Real.sqrt C*(M.maxDiameter*w.q t*N)+Real.sqrt C*(M.maxDiameter*w.q t*N) := add_le_add hb1 hbm
      _ = 2*Real.sqrt C*M.maxDiameter*w.q t*N := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (w.upper t)
        (mul_nonneg (by positivity) M.maxDiameter_nonneg)) hN
  · calc
      _ ≤ w.q t*(Real.sqrt C*(M.maxDiameter^2*w.q t*N)) :=
        mul_le_mul_of_nonneg_left hb0 (w.nonneg t)
      _ = Real.sqrt C*M.maxDiameter^2*(w.q t)^2*N := by ring
      _ ≤ Real.sqrt C*M.maxDiameter^2*w.max^2*N :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (w.nonneg t) (w.upper t) 2) (by positivity)) hN
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith [Real.sqrt_nonneg C]) (sq_nonneg _)) (sq_nonneg _)) hN

end Carleman
