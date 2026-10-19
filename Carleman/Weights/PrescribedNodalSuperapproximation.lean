module

public import Carleman.Weights.PrescribedNodalWeakResidual
public import Carleman.Spatial.HeatNormSquare

/-! The original H¹ test residual norm for prescribed nodal interpolation.
The weak residual is taken with the paper's sign I(σ²u) − σ²u. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem WeakSobolevJet.weightedNorm_neg {m : ℕ} {ν : Measure (SpatialCoordinates d)}
    [IsFiniteMeasureOnCompacts ν] {S : Set (SpatialCoordinates d)}
    (q : ℝ) (σ : BoundedMultiplier ν) (u : WeakSobolevJet d m ν S) :
    weightedNorm q σ (-u)=weightedNorm q σ u := by
  unfold weightedNorm weightedSq
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [map_neg,map_neg_eq_map]

theorem heat_nodal_residual_norm_bound {ν : Measure (SpatialCoordinates d)}
    [IsFiniteMeasureOnCompacts ν] {S : Set (SpatialCoordinates d)}
    (q D C : ℝ) (hq : 0 ≤ q) (hD : 0 ≤ D) (hC : 0 ≤ C) (hsmall : D*q ≤ 1)
    (σ ξ : BoundedMultiplier ν) (u e : WeakSobolevJet d 1 ν S)
    (hzero : (ξ.seminorm (WeakSobolevJet.value e))^2 ≤ C*D^4*
      (q^4*(σ.seminorm (WeakSobolevJet.value u))^2+q^2*(σ.seminorm (WeakSobolevJet.field 1 u))^2))
    (hfirst : (ξ.seminorm (WeakSobolevJet.field 1 e))^2 ≤ C*D^2*
      (q^4*(σ.seminorm (WeakSobolevJet.value u))^2+q^2*(σ.seminorm (WeakSobolevJet.field 1 u))^2)) :
    WeakSobolevJet.weightedNorm q ξ e ≤ Real.sqrt (2*C)*(D*q*WeakSobolevJet.weightedNorm q σ u) := by
  let U := WeakSobolevJet.weightedNorm q σ u
  have hU : 0 ≤ U := WeakSobolevJet.weightedNorm_nonneg _ _ _
  have he : q^4*(σ.seminorm (WeakSobolevJet.value u))^2+q^2*(σ.seminorm (WeakSobolevJet.field 1 u))^2=q^2*U^2 := by
    dsimp only [U]
    rw [WeakSobolevJet.heat_weightedNorm_sq]
    ring
  rw [he] at hzero hfirst
  have hdq : D^2*q^2 ≤ 1 := by
    have ht := pow_le_pow_left₀ (mul_nonneg hD hq) hsmall 2
    simpa only [mul_pow,one_pow] using ht
  have hz : q^2*(ξ.seminorm (WeakSobolevJet.value e))^2 ≤ C*D^2*(q^2*U^2) := by
    calc
      _ ≤ q^2*(C*D^4*(q^2*U^2)) := mul_le_mul_of_nonneg_left hzero (sq_nonneg _)
      _ = (D^2*q^2)*(C*D^2*(q^2*U^2)) := by ring
      _ ≤ 1*(C*D^2*(q^2*U^2)) := mul_le_mul_of_nonneg_right hdq (by positivity)
      _ = _ := one_mul _
  apply nonneg_le_sqrt_mul_of_sq_le (WeakSobolevJet.weightedNorm_nonneg _ _ _) (by positivity)
    (mul_nonneg (mul_nonneg hD hq) hU)
  calc
    _ = q^2*(ξ.seminorm (WeakSobolevJet.value e))^2+(ξ.seminorm (WeakSobolevJet.field 1 e))^2 :=
      WeakSobolevJet.heat_weightedNorm_sq q ξ e
    _ ≤ C*D^2*(q^2*U^2)+C*D^2*(q^2*U^2) := add_le_add hz hfirst
    _ = _ := by ring

set_option maxHeartbeats 800000 in
theorem allowed_prescribed_nodal_superapproximation
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
      WeakSobolevJet.value e=M.nodalLp hS.measurableSet hM (fun x => (σ.mul σ).value x*f x)-
        (σ.mul σ).map (WeakSobolevJet.value u) ∧
      WeakSobolevJet.weightedNorm (w.q t) ξ e ≤
        C*M.maxDiameter*w.max*WeakSobolevJet.weightedNorm (w.q t) σ u := by
  obtain ⟨C,hC,hbound⟩ := allowed_prescribed_nodal_weak_norms hS hc hcompact ρ hρ hκ
  refine ⟨Real.sqrt (2*C),Real.sqrt_pos.mpr (by positivity),?_⟩
  intro ι _ M hM hB w τ t η hη hsmall a r hr hball hshape u f hu hf
  obtain ⟨e,he,hzero,hfirst⟩ := hbound M hM hB w τ t η hη hsmall a r hr hball hshape u f hu hf
  let σ := (ρ.scaled η).multiplier w τ t
  let ξ := (ρ.scaled (-η)).multiplier w (-τ) t
  refine ⟨-e,?_,?_⟩
  · rw [map_neg,he,neg_sub]
  · rw [WeakSobolevJet.weightedNorm_neg]
    have hb := heat_nodal_residual_norm_bound (w.q t) M.maxDiameter C (w.nonneg t)
      M.maxDiameter_nonneg hC.le hsmall σ ξ u e hzero hfirst
    calc
      _ ≤ Real.sqrt (2*C)*(M.maxDiameter*w.q t*WeakSobolevJet.weightedNorm (w.q t) σ u) := hb
      _ ≤ Real.sqrt (2*C)*(M.maxDiameter*w.max*WeakSobolevJet.weightedNorm (w.q t) σ u) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (w.upper t) M.maxDiameter_nonneg)
          (WeakSobolevJet.weightedNorm_nonneg _ _ _)
      _ = _ := by ring

end Carleman
