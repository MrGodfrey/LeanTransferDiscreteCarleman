module

public import Carleman.Section4.CombinedUniform
public import Carleman.Transfer.SobolevBridges

/-! Exact identification of the Section 5 squared quantities with the actual
Section 4 Bochner and weak Sobolev norms. No comparison constants occur. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman.SpatialProfile
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {ν : Measure Ω} (ρ : SpatialProfile ν)

theorem timeSq_eq_bochnerL2Norm_sq (g : TimeGrid) (w : TimeWeight) (b : ℝ)
    (hq : AEStronglyMeasurable w.q g.timeMeasure) {u : ℝ → Lp E 2 ν}
    (hu : MemLp u 2 g.timeMeasure) :
    timeSq g w.q b (fun t => (ρ.multiplier w 0 t).seminorm) u =
      (bochnerL2Norm g.timeMeasure (fun t => (ρ.multiplier w (b/2) t).map (u t)))^2 := by
  rw [bochnerL2Norm_sq_integral (ρ.memLp_map w (b/2) hq hu)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    simpa only [zero_add,timeDensity,BoundedMultiplier.seminorm_apply] using ρ.density_eq_shifted_seminorm_sq w 0 b t (u t)

theorem nodeMap_l2Norm_sq_powerSq (g : TimeGrid) (w : TimeWeight) (b : ℝ)
    (u : g.Sequence (Lp E 2 ν)) :
    (g.l2Norm (ρ.nodeMap g w (b/2) u))^2 =
      g.powerSq (w.nodes g) b (fun i => (ρ.multiplier w 0 (g.nodeTime i)).seminorm) u := by
  rw [ρ.nodeMap_l2Norm,g.weightedNorm_sq]
  unfold TimeGrid.weightedSq TimeGrid.powerSq
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simpa only [zero_add,TimeWeight.nodes] using (ρ.density_eq_shifted_seminorm_sq w 0 b (g.nodeTime i) (u i)).symm

end Carleman.SpatialProfile
namespace Carleman.WeakSobolevJet
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
  {S : Set (SpatialCoordinates d)}

theorem spacetimeWeightedNorm_sq_powerSum (g : TimeGrid) (w : TimeWeight)
    (ρ : SpatialProfile ν) (b : ℝ) (hq : AEStronglyMeasurable w.q g.timeMeasure)
    {u : ℝ → WeakSobolevJet d n ν S} (hu : MemLp u 2 g.timeMeasure) :
    (spacetimeWeightedNorm g w.q (ρ.multiplier w (b/2)) u)^2 =
      ∑ k : Fin (n+1), timeSq g w.q (2*(n-k.val : ℕ)+b)
        (fun t => (ρ.multiplier w 0 t).seminorm.comp (field k)) u := by
  rw [spacetimeWeightedNorm_sq]
  unfold spacetimeWeightedSq
  apply Finset.sum_congr rfl
  intro k _
  have hf : MemLp (parameterTimeField w.q (ρ.multiplier w (b/2)) u k) 2 g.timeMeasure := by
    simpa only [one_mul] using memLp_parameterTimeField g w ρ (b/2) 1 hq hu k
  rw [bochnerL2Norm_sq_integral hf]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    change ‖parameterTimeField w.q (ρ.multiplier w (b/2)) u k t‖^2 = _
    rw [parameterTimeField_norm _ _ _ _ (w.nonneg t),mul_pow]
    change _ = w.q t^(2*(n-k.val : ℕ)+b)*((ρ.multiplier w 0 t).seminorm (field k (u t)))^2
    have hd := ρ.density_eq_shifted_seminorm_sq w 0 b t (field k (u t))
    simp only [zero_add] at hd
    rw [← hd,Real.rpow_add (w.pos t)]
    have he : w.q t^(2*(n-k.val : ℕ) : ℝ) = (w.q t^(n-k.val))^2 := by
      norm_cast
      ring
    rw [he]
    ring

end Carleman.WeakSobolevJet

namespace Carleman
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {a : CarlemanExponents} {V : Submodule ℝ (Lp ℝ 2 ν)}
  (hV : V ≤ sobolevSubspace d a.m ν S)
  {X F Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [AddCommGroup F] [Module ℝ F] [AddCommGroup Y] [Module ℝ Y]
  {Z : Fin a.m → Type*} [∀ j, NormedAddCommGroup (Z j)]
  [∀ j, InnerProductSpace ℝ (Z j)]
  (w : TimeWeight) (ρ : SpatialProfile ν)
  (P : ∀ j : Fin a.m, DifferentialExpression ν
      (fun k : Fin (a.m+1) => DerivativeFiber d k.val) (Z j) (j.val+1))
  (obs : Set (SpatialCoordinates d)) (hobs : MeasurableSet obs)
  (state : ℝ → Seminorm ℝ X) (load : ℝ → Seminorm ℝ F) (control : ℝ → Seminorm ℝ Y)
  (hstate : ∀ t v, state t v = 0 → v = 0)
  (hload : ∀ t v, load t v = 0 → v = 0)
  (hcontrol : ∀ t v, control t v = 0 → v = 0)

local notation "p" => sobolevGeometry hS hν hV w ρ P obs hobs state load control hstate hload hcontrol

variable {g : TimeGrid} (hq : AEStronglyMeasurable w.q g.timeMeasure)

include hq in
/-- The B4 graph square is the true weighted Sobolev space-time norm. -/
theorem sobolevGeometry_graphSq_eq (b : ℝ) {u : ℝ → V}
    (hu : MemLp (fun t => domainSobolevJet hS hν hV (u t)) 2 g.timeMeasure) :
    (p).graphSq g b u =
      (WeakSobolevJet.spacetimeWeightedNorm g w.q (ρ.multiplier w (b/2))
        (fun t => domainSobolevJet hS hν hV (u t)))^2 := by
  exact (WeakSobolevJet.spacetimeWeightedNorm_sq_powerSum g w ρ b hq hu).symm

end Carleman
