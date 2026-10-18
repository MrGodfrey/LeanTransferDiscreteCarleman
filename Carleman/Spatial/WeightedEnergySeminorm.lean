module

public import Carleman.Spatial.ShiftedFormBounds

/-! The actual weighted Sobolev energy is a seminorm, obtained from the
Hilbert product of all weighted derivative fields. This permits the spatial
error analysis to use norm algebra without replacing N by an unrelated norm. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
namespace WeakSobolevJet
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
  {S : Set (SpatialCoordinates d)}

def weightedFieldMap (q : ℝ) (w : BoundedMultiplier ν) :
    WeakSobolevJet d m ν S →ₗ[ℝ] HilbertJetFields d m ν :=
  (WithLp.linearEquiv 2 ℝ (JetFields d m ν)).symm.toLinearMap.comp
    (LinearMap.pi fun k : Fin (m+1) => q^(m-k.val) • w.linearMap.comp (field k))

theorem weightedFieldMap_norm_sq {q : ℝ} (hq : 0 ≤ q) (w : BoundedMultiplier ν)
    (u : WeakSobolevJet d m ν S) :
    ‖weightedFieldMap q w u‖^2 = weightedSq q w u := by
  rw [PiLp.norm_sq_eq_of_L2, weightedSq_eq_sum_norm hq]
  rfl

def weightedSeminorm (q : ℝ) (w : BoundedMultiplier ν) :
    Seminorm ℝ (WeakSobolevJet d m ν S) :=
  (normSeminorm ℝ (HilbertJetFields d m ν)).comp (weightedFieldMap q w)

theorem weightedSeminorm_apply {q : ℝ} (hq : 0 ≤ q) (w : BoundedMultiplier ν)
    (u : WeakSobolevJet d m ν S) : weightedSeminorm q w u = weightedNorm q w u := by
  apply (sq_eq_sq₀ (apply_nonneg _ _) (weightedNorm_nonneg q w u)).mp
  exact (weightedFieldMap_norm_sq hq w u).trans (weightedNorm_sq q w u).symm

theorem weightedNorm_add_le {q : ℝ} (hq : 0 ≤ q) (w : BoundedMultiplier ν)
    (u v : WeakSobolevJet d m ν S) :
    weightedNorm q w (u+v) ≤ weightedNorm q w u + weightedNorm q w v := by
  simpa only [weightedSeminorm_apply hq] using map_add_le_add (weightedSeminorm q w) u v

theorem weightedNorm_sub_le {q : ℝ} (hq : 0 ≤ q) (w : BoundedMultiplier ν)
    (u v : WeakSobolevJet d m ν S) :
    weightedNorm q w (u-v) ≤ weightedNorm q w u + weightedNorm q w v := by
  simpa only [weightedSeminorm_apply hq] using map_sub_le_add (weightedSeminorm q w) u v

end WeakSobolevJet

variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {V : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d m ν S)

def conformingWeightedSeminorm (q : ℝ) (w : BoundedMultiplier ν) : Seminorm ℝ V :=
  (WeakSobolevJet.weightedSeminorm q w).comp (domainSobolevJet hS hν hV)

theorem conformingWeightedSeminorm_apply {q : ℝ} (hq : 0 ≤ q)
    (w : BoundedMultiplier ν) (v : V) :
    conformingWeightedSeminorm hS hν hV q w v = conformingWeightedNorm hS hν hV q w v :=
  WeakSobolevJet.weightedSeminorm_apply hq w _

end Carleman
