module

public import Carleman.Continuous.SobolevGraph

/-! Restriction to lower Sobolev order preserves the actual scalar L² class.
Thus the original H^(2m) elliptic bound supplies the H^m bound used in transfer. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
namespace WeakSobolevJet
variable {d m n : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] {S : Set (SpatialCoordinates d)}

def truncate (h : m ≤ n) : WeakSobolevJet d n ν S →ₗ[ℝ] WeakSobolevJet d m ν S where
  toFun u := ⟨fun k => u.val ⟨k.val, lt_of_lt_of_le k.isLt (Nat.succ_le_succ h)⟩, by
    intro k α i
    exact u.property ⟨k.val, lt_of_lt_of_le k.isLt h⟩ α i⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem truncate_value (h : m ≤ n) (u : WeakSobolevJet d n ν S) :
    value (truncate h u) = value u := rfl

theorem norm_truncate_le (h : m ≤ n) (u : WeakSobolevJet d n ν S) :
    ‖truncate h u‖ ≤ ‖u‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
  intro k
  exact norm_le_pi_norm u.val ⟨k.val, lt_of_lt_of_le k.isLt (Nat.succ_le_succ h)⟩

end WeakSobolevJet

variable {d m n : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {D : Submodule ℝ (Lp ℝ 2 ν)}

omit [IsLocallyFiniteMeasure ν] in
theorem sobolevSubspace_mono (h : m ≤ n) :
    sobolevSubspace d n ν S ≤ sobolevSubspace d m ν S := by
  rintro v ⟨u, rfl⟩
  exact ⟨WeakSobolevJet.truncate h u, WeakSobolevJet.truncate_value h u⟩

theorem domainSobolevJet_norm_mono (h : m ≤ n)
    (hm : D ≤ sobolevSubspace d m ν S) (hn : D ≤ sobolevSubspace d n ν S) (v : D) :
    ‖domainSobolevJet hS hν hm v‖ ≤ ‖domainSobolevJet hS hν hn v‖ := by
  have he : domainSobolevJet hS hν hm v =
      WeakSobolevJet.truncate h (domainSobolevJet hS hν hn v) := by
    apply WeakSobolevJet.value_injective hS hν
    simp only [WeakSobolevJet.truncate_value, domainSobolevJet_value]
  rw [he]
  exact WeakSobolevJet.norm_truncate_le h _

/-- No extra H^m elliptic assumption is needed: A1 at order 2m implies it. -/
theorem elliptic_bound_lower_order (h : m ≤ n)
    (hm : D ≤ sobolevSubspace d m ν S) (hn : D ≤ sobolevSubspace d n ν S)
    (A : D →ₗ[ℝ] Lp ℝ 2 ν) (C : ℝ)
    (hell : ∀ v : D, ‖domainSobolevJet hS hν hn v‖ ≤ C*‖A v‖) :
    ∀ v : D, ‖domainSobolevJet hS hν hm v‖ ≤ C*‖A v‖ :=
  fun v => (domainSobolevJet_norm_mono hS hν h hm hn v).trans (hell v)

end Carleman
