module

public import Carleman.Geometry.ConvexCompactExhaustion
public import Carleman.Spatial.InteriorWeakPoincare
public import Carleman.Spatial.InwardSmoothDerivatives

/-! A single geometric choice of shrinking kernels remains inside the original
open convex domain at every inward image of its entire closure. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem exists_inward_mollifier_sequence (hS : IsOpen S) (hc : Convex ℝ S)
    (hb : Bornology.IsBounded S) {a : SpatialCoordinates d} (ha : a ∈ S) :
    ∃ φ : ℕ → ℕ, (∀ n, n ≤ φ n) ∧ Tendsto φ atTop atTop ∧
      ∀ n, ∀ x ∈ closure S, ∀ y ∈ tsupport (spatialMollifier d (φ n)).value,
        inwardRatio n • x+(1-inwardRatio n) • a-y ∈ S := by
  have hbuffer (n : ℕ) : ∃ N : ℕ, ∀ m ≥ N, ∀ x ∈ convexInnerCompact S a n,
      ∀ y ∈ tsupport (spatialMollifier d m).value, x-y ∈ S :=
    eventually_atTop.mp (compact_mollifier_eventually_inside hS
      (convexInnerCompact_compact hb a n) (convexInnerCompact_subset hS hc ha n))
  choose N hN using hbuffer
  let φ := fun n => max n (N n)
  have hle (n : ℕ) : n ≤ φ n := le_max_left _ _
  refine ⟨φ,hle,tendsto_atTop_mono hle tendsto_id,?_⟩
  intro n x hx y hy
  apply hN n (φ n) (le_max_right _ _) _ _ y hy
  refine ⟨x,hx,?_⟩
  change a+inwardRatio n • (x-a)=inwardRatio n • x+(1-inwardRatio n) • a
  module

end Carleman
