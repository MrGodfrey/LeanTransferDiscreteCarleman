module

public import Carleman.Spatial.CartesianKuhnHatSupport
public import Carleman.Spatial.AllowedCartesianDiagonalTest
public import Mathlib.Topology.MetricSpace.Thickening

/-! Actual Cartesian node restriction and reconstruction locality on the
inner observation region, with a mesh threshold from compact containment. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

def cartesianObservedState (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (ω : Set (SpatialCoordinates d)) :
    (CartesianInteriorIndex N → ℝ) →ₗ[ℝ] (CartesianInteriorIndex N → ℝ) :=
  cartesianNodalMultiplier o δ N (ω.indicator (fun _ => (1:ℝ)))

theorem cartesianObservedState_apply (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (ω : Set (SpatialCoordinates d)) (f : CartesianInteriorIndex N → ℝ)
    (a : CartesianInteriorIndex N) :
    cartesianObservedState o δ N ω f a=if cartesianInteriorPoint o δ N a ∈ ω then f a else 0 := by
  classical
  change ω.indicator (fun _ => (1:ℝ)) (cartesianInteriorPoint o δ N a)*f a=_
  by_cases ha : cartesianInteriorPoint o δ N a ∈ ω <;> simp [ha]

theorem cartesianKuhnHat_support_dist (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (h : ℝ) (hh : 0 < h) (hstep : ∀ j, δ j ≤ h)
    (a : CartesianInteriorIndex N) {x : SpatialCoordinates d}
    (hx : cartesianKuhnHat o δ hδ N (cartesianInteriorLatticeIndex N a) x ≠ 0) :
    dist (cartesianInteriorPoint o δ N a) x ≤ (d:ℝ)*h := by
  obtain ⟨i,hi⟩ := mem_iUnion.mp (cartesianKuhnHat_support_subset o δ hδ N _ hx)
  by_cases hn : cartesianGridPoint o δ (cartesianInteriorLatticeIndex N a) ∈
      Set.range (cartesianFiniteSimplex o δ hδ N i).points
  · rw [ite_eq_left hn] at hi
    obtain ⟨k,hk⟩ := hn
    apply cartesianKuhnSimplex_dist_le o δ hδ _ i.2 h hh hstep _ hi
    change cartesianGridPoint o δ (cartesianInteriorLatticeIndex N a) ∈ _
    rw [← hk]
    exact subset_convexHull ℝ _ (Set.mem_range_self k)
  · simp only [ite_eq_right hn,mem_empty_iff_false] at hi

theorem cartesianKuhnReconstruction_observed_eq
    (ω₀ ω : Set (SpatialCoordinates d)) (hcompact : IsCompact (closure ω₀))
    (hω : IsOpen ω) (hinc : closure ω₀ ⊆ ω) :
    ∃ h₀ > (0:ℝ), ∀ (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
      (h : ℝ), 0 < h → h ≤ h₀ → (∀ j, δ j ≤ h) →
    ∀ (f : CartesianInteriorIndex N → ℝ),
      EqOn (cartesianKuhnReconstruction o δ hδ N f)
        (cartesianKuhnReconstruction o δ hδ N (cartesianObservedState o δ N ω f)) ω₀ := by
  classical
  obtain ⟨r,hr,hbuffer⟩ := hcompact.exists_cthickening_subset_open hω hinc
  refine ⟨r/(d+1:ℝ),by positivity,?_⟩
  intro o δ hδ N h hh hsmall hstep f x hx
  unfold cartesianKuhnReconstruction
  apply Finset.sum_congr rfl
  intro a _
  rw [cartesianObservedState_apply]
  by_cases ha : cartesianInteriorPoint o δ N a ∈ ω
  · rw [ite_eq_left ha]
  · rw [ite_eq_right ha,zero_mul]
    have hz : cartesianKuhnHat o δ hδ N (cartesianInteriorLatticeIndex N a) x=0 := by
      by_contra hn
      apply ha
      apply hbuffer
      apply Metric.mem_cthickening_of_dist_le _ x r _ (subset_closure hx)
      have hd := cartesianKuhnHat_support_dist o δ hδ N h hh hstep a hn
      have hs : (d+1:ℝ)*h ≤ r := by
        simpa only [mul_comm] using (le_div_iff₀ (by positivity : (0:ℝ) < d+1)).mp hsmall
      nlinarith
    rw [hz,mul_zero]

end Carleman
