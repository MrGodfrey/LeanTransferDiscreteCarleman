module

public import Carleman.Spatial.CellwiseInverseWeight

/-! A genuine global weighted inverse estimate for every conforming P1 H¹
state. Geometric shape and local weight comparisons remain explicit. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman

theorem conforming_weighted_inverse (d : ℕ) (κ W : ℝ) (hκ : 0 < κ) (hW : 0 < W) :
    ∃ C > (0:ℝ), ∀ (ι : Type*) [Fintype ι] (S : Set (SpatialCoordinates d))
      (M : SimplicialPartition S ι), IsOpen S → Convex ℝ S →
    ∀ [IsFiniteMeasure (volume.restrict S)]
      (a : ι → SpatialCoordinates d) (r h : ι → ℝ),
      (∀ i, 0 < r i) → (∀ i, 0 < h i) →
      (∀ i, Metric.ball (a i) (r i) ⊆ M.cell i) → (∀ i, h i ≤ κ*r i) →
    ∀ (w : BoundedMultiplier (volume.restrict S)) (s : ι → ℝ),
      (∀ i, 0 < s i) →
      (∀ i, ∀ᵐ x ∂volume.restrict (M.cell i), |w.value x| ≤ W*s i ∧ s i ≤ W*|w.value x|) →
    ∀ (V : Submodule ℝ (Lp ℝ 2 (volume.restrict S)))
      (u : WeakSobolevJet d 1 (volume.restrict S) S),
      WeakSobolevJet.value u ∈ M.conformingSpace V →
      w.seminorm (WeakSobolevJet.field 1 u) ≤ C*(M.inverseWeight h w).seminorm (WeakSobolevJet.value u) := by
  obtain ⟨C,hC,hbound⟩ := simplex_weighted_inverse_integral d κ W hκ hW
  refine ⟨C,hC,?_⟩
  intro ι _ S M hS hc _ a r h hr hh hball hshape w s hs hw V u hu
  have hcell (i : ι) :
      (∫ x in M.cell i, |w.value x|^2*‖WeakSobolevJet.field 1 u x‖^2) ≤
      (C/h i)^2 * ∫ x in M.cell i, |w.value x|^2*‖WeakSobolevJet.value u x‖^2 := by
    obtain ⟨p,hup,hgp⟩ := M.conforming_local_polynomial hS hc V u hu i
    let wi := w.restrictMeasure (M.cell_measure_le_domain hS hc i)
    have hl := hbound (M.simplex i) (a i) (r i) (h i) (hr i) (hh i) (hball i) (hshape i)
      wi (s i) (hs i) (hw i) p
    change (∫ x in M.cell i, |w.value x|^2*‖derivativeOneFiber (fderiv ℝ p x)‖^2) ≤
      (C/h i)^2 * ∫ x in M.cell i, |w.value x|^2*‖p x‖^2 at hl
    convert hl using 1
    · apply integral_congr_ae
      filter_upwards [hgp] with x hx
      rw [hx]
    · congr 1
      apply integral_congr_ae
      filter_upwards [hup] with x hx
      rw [hx]
  have hsq : (w.seminorm (WeakSobolevJet.field 1 u))^2 ≤
      (C*(M.inverseWeight h w).seminorm (WeakSobolevJet.value u))^2 := by
    calc
      _ = ∑ i, ∫ x in M.cell i, |w.value x|^2*‖WeakSobolevJet.field 1 u x‖^2 := by
        rw [w.seminorm_sq_integral,M.integral_eq_sum_cells hS hc _ (w.integrable_density _)]
      _ ≤ ∑ i, (C/h i)^2 * ∫ x in M.cell i, |w.value x|^2*‖WeakSobolevJet.value u x‖^2 :=
        Finset.sum_le_sum (fun i _ => hcell i)
      _ = C^2 * ∑ i, ((h i)⁻¹)^2 * ∫ x in M.cell i, |w.value x|^2*‖WeakSobolevJet.value u x‖^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = C^2 * ((M.inverseWeight h w).seminorm (WeakSobolevJet.value u))^2 := by
        rw [M.inverseWeight_sq_sum hS hc h w]
      _ = _ := by ring
  exact (sq_le_sq₀ (apply_nonneg _ _) (by positivity)).mp hsq

end Carleman
