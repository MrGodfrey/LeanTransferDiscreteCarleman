module

public import Carleman.Spatial.ConeCoordinateInterpolation
public import Carleman.Spatial.L2FiniteCover
public import Carleman.Geometry.LocalLipschitzCharts

/-! Finite-cover assembly of the actual coordinate interpolation estimate.
The positive constants are chosen from domain geometry before any state or
small scale is supplied. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem finite_cones_common_height (P : Finset (InwardConePatch S)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ P, δ ≤ p.height := by
  classical
  induction P using Finset.induction_on with
  | empty => exact ⟨1,zero_lt_one,by simp⟩
  | @insert p P _ ih =>
    obtain ⟨δ,hδ,hd⟩ := ih
    refine ⟨min p.height δ,lt_min p.height_pos hδ,?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hd q hq)

theorem finite_cones_coordinate_interpolation (hS : IsOpen S)
    (P : Finset (InwardConePatch S)) (hcover : S ⊆ ⋃ p ∈ P, p.region)
    {δ : ℝ} (_hδ : 0 < δ) (hheight : ∀ p ∈ P, δ ≤ p.height) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ t : ℝ, 0 < t → t ≤ δ →
      ∀ (u : Lp ℝ 2 ((volume : Measure (SpatialCoordinates d)).restrict S))
        (v : Fin d → Lp ℝ 2 (volume.restrict S))
        (w : Fin d → Fin d → Lp ℝ 2 (volume.restrict S)),
      (∀ i, IsWeakSpatialDerivative (volume.restrict S) S
        (EuclideanSpace.basisFun (Fin d) ℝ i) u (v i)) →
      (∀ i j, IsWeakSpatialDerivative (volume.restrict S) S
        (EuclideanSpace.basisFun (Fin d) ℝ j) (v i) (w i j)) →
      ∀ B : ℝ, 0 ≤ B → (∀ i j, ‖w i j‖ ≤ B) → ∀ i, ‖v i‖ ≤ K*(‖u‖/t+t*B) := by
  classical
  let K := 1+∑ p : P, (4+coneCoordinateConstant p.val)
  have hK : 1 ≤ K := by
    have : 0 ≤ ∑ p : P, (4+coneCoordinateConstant p.val) :=
      Finset.sum_nonneg fun p _ => by linarith [coneCoordinateConstant_nonneg p.val]
    change 1 ≤ 1+∑ p : P, (4+coneCoordinateConstant p.val)
    linarith
  refine ⟨K,hK,?_⟩
  intro t ht htd u v w hf hs B hB hb i
  have hc : ∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)).restrict S,
      ∃ p : P, x ∈ p.val.region := by
    filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
    obtain ⟨p,hp,hx⟩ := mem_iUnion₂.mp (hcover hx)
    exact ⟨⟨p,hp⟩,hx⟩
  have he := bochnerL2Norm_finite_cover (Lp.memLp (v i)) (fun p : P => p.val.region)
    (fun p => p.val.open_region.measurableSet) hc
  rw [bochnerL2Norm_coe] at he
  have hlocal (p : P) : bochnerL2Norm ((volume.restrict S).restrict p.val.region) (v i) ≤
      (4+coneCoordinateConstant p.val)*(‖u‖/t+t*B) := by
    rw [Measure.restrict_restrict p.val.open_region.measurableSet]
    have hb' := weak_cone_coordinate_interpolation hS p.val ht (htd.trans (hheight p.val p.property)) hf hs hB hb i
    have hn := norm_nonneg u
    have hC := coneCoordinateConstant_nonneg p.val
    have hlow : 0 ≤ ‖u‖/t := div_nonneg hn ht.le
    have htop : 0 ≤ t*B := mul_nonneg ht.le hB
    have halg : 4/t*‖u‖ = 4*(‖u‖/t) := by ring
    rw [halg] at hb'
    nlinarith [mul_nonneg hC hlow]
  calc
    _ ≤ _ := he
    _ ≤ ∑ p : P, (4+coneCoordinateConstant p.val)*(‖u‖/t+t*B) :=
      Finset.sum_le_sum fun p _ => hlocal p
    _ = (K-1)*(‖u‖/t+t*B) := by rw [← Finset.sum_mul]; congr 1; dsimp [K]; ring
    _ ≤ K*(‖u‖/t+t*B) := mul_le_mul_of_nonneg_right (by linarith)
      (add_nonneg (div_nonneg (norm_nonneg _) ht.le) (mul_nonneg ht.le hB))
end Carleman
