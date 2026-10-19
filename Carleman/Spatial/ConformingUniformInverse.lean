module

public import Carleman.Spatial.ConformingWeightedInverse
public import Carleman.Spatial.SimplicialDiameter
public import Carleman.Spatial.MultiplierAlgebra

/-! The unweighted P1 inverse estimate at the genuine maximum coarse
cell diameter, with a constant uniform over all coarse meshes and states. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman

theorem SimplicialPartition.maxDiameter_pos {d : ℕ} {ι : Type*} [Fintype ι]
    {S : Set (SpatialCoordinates d)} (M : SimplicialPartition S ι)
    (hd : 0 < d) (hS : S.Nonempty) : 0 < M.maxDiameter := by
  obtain ⟨x,hx⟩ := hS
  obtain ⟨i,_⟩ := mem_iUnion.mp (M.cover hx)
  have hp : 0 < M.cellDiameter i := by
    apply Metric.diam_pos _ (simplicialCell_compact _).isBounded
    refine ⟨(M.simplex i).points 0,subset_convexHull ℝ _ (mem_range_self 0),
      (M.simplex i).points ⟨1,by omega⟩,subset_convexHull ℝ _ (mem_range_self _),?_⟩
    intro he
    have hh := (M.simplex i).independent.injective he
    have hval := congrArg Fin.val hh
    norm_num at hval
  exact hp.trans_le (M.cellDiameter_le_max i)

theorem SimplicialPartition.inverseWeight_const_bound {d : ℕ} {ι : Type*} [Fintype ι]
    {S : Set (SpatialCoordinates d)} (M : SimplicialPartition S ι) (hS : MeasurableSet S)
    {H : ℝ} (hH : 0 < H) (u : Lp ℝ 2 (volume.restrict S)) :
    (M.inverseWeight (fun _ => H) BoundedMultiplier.one).seminorm u ≤ H⁻¹*‖u‖ := by
  have hb : ∀ᵐ x ∂volume.restrict S,
      |(M.inverseWeight (fun _ => H) BoundedMultiplier.one).value x| ≤
        H⁻¹*|BoundedMultiplier.one (ν := volume.restrict S) |>.value x| := by
    filter_upwards [M.ae_partition hS,ae_all_iff.mpr
      (fun i => M.inverseWeight_on_cell hS (fun _ => H) BoundedMultiplier.one i)] with x hx hw
    obtain ⟨i,hi,_⟩ := hx
    rw [hw i hi]
    simp only [BoundedMultiplier.one,mul_one,abs_one,abs_of_pos (inv_pos.mpr hH)]
    exact le_rfl
  simpa only [BoundedMultiplier.one_seminorm] using
    (M.inverseWeight (fun _ => H) BoundedMultiplier.one).seminorm_le_of_weight_le
      BoundedMultiplier.one H⁻¹ hb u

theorem conforming_uniform_inverse (d : ℕ) (κ Q : ℝ) (hκ : 0 < κ) (hQ : 0 < Q) :
    ∃ C > (0:ℝ), ∀ (ι : Type*) [Fintype ι] (S : Set (SpatialCoordinates d))
      (M : SimplicialPartition S ι), IsOpen S → Convex ℝ S →
    ∀ [IsFiniteMeasure (volume.restrict S)] (a : ι → SpatialCoordinates d) (r : ι → ℝ),
      (∀ i, 0 < r i) → (∀ i, Metric.ball (a i) (r i) ⊆ M.cell i) →
      (∀ i, M.cellDiameter i ≤ κ*r i) → (∀ i, M.maxDiameter ≤ Q*M.cellDiameter i) →
      0 < M.maxDiameter →
    ∀ (V : Submodule ℝ (Lp ℝ 2 (volume.restrict S)))
      (u : WeakSobolevJet d 1 (volume.restrict S) S),
      WeakSobolevJet.value u ∈ M.conformingSpace V →
      ‖WeakSobolevJet.field 1 u‖ ≤ (C/M.maxDiameter)*‖WeakSobolevJet.value u‖ := by
  obtain ⟨C,hC,hbound⟩ := conforming_weighted_inverse d (Q*κ) 1 (mul_pos hQ hκ) zero_lt_one
  refine ⟨C,hC,?_⟩
  intro ι _ S M hS hc _ a r hr hball hshape hquasi hH V u hu
  have hh := hbound ι S M hS hc a r (fun _ => M.maxDiameter) hr (fun _ => hH) hball
    (M.cellScale_le_inball hQ.le r (fun _ => M.maxDiameter) hshape hquasi)
    BoundedMultiplier.one (fun _ => 1) (fun _ => zero_lt_one)
    (fun _ => Filter.Eventually.of_forall fun _ => by simp [BoundedMultiplier.one]) V u hu
  rw [BoundedMultiplier.one_seminorm] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left
    (M.inverseWeight_const_bound hS.measurableSet hH _) hC.le).trans_eq (by ring))

end Carleman
