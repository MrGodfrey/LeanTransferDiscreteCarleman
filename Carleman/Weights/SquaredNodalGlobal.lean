module

public import Carleman.Weights.SquaredNodalCell

/-! True global weighted residual integrals obtained by exact integration over
the mesh, with a constant selected before the mesh and all allowed weight data. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem allowedSquaredWeight_nodal_global_integrals
    {S : Set (SpatialCoordinates d)} {ρ : SpatialCoordinates d → ℝ}
    (hS : IsOpen S) (hc : Convex ℝ S) (hcompact : IsCompact (closure S))
    (hρ : ContDiffOn ℝ 2 ρ (closure S)) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ C > (0:ℝ), ∀ {ι : Type*} [Fintype ι] (M : SimplicialPartition S ι), M.FaceMatching →
    ∀ q : ℝ, 1 ≤ q → ∀ τ η : ℝ, |η|=1 → M.maxDiameter*q ≤ 1 →
    ∀ (a : ι → SpatialCoordinates d) (r : ι → ℝ),
      (∀ i, 0 < r i) → (∀ i, Metric.ball (a i) (r i) ⊆ M.cell i) →
      (∀ i, M.cellDiameter i ≤ κ*r i) →
    ∀ f : SpatialCoordinates d → ℝ,
      let w := allowedSquaredWeight ρ q τ η
      let u := M.nodalFunction f
      let e := M.nodalProductResidual w f
      let energy := q^4*(∫ x in S, w x*(u x)^2)+
        q^2*(∫ x in S, w x*‖derivativeOneFiber (fderiv ℝ u x)‖^2)
      (∫ x in S, (e x)^2/w x) ≤ C*M.maxDiameter^4*energy ∧
      (∫ x in S, ‖derivativeOneFiber (fderiv ℝ e x)‖^2/w x) ≤ C*M.maxDiameter^2*energy := by
  obtain ⟨C,hC,hbound⟩ := allowedSquaredWeight_nodal_cell_integrals hS hc hcompact hρ hκ
  refine ⟨C,hC,?_⟩
  intro ι _ M hM q hq τ η hη hsmall a r hr hball hshape f
  let w := allowedSquaredWeight ρ q τ η
  let u := M.nodalFunction f
  let e := M.nodalProductResidual w f
  let cellEnergy (i : ι) := q^4*(∫ x in M.cell i, w x*(u x)^2)+
    q^2*(∫ x in M.cell i, w x*‖derivativeOneFiber (fderiv ℝ u x)‖^2)
  let energy := q^4*(∫ x in S, w x*(u x)^2)+
    q^2*(∫ x in S, w x*‖derivativeOneFiber (fderiv ℝ u x)‖^2)
  have hwpos (x : SpatialCoordinates d) : 0 < w x := by
    dsimp only [w,allowedSquaredWeight]
    have hqpos := zero_lt_one.trans_le hq
    positivity
  have hEi (i : ι) : 0 ≤ cellEnergy i := by
    apply add_nonneg
    · exact mul_nonneg (by positivity) (integral_nonneg (fun x => mul_nonneg (hwpos x).le (sq_nonneg _)))
    · exact mul_nonneg (sq_nonneg q) (integral_nonneg (fun x => mul_nonneg (hwpos x).le (sq_nonneg _)))
  obtain ⟨he₀,he₁,hu₀,hu₁⟩ := M.squaredNodal_integrability hS hc hM hρ (zero_lt_one.trans_le hq) τ η f
  have hsum : ∑ i, cellEnergy i = energy := by
    dsimp only [cellEnergy,energy]
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
      ← M.integral_eq_sum_cells hS hc _ hu₀,← M.integral_eq_sum_cells hS hc _ hu₁]
  have hb (i : ι) := hbound M hM q hq τ η hη hsmall a r hr hball hshape f i
  change (∫ x in S, (e x)^2/w x) ≤ C*M.maxDiameter^4*energy ∧
    (∫ x in S, ‖derivativeOneFiber (fderiv ℝ e x)‖^2/w x) ≤ C*M.maxDiameter^2*energy
  constructor
  · rw [M.integral_eq_sum_cells hS hc _ he₀]
    calc
      _ ≤ ∑ i, C*(M.cellDiameter i)^4*cellEnergy i := Finset.sum_le_sum (fun i _ => (hb i).1)
      _ ≤ ∑ i, C*M.maxDiameter^4*cellEnergy i := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_right _ (hEi i)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (M.cellDiameter_nonneg i) (M.cellDiameter_le_max i) 4) hC.le
      _ = _ := by rw [← Finset.mul_sum,hsum]
  · rw [M.integral_eq_sum_cells hS hc _ he₁]
    calc
      _ ≤ ∑ i, C*(M.cellDiameter i)^2*cellEnergy i := Finset.sum_le_sum (fun i _ => (hb i).2)
      _ ≤ ∑ i, C*M.maxDiameter^2*cellEnergy i := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_right _ (hEi i)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (M.cellDiameter_nonneg i) (M.cellDiameter_le_max i) 2) hC.le
      _ = _ := by rw [← Finset.mul_sum,hsum]

end Carleman
