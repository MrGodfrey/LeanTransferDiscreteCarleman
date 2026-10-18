module

public import Carleman.Spatial.UniformNeighborGrading
public import Carleman.Spatial.NodalWeightMinimum

/-! Actual cell samples of the four allowed weights, before their nodal minimum. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}
  (M : Carleman.SimplicialPartition S ι)

def gradedCellWeight (inverseSize : Bool) (ℓ : ι → ℝ)
    (w : BoundedMultiplier (volume.restrict S)) (i : ι) : ℝ :=
  (if inverseSize then (ℓ i)⁻¹ else 1)*w.value ((M.simplex i).points 0)

omit [Fintype ι] in
theorem gradedCellWeight_pos (inverseSize : Bool) (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (ρ : SpatialProfile (volume.restrict S)) (w : TimeWeight) (τ t η : ℝ) (i : ι) :
    0 < M.gradedCellWeight inverseSize ℓ ((ρ.scaled η).multiplier w τ t) i := by
  apply mul_pos _ (ρ.scaled_multiplier_pos η w τ t _)
  cases inverseSize <;> simp [hℓ i]

theorem allowedWeight_scaled_neighbor_le (ρ : SpatialProfile (volume.restrict S)) {L γ : ℝ}
    (hL : 0 ≤ L)
    (hρ : ∀ x ∈ closure S, ∀ y ∈ closure S, |ρ.value x-ρ.value y| ≤ L*dist x y)
    (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (hg : ∀ i j, M.VertexNeighbors i j → a i ≤ γ*a j)
    (w : TimeWeight) (τ t η : ℝ) (hη : |η|=1) {i j : ι} (hij : M.VertexNeighbors i j)
    {x y : SpatialCoordinates d} (hx : x ∈ M.cell i) (hy : y ∈ M.cell j) :
    a i*((ρ.scaled η).multiplier w τ t).value x ≤
      (γ*Real.exp (2*L*M.maxDiameter*w.q t))*(a j*((ρ.scaled η).multiplier w τ t).value y) := by
  have hb := M.allowedWeight_neighbor_le ρ hL hρ w τ t η hη hij hx hy
  calc
    _ ≤ a i*(Real.exp (2*L*M.maxDiameter*w.q t)*((ρ.scaled η).multiplier w τ t).value y) :=
      mul_le_mul_of_nonneg_left hb (ha i).le
    _ ≤ (γ*a j)*(Real.exp (2*L*M.maxDiameter*w.q t)*((ρ.scaled η).multiplier w τ t).value y) :=
      mul_le_mul_of_nonneg_right (hg i j hij)
        (mul_nonneg (Real.exp_pos _).le (ρ.scaled_multiplier_pos η w τ t y).le)
    _ = _ := by ring

omit [Fintype ι] in
theorem sizeWeightFactor_grading (inverseSize : Bool) (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    {γ : ℝ} (hγ : 1 ≤ γ) (hg : ∀ i j, M.VertexNeighbors i j → ℓ j ≤ γ*ℓ i) :
    ∀ i j, M.VertexNeighbors i j →
      (if inverseSize then (ℓ i)⁻¹ else 1) ≤ γ*(if inverseSize then (ℓ j)⁻¹ else 1) := by
  intro i j hij
  cases inverseSize
  · simpa using hγ
  · change (ℓ i)⁻¹ ≤ γ*(ℓ j)⁻¹
    rw [← one_div,← div_eq_mul_inv γ (ℓ j)]
    exact (div_le_div_iff₀ (hℓ i) (hℓ j)).mpr (by simpa only [one_mul] using hg i j hij)

theorem gradedCellWeight_neighbor_le (ρ : SpatialProfile (volume.restrict S)) {L γ : ℝ}
    (hL : 0 ≤ L) (hγ : 1 ≤ γ)
    (hρ : ∀ x ∈ closure S, ∀ y ∈ closure S, |ρ.value x-ρ.value y| ≤ L*dist x y)
    (inverseSize : Bool) (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (hg : ∀ i j, M.VertexNeighbors i j → ℓ j ≤ γ*ℓ i)
    (w : TimeWeight) (τ t η : ℝ) (hη : |η|=1) {i j : ι} (hij : M.VertexNeighbors i j) :
    M.gradedCellWeight inverseSize ℓ ((ρ.scaled η).multiplier w τ t) i ≤
      (γ*Real.exp (2*L*M.maxDiameter*w.q t))*
        M.gradedCellWeight inverseSize ℓ ((ρ.scaled η).multiplier w τ t) j := by
  exact M.allowedWeight_scaled_neighbor_le ρ hL hρ
    (fun k => if inverseSize then (ℓ k)⁻¹ else 1)
    (fun k => by cases inverseSize <;> simp [hℓ k])
    (M.sizeWeightFactor_grading inverseSize ℓ hℓ hγ hg) w τ t η hη hij
    (subset_convexHull ℝ _ (Set.mem_range_self 0)) (subset_convexHull ℝ _ (Set.mem_range_self 0))


theorem gradedCellWeight_compare (hS : IsOpen S) (hc : Convex ℝ S)
    (ρ : SpatialProfile (volume.restrict S)) {L γ : ℝ} (hL : 0 ≤ L) (hγ : 1 ≤ γ)
    (hρ : ∀ x ∈ closure S, ∀ y ∈ closure S, |ρ.value x-ρ.value y| ≤ L*dist x y)
    (inverseSize : Bool) (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (hg : ∀ i j, M.VertexNeighbors i j → ℓ j ≤ γ*ℓ i)
    (w : TimeWeight) (τ t η : ℝ) (hη : |η|=1) (i : ι) :
    ∀ᵐ x ∂volume.restrict (M.cell i),
      |(M.gradedWeight inverseSize ℓ ((ρ.scaled η).multiplier w τ t)).value x| ≤
        (γ*Real.exp (2*L*M.maxDiameter*w.q t))*
          M.gradedCellWeight inverseSize ℓ ((ρ.scaled η).multiplier w τ t) i ∧
      M.gradedCellWeight inverseSize ℓ ((ρ.scaled η).multiplier w τ t) i ≤
        (γ*Real.exp (2*L*M.maxDiameter*w.q t))*
          |(M.gradedWeight inverseSize ℓ ((ρ.scaled η).multiplier w τ t)).value x| := by
  let a : ι → ℝ := fun k => if inverseSize then (ℓ k)⁻¹ else 1
  have ha (k : ι) : 0 < a k := by cases inverseSize <;> simp [a,hℓ k]
  have hcomp {x y : SpatialCoordinates d} := M.allowedWeight_scaled_neighbor_le ρ hL hρ a ha
    (M.sizeWeightFactor_grading inverseSize ℓ hℓ hγ hg) w τ t η hη
    (i := i) (j := i) (x := x) (y := y) ⟨0,0,rfl⟩
  have h0 : (M.simplex i).points 0 ∈ M.cell i := subset_convexHull ℝ _ (Set.mem_range_self 0)
  filter_upwards [M.gradedWeight_on_cell hS hc inverseSize ℓ ((ρ.scaled η).multiplier w τ t) i,
    ae_restrict_mem (simplicialCell_measurable (M.simplex i).points)] with x hx hxi
  rw [hx,abs_of_pos (mul_pos (ha i) (ρ.scaled_multiplier_pos η w τ t x))]
  exact ⟨hcomp hxi h0,hcomp h0 hxi⟩

end Carleman.SimplicialPartition
