module

public import Carleman.Spatial.SimplicialNeighbors
public import Carleman.Spatial.SimplicialAllowedComparison
public import Carleman.Spatial.CellwiseInverseWeight

/-! Actual neighbor comparison for sigma and the elementwise inverse-scale
weight. Both signs and all real powers cover the four weights in Section 6. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SpatialProfile
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

theorem scaled_multiplier_inverse_value (ρ : SpatialProfile ν) (η : ℝ)
    (w : TimeWeight) (τ t : ℝ) (x : Ω) :
    ((ρ.scaled (-η)).multiplier w (-τ) t).value x =
      (((ρ.scaled η).multiplier w τ t).value x)⁻¹ := by
  simp only [scaled_multiplier_value,Real.rpow_neg (w.nonneg t),neg_mul,Real.exp_neg,mul_inv_rev]
  ring

end Carleman.SpatialProfile

namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}
  (M : Carleman.SimplicialPartition S ι)

omit [Fintype ι] in
theorem scale_grading_from_ratios (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i) (γ : ℝ)
    (hg : ∀ i j, M.VertexNeighbors i j → γ⁻¹ ≤ ℓ i/ℓ j ∧ ℓ i/ℓ j ≤ γ) :
    ∀ i j, M.VertexNeighbors i j → ℓ j ≤ γ*ℓ i := by
  intro i j hij
  exact (div_le_iff₀ (hℓ i)).mp ((hg j i (hij.symm M)).2)

theorem allowedWeight_neighbor_le (ρ : SpatialProfile (volume.restrict S)) {L : ℝ}
    (hL : 0 ≤ L)
    (hρ : ∀ x ∈ closure S, ∀ y ∈ closure S, |ρ.value x-ρ.value y| ≤ L*dist x y)
    (w : TimeWeight) (τ t η : ℝ) (hη : |η|=1) {i j : ι} (hij : M.VertexNeighbors i j)
    {x y : SpatialCoordinates d} (hx : x ∈ M.cell i) (hy : y ∈ M.cell j) :
    ((ρ.scaled η).multiplier w τ t).value x ≤
      Real.exp (2*L*M.maxDiameter*w.q t)*((ρ.scaled η).multiplier w τ t).value y := by
  have hb : |ρ.value x-ρ.value y| ≤ 2*L*M.maxDiameter := by
    have hh := (hρ x (M.inside i hx) y (M.inside j hy)).trans
      (mul_le_mul_of_nonneg_left (M.vertexNeighbors_dist_le_max hij hx hy) hL)
    nlinarith
  exact ρ.scaled_multiplier_spatial_le η hη w τ t hb

def gradedWeight (inverseSize : Bool) (ℓ : ι → ℝ) (w : BoundedMultiplier (volume.restrict S)) :
    BoundedMultiplier (volume.restrict S) := if inverseSize then M.inverseWeight ℓ w else w

theorem gradedWeight_on_cell (hS : IsOpen S) (hc : Convex ℝ S) (inverseSize : Bool)
    (ℓ : ι → ℝ) (w : BoundedMultiplier (volume.restrict S)) (i : ι) :
    ∀ᵐ x ∂volume.restrict (M.cell i),
      (M.gradedWeight inverseSize ℓ w).value x = (if inverseSize then (ℓ i)⁻¹ else 1)*w.value x := by
  cases inverseSize
  · exact Filter.Eventually.of_forall (fun _ => (one_mul _).symm)
  · filter_upwards [(M.inverseWeight_on_cell hS.measurableSet ℓ w i).filter_mono
      (ae_mono (M.cell_measure_le_domain hS hc i)),
      ae_restrict_mem (simplicialCell_measurable (M.simplex i).points)] with x hx hi
    exact hx hi

theorem gradedWeight_neighbor_le (hS : IsOpen S) (hc : Convex ℝ S)
    (ρ : SpatialProfile (volume.restrict S)) {L γ : ℝ} (hL : 0 ≤ L) (hγ : 1 ≤ γ)
    (hρ : ∀ x ∈ closure S, ∀ y ∈ closure S, |ρ.value x-ρ.value y| ≤ L*dist x y)
    (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (hg : ∀ i j, M.VertexNeighbors i j → ℓ j ≤ γ*ℓ i)
    (w : TimeWeight) (τ t η : ℝ) (hη : |η|=1) (inverseSize : Bool)
    {i j : ι} (hij : M.VertexNeighbors i j) :
    ∀ᵐ x ∂volume.restrict (M.cell i), ∀ᵐ y ∂volume.restrict (M.cell j),
      |(M.gradedWeight inverseSize ℓ ((ρ.scaled η).multiplier w τ t)).value x| ≤
        (γ*Real.exp (2*L*M.maxDiameter*w.q t))*
          |(M.gradedWeight inverseSize ℓ ((ρ.scaled η).multiplier w τ t)).value y| := by
  let σ := (ρ.scaled η).multiplier w τ t
  let a : ι → ℝ := fun k => if inverseSize then (ℓ k)⁻¹ else 1
  have ha (k : ι) : 0 < a k := by cases inverseSize <;> simp [a,hℓ k]
  have hag : a i ≤ γ*a j := by
    cases inverseSize
    · simpa only [a,Bool.false_eq_true,↓reduceIte,mul_one] using hγ
    · change (ℓ i)⁻¹ ≤ γ*(ℓ j)⁻¹
      rw [← one_div,← div_eq_mul_inv γ (ℓ j)]
      exact (div_le_div_iff₀ (hℓ i) (hℓ j)).mpr (by simpa only [one_mul] using hg i j hij)
  filter_upwards [M.gradedWeight_on_cell hS hc inverseSize ℓ σ i,
    ae_restrict_mem (simplicialCell_measurable (M.simplex i).points)] with x hx hxi
  filter_upwards [M.gradedWeight_on_cell hS hc inverseSize ℓ σ j,
    ae_restrict_mem (simplicialCell_measurable (M.simplex j).points)] with y hy hyj
  change |(M.gradedWeight inverseSize ℓ σ).value x| ≤ _
  rw [hx,hy]
  change |a i*σ.value x| ≤ (γ*Real.exp (2*L*M.maxDiameter*w.q t))*|a j*σ.value y|
  rw [abs_of_pos (mul_pos (ha i) (ρ.scaled_multiplier_pos η w τ t x)),
    abs_of_pos (mul_pos (ha j) (ρ.scaled_multiplier_pos η w τ t y))]
  have hb := M.allowedWeight_neighbor_le ρ hL hρ w τ t η hη hij hxi hyj
  calc
    _ ≤ a i*(Real.exp (2*L*M.maxDiameter*w.q t)*σ.value y) :=
      mul_le_mul_of_nonneg_left hb (ha i).le
    _ ≤ (γ*a j)*(Real.exp (2*L*M.maxDiameter*w.q t)*σ.value y) :=
      mul_le_mul_of_nonneg_right hag (mul_nonneg (Real.exp_pos _).le (ρ.scaled_multiplier_pos η w τ t y).le)
    _ = _ := by ring

end Carleman.SimplicialPartition
