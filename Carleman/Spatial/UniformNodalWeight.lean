module

public import Carleman.Spatial.AllowedCellWeight

/-! Uniform admissible nodal weights constructed from each of the four actual weights. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman

theorem allowed_weights_uniform_nodal_weights {d : ℕ} {S : Set (SpatialCoordinates d)}
    (hS : IsOpen S) (hc : Convex ℝ S) (hcompact : IsCompact (closure S))
    (ρ : SpatialProfile (volume.restrict S)) (hρ : ContDiffOn ℝ 1 ρ.value (closure S))
    (γ : ℝ) (hγ : 1 ≤ γ) (hΓ : γ < p1GradingLimit d) :
    ∃ δ > (0:ℝ), δ ≤ 1 ∧
    let θ := (γ+p1GradingLimit d)/2
    1 ≤ θ ∧ θ < p1GradingLimit d ∧
    ∀ (ι : Type*) [Fintype ι] (M : SimplicialPartition S ι) (ℓ : ι → ℝ),
      (∀ i, 0 < ℓ i) →
      (∀ i j, M.VertexNeighbors i j → ℓ j ≤ γ*ℓ i) →
    ∀ (w : TimeWeight), M.maxDiameter*w.max ≤ δ →
    ∀ (τ t η : ℝ), |η|=1 → ∀ (inverseSize : Bool),
    let ζ := M.gradedWeight inverseSize ℓ ((ρ.scaled η).multiplier w τ t)
    let a := M.gradedCellWeight inverseSize ℓ ((ρ.scaled η).multiplier w τ t)
    let ω := M.nodalWeightMinimum a
    (∀ x, 0 < ω x) ∧
    (∀ i k, a i/θ ≤ ω ((M.simplex i).points k) ∧ ω ((M.simplex i).points k) ≤ a i) ∧
    (∀ i, ∀ᵐ x ∂volume.restrict (M.cell i),
      |ζ.value x| ≤ θ*a i ∧ a i ≤ θ*|ζ.value x|) := by
  obtain ⟨L,hL,hLip⟩ := smooth_profile_lipschitz hS hc hcompact hρ
  obtain ⟨δ,hδ,hd,hbound,hstrict⟩ := exists_weight_grading_threshold
    (zero_lt_one.trans_le hγ) hΓ (zero_lt_one.trans_le hL)
  have hθ : 1 ≤ (γ+p1GradingLimit d)/2 := by linarith
  refine ⟨δ,hδ,hd,hθ,hstrict,?_⟩
  intro ι _ M ℓ hℓ hg w hm τ t η hη inverseSize
  let θ := (γ+p1GradingLimit d)/2
  let a := M.gradedCellWeight inverseSize ℓ ((ρ.scaled η).multiplier w τ t)
  have ha (i : ι) : 0 < a i := M.gradedCellWeight_pos inverseSize ℓ hℓ ρ w τ t η i
  have hsmall : γ*Real.exp (2*L*M.maxDiameter*w.q t) ≤ θ := by
    apply le_trans _ hbound
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hγ)
    apply Real.exp_le_exp.mpr
    have hmq := M.maxDiameter_mul_q_le w hm t
    nlinarith [mul_le_mul_of_nonneg_left hmq (by positivity : 0 ≤ 2*L)]
  have hag : ∀ i j, M.VertexNeighbors i j → a i ≤ θ*a j := by
    intro i j hij
    exact (M.gradedCellWeight_neighbor_le ρ (zero_le_one.trans hL) hγ hLip
      inverseSize ℓ hℓ hg w τ t η hη hij).trans
        (mul_le_mul_of_nonneg_right hsmall (ha j).le)
  refine ⟨M.nodalWeightMinimum_pos a ha,
    M.nodalWeightMinimum_vertex_bounds a (zero_lt_one.trans_le hθ) hag,?_⟩
  intro i
  filter_upwards [M.gradedCellWeight_compare hS hc ρ (zero_le_one.trans hL) hγ hLip
    inverseSize ℓ hℓ hg w τ t η hη i] with x hx
  exact ⟨hx.1.trans (mul_le_mul_of_nonneg_right hsmall (ha i).le),
    hx.2.trans (mul_le_mul_of_nonneg_right hsmall (abs_nonneg _))⟩

end Carleman
