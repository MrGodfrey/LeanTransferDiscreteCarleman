module

public import Carleman.Spatial.NeighborWeightComparison
public import Carleman.Weights.GradingThreshold

/-! The four actual Section 6 weights have a mesh-independent grading bound
strictly below Gamma_d. This does not yet prove projection stability. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman

def p1GradingLimit (d : ℕ) : ℝ := (Real.sqrt (d+2)+1)/(Real.sqrt (d+2)-1)

theorem p1GradingLimit_gt_one (d : ℕ) : 1 < p1GradingLimit d := by
  have hs : 1 < Real.sqrt (d+2) := (Real.lt_sqrt (by norm_num)).mpr (by nlinarith [show (0:ℝ) ≤ (d:ℝ) from Nat.cast_nonneg d])
  unfold p1GradingLimit
  apply (lt_div_iff₀ (sub_pos.mpr hs)).mpr
  linarith

theorem p1GradingLimit_two : p1GradingLimit 2=3 := by
  have hs : Real.sqrt (4:ℝ)=2 := by
    rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,Real.sqrt_sq (by norm_num)]
  norm_num [p1GradingLimit,hs]

theorem p1GradingLimit_three : p1GradingLimit 3=(3+Real.sqrt 5)/2 := by
  have hs : Real.sqrt 5-1 ≠ 0 := by
    have h : 1 < Real.sqrt 5 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
    linarith
  have hsq := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  norm_num only [p1GradingLimit,Nat.cast_ofNat,Nat.reduceAdd] 
  field_simp
  nlinarith

theorem allowed_weights_uniform_neighbor_grading {d : ℕ} {S : Set (SpatialCoordinates d)}
    (hS : IsOpen S) (hc : Convex ℝ S) (hcompact : IsCompact (closure S))
    (ρ : SpatialProfile (volume.restrict S)) (hρ : ContDiffOn ℝ 1 ρ.value (closure S))
    (γ : ℝ) (hγ : 1 ≤ γ) (hΓ : γ < p1GradingLimit d) :
    ∃ δ > (0:ℝ), δ ≤ 1 ∧ (γ+p1GradingLimit d)/2 < p1GradingLimit d ∧
    ∀ (ι : Type*) [Fintype ι] (M : SimplicialPartition S ι) (ℓ : ι → ℝ),
      (∀ i, 0 < ℓ i) →
      (∀ i j, M.VertexNeighbors i j → ℓ j ≤ γ*ℓ i) →
    ∀ (w : TimeWeight), M.maxDiameter*w.max ≤ δ →
    ∀ (τ t η : ℝ), |η|=1 → ∀ (inverseSize : Bool) (i j : ι), M.VertexNeighbors i j →
    ∀ᵐ x ∂volume.restrict (M.cell i), ∀ᵐ y ∂volume.restrict (M.cell j),
      |(M.gradedWeight inverseSize ℓ ((ρ.scaled η).multiplier w τ t)).value x| ≤
        ((γ+p1GradingLimit d)/2)*
          |(M.gradedWeight inverseSize ℓ ((ρ.scaled η).multiplier w τ t)).value y| := by
  obtain ⟨L,hL,hLip⟩ := smooth_profile_lipschitz hS hc hcompact hρ
  obtain ⟨δ,hδ,hd,hbound,hstrict⟩ := exists_weight_grading_threshold
    (zero_lt_one.trans_le hγ) hΓ (zero_lt_one.trans_le hL)
  refine ⟨δ,hδ,hd,hstrict,?_⟩
  intro ι _ M ℓ hℓ hg w hm τ t η hη inverseSize i j hij
  have he : γ*Real.exp (2*L*M.maxDiameter*w.q t) ≤ (γ+p1GradingLimit d)/2 := by
    apply le_trans _ hbound
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hγ)
    apply Real.exp_le_exp.mpr
    have hmq := M.maxDiameter_mul_q_le w hm t
    nlinarith [mul_le_mul_of_nonneg_left hmq (by positivity : 0 ≤ 2*L)]
  filter_upwards [M.gradedWeight_neighbor_le hS hc ρ (zero_le_one.trans hL) hγ hLip
    ℓ hℓ hg w τ t η hη inverseSize hij] with x hx
  filter_upwards [hx] with y hy
  exact hy.trans (mul_le_mul_of_nonneg_right he (abs_nonneg _))

end Carleman
