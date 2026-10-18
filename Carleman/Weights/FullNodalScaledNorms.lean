module

public import Carleman.Weights.ScaledNodalResidual

/-! All three original nodal residual estimates hold for the same genuine
weak residual and nodal test, including the inverse mesh-size weight. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

set_option maxHeartbeats 800000 in
theorem allowed_full_nodal_scaled_norms
    {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hc : Convex ℝ S)
    (hcompact : IsCompact (closure S)) (ρ : SpatialProfile (volume.restrict S))
    (hρ : ContDiffOn ℝ 2 ρ.value (closure S)) {κ c : ℝ} (hκ : 0 ≤ κ) (hcpos : 0 < c)
    [IsFiniteMeasure (volume.restrict S)] :
    ∃ C > (0:ℝ), ∀ {ι : Type*} [Fintype ι] (M : SimplicialPartition S ι),
    M.FaceMatching → M.BoundaryFitted →
    ∀ (w : TimeWeight) (τ t η : ℝ), 1 ≤ w.q t → |η|=1 → M.maxDiameter*w.q t ≤ 1 →
    ∀ (a : ι → SpatialCoordinates d) (r ℓ : ι → ℝ),
      (∀ i, 0 < r i) → (∀ i, Metric.ball (a i) (r i) ⊆ M.cell i) →
      (∀ i, M.cellDiameter i ≤ κ*r i) →
      (∀ i, 0 < ℓ i) → (∀ i, c*M.cellDiameter i ≤ ℓ i) →
    ∀ u : WeakSobolevJet d 1 (volume.restrict S) S,
      WeakSobolevJet.value u ∈ M.conformingSpace (dirichletSubspace S) →
    ∃ (I : Lp ℝ 2 (volume.restrict S)) (e : WeakSobolevJet d 1 (volume.restrict S) S),
      I ∈ M.conformingSpace (dirichletSubspace S) ∧
      let σ := (ρ.scaled η).multiplier w τ t
      let ξ := (ρ.scaled (-η)).multiplier w (-τ) t
      let energy := (w.q t)^4*(σ.seminorm (WeakSobolevJet.value u))^2+
        (w.q t)^2*(σ.seminorm (WeakSobolevJet.field 1 u))^2
      WeakSobolevJet.value e=(σ.mul σ).map (WeakSobolevJet.value u)-I ∧
      (ξ.seminorm (WeakSobolevJet.value e))^2 ≤ C*M.maxDiameter^4*energy ∧
      (ξ.seminorm (WeakSobolevJet.field 1 e))^2 ≤ C*M.maxDiameter^2*energy ∧
      ((M.inverseWeight ℓ ξ).seminorm (WeakSobolevJet.value e))^2 ≤ C*M.maxDiameter^2*energy := by
  obtain ⟨C₁,hC₁,hbound⟩ := allowedSquaredWeight_full_weak_residual hS hc hcompact hρ hκ
  obtain ⟨C₂,hC₂,hscaled⟩ := allowed_scaled_nodal_residual hS hc hcompact ρ hρ hκ hcpos
  refine ⟨C₁+C₂,by positivity,?_⟩
  intro ι _ M hM hB w τ t η hq hη hsmall a r ℓ hr hball hshape hℓ hscale u hu
  obtain ⟨f,e,hf,hval,he,hI,hvalue,hgradient⟩ :=
    hbound M hM hB (w.q t) hq τ η hη hsmall a r hr hball hshape u hu
  let σ := (ρ.scaled η).multiplier w τ t
  let ξ := (ρ.scaled (-η)).multiplier w (-τ) t
  let I := M.nodalLp hS.measurableSet hM (fun x => allowedSquaredWeight ρ.value (w.q t) τ η x*f x)
  let energy := (w.q t)^4*(σ.seminorm (WeakSobolevJet.value u))^2+
    (w.q t)^2*(σ.seminorm (WeakSobolevJet.field 1 u))^2
  have henergy : 0 ≤ energy := by dsimp only [energy]; positivity
  have hw : allowedSquaredWeight ρ.value (w.q t) τ η = (σ.mul σ).value := by
    funext x
    rw [allowedSquaredWeight_multiplier_value]
    change (σ.value x)^2=σ.value x*σ.value x
    ring
  have hmap : WeakSobolevJet.value e=(σ.mul σ).map (WeakSobolevJet.value u)-I := by
    have he' := he
    rw [hw] at he'
    simpa only [I,hw] using M.nodalProductResidual_lp hS.measurableSet hM (σ.mul σ) f
      (WeakSobolevJet.value u) (WeakSobolevJet.value e) hval he'
  have hzero : (ξ.seminorm (WeakSobolevJet.value e))^2 ≤ C₁*M.maxDiameter^4*energy := by
    dsimp only [ξ,energy,σ]
    rw [allowed_inverse_weight_sq_integral,allowed_weight_sq_integral,allowed_weight_sq_integral]
    simpa only [Real.norm_eq_abs,sq_abs] using hvalue
  have hfirst : (ξ.seminorm (WeakSobolevJet.field 1 e))^2 ≤ C₁*M.maxDiameter^2*energy := by
    dsimp only [ξ,energy,σ]
    rw [allowed_inverse_weight_sq_integral,allowed_weight_sq_integral,allowed_weight_sq_integral]
    simpa only [Real.norm_eq_abs,sq_abs] using hgradient
  have hmesh : ((M.inverseWeight ℓ ξ).seminorm (WeakSobolevJet.value e))^2 ≤ C₂*M.maxDiameter^2*energy := by
    have hb := hscaled M hM w τ t η hq hη hsmall a r ℓ hr hball hshape hℓ hscale f (WeakSobolevJet.value e) he
    have hv : (∫ x in S, allowedSquaredWeight ρ.value (w.q t) τ η x*(M.nodalFunction f x)^2) =
        (σ.seminorm (WeakSobolevJet.value u))^2 := by
      rw [allowed_weight_sq_integral,hval]
      apply integral_congr_ae
      filter_upwards [M.nodalLp_ae hS.measurableSet hM f] with x hx
      rw [hx,Real.norm_eq_abs,sq_abs]
    have hg : (∫ x in S, allowedSquaredWeight ρ.value (w.q t) τ η x*
        ‖derivativeOneFiber (fderiv ℝ (M.nodalFunction f) x)‖^2) =
        (σ.seminorm (WeakSobolevJet.field 1 u))^2 := by
      rw [allowed_weight_sq_integral]
      apply integral_congr_ae
      filter_upwards [M.nodal_representation_weak_gradient hS hc hM u f hval] with x hx
      rw [hx]
    dsimp only at hb
    rw [hv,hg] at hb
    exact hb
  refine ⟨I,e,hI,hmap,?_,?_,?_⟩
  · exact hzero.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₂.le) (pow_nonneg M.maxDiameter_nonneg 4)) henergy)
  · exact hfirst.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₂.le) (sq_nonneg _)) henergy)
  · exact hmesh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₁.le) (sq_nonneg _)) henergy)

end Carleman
