module

public import Carleman.Spatial.ScaledResidualIntegral

/-! The inverse mesh-size weighted residual estimate, from the original
positive lower comparison of scale and actual cell diameter. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem allowed_scaled_nodal_residual
    {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hc : Convex ℝ S)
    (hcompact : IsCompact (closure S)) (ρ : SpatialProfile (volume.restrict S))
    (hρ : ContDiffOn ℝ 2 ρ.value (closure S)) {κ c : ℝ} (hκ : 0 ≤ κ) (hcpos : 0 < c) :
    ∃ C > (0:ℝ), ∀ {ι : Type*} [Fintype ι] (M : SimplicialPartition S ι), M.FaceMatching →
    ∀ (w : TimeWeight) (τ t η : ℝ), 1 ≤ w.q t → |η|=1 → M.maxDiameter*w.q t ≤ 1 →
    ∀ (a : ι → SpatialCoordinates d) (r ℓ : ι → ℝ),
      (∀ i, 0 < r i) → (∀ i, Metric.ball (a i) (r i) ⊆ M.cell i) →
      (∀ i, M.cellDiameter i ≤ κ*r i) →
      (∀ i, 0 < ℓ i) → (∀ i, c*M.cellDiameter i ≤ ℓ i) →
    ∀ (f : SpatialCoordinates d → ℝ) (e : Lp ℝ 2 (volume.restrict S)),
      e =ᵐ[volume.restrict S] M.nodalProductResidual (allowedSquaredWeight ρ.value (w.q t) τ η) f →
      let W := allowedSquaredWeight ρ.value (w.q t) τ η
      let u := M.nodalFunction f
      ((M.inverseWeight ℓ ((ρ.scaled (-η)).multiplier w (-τ) t)).seminorm e)^2 ≤
        C*M.maxDiameter^2*((w.q t)^4*(∫ x in S, W x*(u x)^2)+
          (w.q t)^2*(∫ x in S, W x*‖derivativeOneFiber (fderiv ℝ u x)‖^2)) := by
  obtain ⟨C,hC,hbound⟩ := allowedSquaredWeight_nodal_cell_integrals hS hc hcompact hρ hκ
  refine ⟨C*(c⁻¹)^2,by positivity,?_⟩
  intro ι _ M hM w τ t η hq hη hsmall a r ℓ hr hball hshape hℓ hscale f e he
  let W := allowedSquaredWeight ρ.value (w.q t) τ η
  let u := M.nodalFunction f
  let cellEnergy (i : ι) := (w.q t)^4*(∫ x in M.cell i, W x*(u x)^2)+
    (w.q t)^2*(∫ x in M.cell i, W x*‖derivativeOneFiber (fderiv ℝ u x)‖^2)
  let energy := (w.q t)^4*(∫ x in S, W x*(u x)^2)+
    (w.q t)^2*(∫ x in S, W x*‖derivativeOneFiber (fderiv ℝ u x)‖^2)
  have hW (x : SpatialCoordinates d) : 0 ≤ W x := sq_nonneg _
  have hEi (i : ι) : 0 ≤ cellEnergy i := by
    apply add_nonneg
    · exact mul_nonneg (by positivity) (integral_nonneg (fun x => mul_nonneg (hW x) (sq_nonneg _)))
    · exact mul_nonneg (sq_nonneg _) (integral_nonneg (fun x => mul_nonneg (hW x) (sq_nonneg _)))
  obtain ⟨_,_,hu₀,hu₁⟩ := M.squaredNodal_integrability hS hc hM hρ (w.pos t) τ η f
  have hsum : ∑ i, cellEnergy i = energy := by
    dsimp only [cellEnergy,energy]
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
      ← M.integral_eq_sum_cells hS hc _ hu₀,← M.integral_eq_sum_cells hS hc _ hu₁]
  have hb (i : ι) := (hbound M hM (w.q t) hq τ η hη hsmall a r hr hball hshape f i).1
  rw [M.inverseWeight_residual_sq_sum hS hc ℓ ρ w τ t η f e he]
  calc
    _ ≤ ∑ i, ((ℓ i)⁻¹)^2*(C*(M.cellDiameter i)^4*cellEnergy i) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hb i) (sq_nonneg _))
    _ = ∑ i, C*(((ℓ i)⁻¹)^2*(M.cellDiameter i)^4)*cellEnergy i :=
      Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ ∑ i, C*((c⁻¹)^2*M.maxDiameter^2)*cellEnergy i := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (inverseScale_diameter_four_bound hcpos (hℓ i) (M.cellDiameter_nonneg i)
          (M.cellDiameter_le_max i) (hscale i)) hC.le) (hEi i)
    _ = C*(c⁻¹)^2*M.maxDiameter^2*energy := by rw [← Finset.mul_sum,hsum]; ring

end Carleman
