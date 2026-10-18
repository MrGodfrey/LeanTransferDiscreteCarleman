module

public import Carleman.Spatial.NodalWeightedTest
public import Carleman.Spatial.WeightedSimplexMassBound

/-! Genuine weighted L² norm bounds for nodal states and their squared-weight tests. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}
  (M : Carleman.SimplicialPartition S ι)

def nodalCoefficientEnergy (ω f : SpatialCoordinates d → ℝ) : ℝ :=
  ∑ i, volume.real (M.cell i)/((d+1:ℝ)*(d+2))*
    (∑ k, (ω ((M.simplex i).points k)*f ((M.simplex i).points k))^2)

theorem nodalCoefficientEnergy_nonneg (ω f : SpatialCoordinates d → ℝ) :
    0 ≤ M.nodalCoefficientEnergy ω f :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (simplex_mass_factor_pos (M.simplex i)).le
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

theorem ae_of_cells (hS : IsOpen S) (hc : Convex ℝ S) {P : SpatialCoordinates d → Prop}
    (h : ∀ i, ∀ᵐ x ∂volume.restrict (M.cell i), P x) : ∀ᵐ x ∂volume.restrict S, P x := by
  have hl (i : ι) : ∀ᵐ x ∂volume.restrict S, x ∈ M.cell i → P x := by
    apply (ae_restrict_iff' (simplicialCell_measurable (M.simplex i).points)).mp
    rw [M.cell_restrict_domain hS hc i]
    exact h i
  filter_upwards [ae_all_iff.mpr hl,M.ae_partition hS.measurableSet] with x hx hp
  obtain ⟨i,hi,_⟩ := hp
  exact hx i hi

variable [IsFiniteMeasure (volume.restrict S)]

theorem nodal_weighted_norm_sq_sum (hS : IsOpen S) (hc : Convex ℝ S) (hM : M.FaceMatching)
    (w : BoundedMultiplier (volume.restrict S)) (f : SpatialCoordinates d → ℝ) :
    (w.seminorm (M.nodalLp hS.measurableSet hM f))^2 =
      ∑ i, ∫ x in M.cell i, |w.value x|^2*
        (simplexNodalInterpolant (M.simplex i) (fun k => f ((M.simplex i).points k)) x)^2 := by
  rw [w.seminorm_sq_integral,M.integral_eq_sum_cells hS hc _ (w.integrable_density _)]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [(M.nodalLp_ae hS.measurableSet hM f).filter_mono
    (ae_mono (M.cell_measure_le_domain hS hc i)),
    ae_restrict_mem (simplicialCell_measurable (M.simplex i).points)] with x hx hxi
  rw [hx,M.nodalFunction_on_cell hM f i hxi,Real.norm_eq_abs]
  simp only [sq_abs,localNodal]

theorem nodal_weighted_state_bound (hS : IsOpen S) (hc : Convex ℝ S) (hM : M.FaceMatching)
    (w : BoundedMultiplier (volume.restrict S)) (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    {θ : ℝ} (hθ : 0 < θ) (hg : ∀ i j, M.VertexNeighbors i j → a i ≤ θ*a j)
    (hb : ∀ i, ∀ᵐ x ∂volume.restrict (M.cell i), |w.value x| ≤ θ*a i)
    (f : SpatialCoordinates d → ℝ) :
    (w.seminorm (M.nodalLp hS.measurableSet hM f))^2 ≤
      θ^4*(d+2)*M.nodalCoefficientEnergy (M.nodalWeightMinimum a) f := by
  rw [M.nodal_weighted_norm_sq_sum hS hc hM,nodalCoefficientEnergy,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact weighted_simplex_state_bound (M.simplex i)
    (w.restrictMeasure (M.cell_measure_le_domain hS hc i))
    (fun k => f ((M.simplex i).points k))
    (fun k => M.nodalWeightMinimum a ((M.simplex i).points k)) hθ (ha i)
    (fun k => (M.nodalWeightMinimum_vertex_bounds a hθ hg i k).1) (hb i)

theorem nodal_weighted_test_bound (hS : IsOpen S) (hc : Convex ℝ S) (hM : M.FaceMatching)
    (w : BoundedMultiplier (volume.restrict S)) (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    {θ : ℝ} (hθ : 0 < θ) (hg : ∀ i j, M.VertexNeighbors i j → a i ≤ θ*a j)
    (hb : ∀ i, ∀ᵐ x ∂volume.restrict (M.cell i), |w.value x| ≤ θ/a i)
    (f : SpatialCoordinates d → ℝ) :
    (w.seminorm (M.nodalLp hS.measurableSet hM (fun x => (M.nodalWeightMinimum a x)^2*f x)))^2 ≤
      θ^2*(d+2)*M.nodalCoefficientEnergy (M.nodalWeightMinimum a) f := by
  rw [M.nodal_weighted_norm_sq_sum hS hc hM,nodalCoefficientEnergy,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact weighted_simplex_test_bound (M.simplex i)
    (w.restrictMeasure (M.cell_measure_le_domain hS hc i))
    (fun k => f ((M.simplex i).points k))
    (fun k => M.nodalWeightMinimum a ((M.simplex i).points k)) hθ (ha i)
    (fun k => (M.nodalWeightMinimum_pos a ha _).le)
    (fun k => (M.nodalWeightMinimum_vertex_bounds a hθ hg i k).2) (hb i)

end Carleman.SimplicialPartition
