module

public import Carleman.Spatial.UniformNodalWeight
public import Carleman.Spatial.SimplexMassIntegral
public import Carleman.Spatial.NodalDirichletMembership
public import Carleman.Spatial.RealL2Integral

/-! Genuine zero-boundary nodal weighted tests and their global mass coercivity.
No converse representation of the full H¹-conforming P1 space is assumed. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}
  (M : Carleman.SimplicialPartition S ι) [IsFiniteMeasure (volume.restrict S)]

theorem nodal_squared_weight_test_mem (hS : IsOpen S) (hc : Convex ℝ S)
    (hM : M.FaceMatching) (hB : M.BoundaryFitted) (ω f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k)=0) :
    M.nodalLp hS.measurableSet hM (fun x => (ω x)^2*f x) ∈
      M.conformingSpace (dirichletSubspace S) := by
  apply M.nodalLp_mem_dirichletConformingSpace hS hc hM hB
  intro i k hk
  rw [hf i k hk,mul_zero]

theorem nodal_weighted_mass_coercive (hS : IsOpen S) (hc : Convex ℝ S)
    (hM : M.FaceMatching) (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    {γ : ℝ} (hγ : 1 ≤ γ) (hg : ∀ i j, M.VertexNeighbors i j → a i ≤ γ*a j)
    (f : SpatialCoordinates d → ℝ) :
    let ω := M.nodalWeightMinimum a
    p1MassMargin d γ * ∑ i, volume.real (M.cell i)/((d+1:ℝ)*(d+2))*
      (∑ k, (ω ((M.simplex i).points k)*f ((M.simplex i).points k))^2) ≤
    ∫ x in S, M.nodalFunction f x * M.nodalFunction (fun y => (ω y)^2*f y) x := by
  dsimp only
  let ω := M.nodalWeightMinimum a
  have hint : Integrable (fun x => M.nodalFunction f x *
      M.nodalFunction (fun y => (ω y)^2*f y) x) (volume.restrict S) :=
    (M.nodalFunction_memLp hS.measurableSet hM f).integrable_mul
      (M.nodalFunction_memLp hS.measurableSet hM (fun y => (ω y)^2*f y))
  rw [M.integral_eq_sum_cells hS hc _ hint,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hb := M.nodalWeightMinimum_vertex_bounds a (zero_lt_one.trans_le hγ) hg i
  have hh := weighted_simplex_mass_coercive (M.simplex i)
    (fun k => f ((M.simplex i).points k)) (fun k => ω ((M.simplex i).points k)) hγ
    (div_pos (ha i) (zero_lt_one.trans_le hγ)) (fun k => (hb k).1)
    (fun k => by simpa only [mul_div_cancel₀ _ (ne_of_gt (zero_lt_one.trans_le hγ)),
      mul_div_cancel_left₀ _ (ne_of_gt (zero_lt_one.trans_le hγ))] using (hb k).2)
  have he : (∫ x in M.cell i, M.nodalFunction f x * M.nodalFunction (fun y => (ω y)^2*f y) x) =
      ∫ x in M.cell i, simplexNodalInterpolant (M.simplex i) (fun k => f ((M.simplex i).points k)) x *
        simplexNodalInterpolant (M.simplex i) (fun k => (ω ((M.simplex i).points k))^2*
          f ((M.simplex i).points k)) x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (simplicialCell_measurable (M.simplex i).points)] with x hx
    rw [M.nodalFunction_on_cell hM f i hx,M.nodalFunction_on_cell hM _ i hx]
    rfl
  rw [he]
  convert hh using 1
  ring


theorem nodal_weighted_pairing_coercive (hS : IsOpen S) (hc : Convex ℝ S)
    (hM : M.FaceMatching) (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    {γ : ℝ} (hγ : 1 ≤ γ) (hg : ∀ i j, M.VertexNeighbors i j → a i ≤ γ*a j)
    (f : SpatialCoordinates d → ℝ) :
    let ω := M.nodalWeightMinimum a
    p1MassMargin d γ * ∑ i, volume.real (M.cell i)/((d+1:ℝ)*(d+2))*
      (∑ k, (ω ((M.simplex i).points k)*f ((M.simplex i).points k))^2) ≤
    inner ℝ (M.nodalLp hS.measurableSet hM f)
      (M.nodalLp hS.measurableSet hM (fun x => (ω x)^2*f x)) := by
  have h := M.nodal_weighted_mass_coercive hS hc hM a ha hγ hg f
  dsimp only at h ⊢
  rw [integral_mul_eq_L2_inner (M.nodalFunction_memLp hS.measurableSet hM f)
    (M.nodalFunction_memLp hS.measurableSet hM (fun x => (M.nodalWeightMinimum a x)^2*f x))] at h
  exact h

end Carleman.SimplicialPartition
