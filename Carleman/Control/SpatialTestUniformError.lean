module

public import Carleman.Control.CartesianTensorTestConsistency
public import Carleman.Control.P1TensorTestConsistency

/-! Actual spatial test errors, including the original Cartesian boundary strips. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology NNReal BigOperators ContDiff
namespace Carleman
variable {d : ℕ}

theorem cartesian_test_cell_uniform_error (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (φ : SpatialTest (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))
    {C : ℝ≥0} (hφ : LipschitzWith C φ.value) (h : ℝ) (hh : 0 < h) (hstep : ∀ j, δ j ≤ h) :
    ∀ᵐ x ∂volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)),
      |finiteCellFunction (cartesianDualCell o δ N) (cartesianNodalSample o δ hδ N φ.value) x-φ.value x|
        ≤ C*(d+1:ℝ)*h := by
  apply (cartesianKuhnPartition o δ hδ N).ae_of_cells (openCoordinateBox_isOpen _ _) (openCoordinateBox_convex _ _)
  intro i
  let z := (cartesianCellLatticeIndex N i).1
  let S := cartesianFiniteSimplex o δ hδ N i
  filter_upwards [cartesianKuhnSimplex_nearest_vertex_ae o δ hδ z i.2,
    ae_restrict_mem (simplicialCell_measurable S.points)] with x hn hx
  obtain ⟨k,hk⟩ := hn
  change ∀ j, |x j-S.points k j| < δ j/2 at hk
  have hv : S.points k=cartesianGridPoint o δ (kuhnVertexIndex z i.2 k) :=
    cartesianKuhnSimplex_points_eq_gridPoint o δ hδ z i.2 k
  have he := cartesianCellFunction_nearest_value o δ hδ N (cartesianNodalSample o δ hδ N φ.value)
    (kuhnVertexIndex z i.2 k) x (by intro j; rw [← hv]; exact hk j)
  rw [← hv] at he
  rw [he,cartesianInteriorData_test_vertex]
  have hd := ((cartesianKuhnPartition o δ hδ N).dist_le_cellDiameter i
    (subset_convexHull ℝ _ (Set.mem_range_self k)) hx).trans
      (cartesianKuhn_cellDiameter_le o δ hδ N h hh hstep i)
  change dist (S.points k) x ≤ (d+1:ℝ)*h at hd
  exact (hφ.dist_le_mul (S.points k) x).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hd C.coe_nonneg)

theorem cartesian_box_test_cell_uniform_error (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j)
    (φ : SpatialTest (openCoordinateBox lo hi)) {C : ℝ≥0} (hφ : LipschitzWith C φ.value)
    (h : ℝ) (hh : 0 < h) (hstep : ∀ j, δ j ≤ h) :
    ∀ᵐ x ∂volume.restrict (openCoordinateBox lo hi),
      |finiteCellFunction (cartesianDualCell lo δ N) (cartesianNodalSample lo δ hδ N φ.value) x-φ.value x|
        ≤ C*(d+1:ℝ)*h := by
  have he := funext hbox
  subst hi
  exact cartesian_test_cell_uniform_error lo δ hδ N φ hφ h hh hstep

theorem p1_test_uniform_error {S : Set (SpatialCoordinates d)} (hS : IsOpen S)
    {ι : Type*} [Fintype ι] (M : SimplicialPartition S ι) (hM : M.FaceMatching)
    (φ : SpatialTest S) {C : ℝ≥0} (hφ : LipschitzWith C φ.value) :
    ∀ᵐ x ∂volume.restrict S, |M.nodalFunction φ.value x-φ.value x| ≤ 2*C*M.maxDiameter := by
  filter_upwards [M.ae_partition hS.measurableSet] with x hx
  obtain ⟨i,hi,_⟩ := hx
  rw [abs_sub_comm]
  exact M.nodal_lipschitz_value_error hM φ.value hφ i hi

end Carleman
