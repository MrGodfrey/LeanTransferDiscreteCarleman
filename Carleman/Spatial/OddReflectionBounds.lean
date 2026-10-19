module

public import Carleman.Spatial.OddReflectionDirichlet

/-! Actual odd extension has quantitative L2 and weak gradient bounds,
uniform in the coordinate face and in the state. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem oddExtendLp_norm_le (hS : MeasurableSet S) (f : Lp ℝ 2 (volume.restrict S))
    (r : Fin d) (c : ℝ) : ‖oddExtendLp hS f r c‖ ≤ 2*‖f‖ := by
  unfold oddExtendLp
  calc
    _ ≤ ‖zeroExtendLp hS f‖+‖coordinateReflectionLp r c (zeroExtendLp hS f)‖ := norm_sub_le _ _
    _ = _ := by rw [coordinateReflectionLp_norm,zeroExtendLp_norm]; ring

theorem WeakSobolevJet.oddExtend_value_norm_le (hS : IsOpen S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (r : Fin d) (c : ℝ) : ‖value (oddExtend hS u hu r c)‖ ≤ 2*‖value u‖ := by
  rw [oddExtend,map_sub,reflectCoordinate_value,zeroExtendDirichlet_value]
  exact oddExtendLp_norm_le hS.measurableSet (value u) r c

theorem WeakSobolevJet.oddExtend_gradient_norm_le (hS : IsOpen S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (r : Fin d) (c : ℝ) : ‖field 1 (oddExtend hS u hu r c)‖ ≤ 2*‖field 1 u‖ := by
  rw [oddExtend,map_sub]
  calc
    _ ≤ ‖field 1 (zeroExtendDirichlet hS u hu)‖+
      ‖field 1 (reflectCoordinate r c (zeroExtendDirichlet hS u hu))‖ := norm_sub_le _ _
    _ = _ := by rw [reflectCoordinate_gradient_norm,zeroExtendDirichlet_field_norm]; ring

end Carleman
