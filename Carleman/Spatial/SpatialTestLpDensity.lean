module

public import Carleman.Spatial.SpatialTestOperations

/-! The original compactly supported smooth tests are dense in the physical L² space. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace Carleman

theorem spatialTest_toLp_denseRange {d : ℕ} {S : Set (SpatialCoordinates d)} (hS : IsOpen S) :
    DenseRange (fun φ : SpatialTest S => φ.toLp (volume.restrict S)) := by
  let P := Submodule.span ℝ (Set.range (fun φ : SpatialTest S => φ.sobolevJet))
  let D := P.map WeakSobolevJet.value
  have hd : Dense (D : Set (Lp ℝ 2 (volume.restrict S))) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top,Submodule.topologicalClosure_eq_top_iff]
    apply (Submodule.eq_bot_iff _).mpr
    intro u hu
    apply spatial_eq_zero_of_tests hS (ae_restrict_mem hS.measurableSet)
    intro φ
    exact (D.mem_orthogonal' u).mp hu _
      ⟨φ.sobolevJet,Submodule.subset_span (Set.mem_range_self φ),φ.sobolevJet_value⟩
  have he : (D : Set (Lp ℝ 2 (volume.restrict S)))=
      Set.range (fun φ : SpatialTest S => φ.toLp (volume.restrict S)) := by
    ext u
    constructor
    · rintro ⟨v,hv,rfl⟩
      obtain ⟨φ,rfl⟩ := exists_test_of_mem_test_span hS hv
      exact ⟨φ,φ.sobolevJet_value.symm⟩
    · rintro ⟨φ,rfl⟩
      exact ⟨φ.sobolevJet,Submodule.subset_span (Set.mem_range_self φ),φ.sobolevJet_value⟩
  rwa [he] at hd

end Carleman
