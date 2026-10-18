module

public import Carleman.Spatial.DirichletSpace

/-! The actual smooth test jets form a linear space. Thus the Dirichlet
definition is also literally the H¹ closure of these tests. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SpatialTest
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

def zeroTest : SpatialTest S where
  value := 0
  smooth := contDiff_const
  compact := HasCompactSupport.zero
  support := by simp

def addTest (φ ψ : SpatialTest S) : SpatialTest S where
  value := φ.value + ψ.value
  smooth := φ.smooth.add ψ.smooth
  compact := φ.compact.add ψ.compact
  support := (tsupport_add _ _).trans (union_subset φ.support ψ.support)

def smulTest (c : ℝ) (φ : SpatialTest S) : SpatialTest S where
  value x := c * φ.value x
  smooth := contDiff_const.mul φ.smooth
  compact := φ.compact.mul_left
  support := tsupport_mul_subset_right.trans φ.support

theorem zeroTest_jet (hS : IsOpen S) : (zeroTest (S := S)).sobolevJet = 0 := by
  apply WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)
  rw [sobolevJet_value,map_zero]
  apply Lp.ext
  filter_upwards [(zeroTest (S := S)).toLp_ae (volume.restrict S),Lp.coeFn_zero ℝ 2 (volume.restrict S)] with x hx hz
  rw [hx,hz]
  rfl

theorem addTest_jet (hS : IsOpen S) (φ ψ : SpatialTest S) :
    (φ.addTest ψ).sobolevJet = φ.sobolevJet + ψ.sobolevJet := by
  apply WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)
  rw [map_add,sobolevJet_value,sobolevJet_value,sobolevJet_value]
  apply Lp.ext
  filter_upwards [(φ.addTest ψ).toLp_ae (volume.restrict S),φ.toLp_ae (volume.restrict S),
    ψ.toLp_ae (volume.restrict S),Lp.coeFn_add (φ.toLp (volume.restrict S)) (ψ.toLp (volume.restrict S))] with x hx hy hz ha
  rw [hx,ha,Pi.add_apply,hy,hz]
  rfl

theorem smulTest_jet (hS : IsOpen S) (c : ℝ) (φ : SpatialTest S) :
    (φ.smulTest c).sobolevJet = c • φ.sobolevJet := by
  apply WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)
  rw [map_smul,sobolevJet_value,sobolevJet_value]
  apply Lp.ext
  filter_upwards [(φ.smulTest c).toLp_ae (volume.restrict S),φ.toLp_ae (volume.restrict S),
    Lp.coeFn_smul c (φ.toLp (volume.restrict S))] with x hx hy hs
  rw [hx,hs,Pi.smul_apply,hy]
  rfl

end SpatialTest

theorem exists_test_of_mem_test_span {d : ℕ} {S : Set (SpatialCoordinates d)} (hS : IsOpen S)
    {u : WeakSobolevJet d 1 (volume.restrict S) S}
    (hu : u ∈ Submodule.span ℝ (Set.range (fun φ : SpatialTest S => φ.sobolevJet))) :
    ∃ φ : SpatialTest S, φ.sobolevJet = u := by
  induction hu using Submodule.span_induction with
  | mem u hu => exact hu
  | zero => exact ⟨SpatialTest.zeroTest,SpatialTest.zeroTest_jet hS⟩
  | add u v _ _ hu hv =>
    obtain ⟨φ,rfl⟩ := hu
    obtain ⟨ψ,rfl⟩ := hv
    exact ⟨φ.addTest ψ,φ.addTest_jet hS ψ⟩
  | smul c u _ hu =>
    obtain ⟨φ,rfl⟩ := hu
    exact ⟨φ.smulTest c,φ.smulTest_jet hS c⟩

end Carleman
