module

public import Carleman.Spatial.SpatialTestOperations
public import Carleman.Spatial.TestPoincare

/-! The slab Poincare bound passes to the genuine H¹₀ closure by
continuity of the actual scalar value and gradient fields. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem SpatialTest.sobolevJet_derivative (φ : SpatialTest S) (i : Fin d) :
    derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 φ.sobolevJet) =
      φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i) := by
  change derivativeComponent (Sym.cons i Sym.nil)
    ((OperatorMultiplier.const derivativeOneFiber).map φ.fderivLp) = _
  rw [derivativeOneFiber_component]
  apply Lp.ext
  filter_upwards [OperatorMultiplier.const_map_ae
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)) φ.fderivLp,
    φ.fderivLp_ae,φ.derivativeLp_ae (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i)] with x hx hy hz
  rw [hx,hy,hz]
  rfl

theorem derivativeComponent_norm_le {k : ℕ} {ν : Measure (SpatialCoordinates d)}
    (α : Sym (Fin d) k) (u : Lp (DerivativeFiber d k) 2 ν) :
    ‖derivativeComponent α u‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [derivativeComponent_ae α u] with x hx
  rw [hx]
  exact PiLp.norm_apply_le (u x) α

theorem dirichlet_poincare (hS : IsOpen S) (i : Fin d) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ x ∈ S, |x i| ≤ R) (u : WeakSobolevJet d 1 (volume.restrict S) S)
    (hu : u ∈ dirichletJetSpace S) :
    ‖WeakSobolevJet.value u‖ ≤ 2*R*‖WeakSobolevJet.field 1 u‖ := by
  have hc : IsClosed {v : WeakSobolevJet d 1 (volume.restrict S) S |
      ‖WeakSobolevJet.value v‖ ≤ 2*R*‖WeakSobolevJet.field 1 v‖} :=
    isClosed_le WeakSobolevJet.valueCLM.continuous.norm
      (continuous_const.mul (WeakSobolevJet.fieldCLM 1).continuous.norm)
  apply closure_minimal (s := (Submodule.span ℝ (Set.range (fun φ : SpatialTest S => φ.sobolevJet)) : Set _)) _ hc hu
  intro v hv
  obtain ⟨φ,rfl⟩ := exists_test_of_mem_test_span hS hv
  change ‖WeakSobolevJet.value φ.sobolevJet‖ ≤ 2*R*‖WeakSobolevJet.field 1 φ.sobolevJet‖
  rw [SpatialTest.sobolevJet_value]
  have ht := φ.poincare_slab hS (EuclideanSpace.proj i)
    (EuclideanSpace.basisFun (Fin d) ℝ i) (by simp) hR0 hR
  rw [← φ.sobolevJet_derivative i] at ht
  exact ht.trans (mul_le_mul_of_nonneg_left (derivativeComponent_norm_le _ _) (by positivity))

end Carleman
