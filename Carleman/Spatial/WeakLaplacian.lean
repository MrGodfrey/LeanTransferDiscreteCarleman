module

public import Carleman.Spatial.GradientPairing
public import Carleman.Spatial.SobolevTruncation

/-! The actual negative Laplacian of an H² jet satisfies Green's
identity against all H¹₀ jets, by the full smooth-test definition and closure. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

def negativeLaplacian : WeakSobolevJet d 2 (volume.restrict S) S →L[ℝ] Lp ℝ 2 (volume.restrict S) :=
  -∑ i : Fin d, (derivativeComponentCLM (Sym.cons i (Sym.cons i Sym.nil))).comp (WeakSobolevJet.fieldCLM 2)

theorem negativeLaplacian_apply (u : WeakSobolevJet d 2 (volume.restrict S) S) :
    negativeLaplacian u = -∑ i : Fin d,
      derivativeComponent (Sym.cons i (Sym.cons i Sym.nil)) (WeakSobolevJet.field 2 u) := by
  simp only [negativeLaplacian,neg_apply,sum_apply,ContinuousLinearMap.comp_apply,
    derivativeComponentCLM_apply]
  rfl

theorem negativeLaplacian_test (u : WeakSobolevJet d 2 (volume.restrict S) S) (φ : SpatialTest S) :
    weakGradientPairing (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u) φ.sobolevJet =
      inner ℝ (negativeLaplacian u) (φ.toLp (volume.restrict S)) := by
  rw [weakGradientPairing_apply,firstDerivativeField_inner,negativeLaplacian_apply,
    inner_neg_left,sum_inner,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [φ.sobolevJet_derivative]
  exact u.property (1 : Fin 2) (Sym.cons i Sym.nil) i φ

theorem negativeLaplacian_dirichlet (hS : IsOpen S)
    (u : WeakSobolevJet d 2 (volume.restrict S) S)
    (v : WeakSobolevJet d 1 (volume.restrict S) S) (hv : v ∈ dirichletJetSpace S) :
    weakGradientPairing (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u) v =
      inner ℝ (negativeLaplacian u) (WeakSobolevJet.value v) := by
  have hc : IsClosed {w : WeakSobolevJet d 1 (volume.restrict S) S |
      weakGradientPairing (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u) w =
        inner ℝ (negativeLaplacian u) (WeakSobolevJet.value w)} :=
    isClosed_eq (weakGradientPairing _).continuous
      (continuous_const.inner WeakSobolevJet.valueCLM.continuous)
  apply closure_minimal (s := (Submodule.span ℝ (Set.range (fun φ : SpatialTest S => φ.sobolevJet)) : Set _)) _ hc hv
  intro w hw
  obtain ⟨φ,rfl⟩ := exists_test_of_mem_test_span hS hw
  change weakGradientPairing _ φ.sobolevJet = inner ℝ (negativeLaplacian u) (WeakSobolevJet.value φ.sobolevJet)
  rw [φ.sobolevJet_value]
  exact negativeLaplacian_test u φ

end Carleman
