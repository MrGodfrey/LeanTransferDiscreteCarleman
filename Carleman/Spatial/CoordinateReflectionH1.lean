module

public import Carleman.Spatial.CoordinateReflectionLp
public import Carleman.Spatial.FirstComponentJet
public import Carleman.Spatial.WeakProductComponents

/-! Reflection preserves the original full weak H1 jet and its gradient
energy. The same complete weak tests are used before and after reflection. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman.WeakSobolevJet
variable {d : ℕ}

def reflectCoordinate (r : Fin d) (c : ℝ) (u : WeakSobolevJet d 1 volume univ) :
    WeakSobolevJet d 1 volume univ :=
  firstComponentJet (coordinateReflectionLp r c (value u))
    (fun i => coordinateReflectionSign r i • coordinateReflectionLp r c
      (derivativeComponent (Sym.cons i Sym.nil) (field 1 u)))
    (fun i => (u.property 0 Sym.nil i).coordinate_reflection r c i)

theorem reflectCoordinate_value (r : Fin d) (c : ℝ) (u : WeakSobolevJet d 1 volume univ) :
    value (reflectCoordinate r c u)=coordinateReflectionLp r c (value u) := firstComponentJet_value _ _ _

theorem reflectCoordinate_gradient (r : Fin d) (c : ℝ) (u : WeakSobolevJet d 1 volume univ) (i : Fin d) :
    derivativeComponent (Sym.cons i Sym.nil) (field 1 (reflectCoordinate r c u))=
      coordinateReflectionSign r i • coordinateReflectionLp r c
        (derivativeComponent (Sym.cons i Sym.nil) (field 1 u)) := firstComponentJet_gradient _ _ _ i

theorem reflectCoordinate_involutive (r : Fin d) (c : ℝ) (u : WeakSobolevJet d 1 volume univ) :
    reflectCoordinate r c (reflectCoordinate r c u)=u := by
  apply value_injective isOpen_univ (Filter.Eventually.of_forall fun _ => mem_univ _)
  rw [reflectCoordinate_value,reflectCoordinate_value,coordinateReflectionLp_involutive]

theorem reflectCoordinate_value_norm (r : Fin d) (c : ℝ) (u : WeakSobolevJet d 1 volume univ) :
    ‖value (reflectCoordinate r c u)‖=‖value u‖ := by
  rw [reflectCoordinate_value,coordinateReflectionLp_norm]

theorem reflectCoordinate_gradient_pairing (r : Fin d) (c : ℝ)
    (u v : WeakSobolevJet d 1 volume univ) :
    weakGradientPairing (reflectCoordinate r c u) (reflectCoordinate r c v)=weakGradientPairing u v := by
  rw [weakGradientPairing_coordinates,weakGradientPairing_coordinates]
  apply Finset.sum_congr rfl
  intro i _
  rw [reflectCoordinate_gradient,reflectCoordinate_gradient,real_inner_smul_left,real_inner_smul_right,
    coordinateReflectionLp_inner_both]
  rw [← mul_assoc, ← pow_two, coordinateReflectionSign_sq, one_mul]

theorem reflectCoordinate_gradient_norm (r : Fin d) (c : ℝ) (u : WeakSobolevJet d 1 volume univ) :
    ‖field 1 (reflectCoordinate r c u)‖=‖field 1 u‖ := by
  have hh := reflectCoordinate_gradient_pairing r c u u
  rw [weakGradientPairing_apply,weakGradientPairing_apply,real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq] at hh
  nlinarith [norm_nonneg (field (m := 1) 1 (reflectCoordinate r c u)),norm_nonneg (field (m := 1) 1 u)]

theorem reflectCoordinate_gradient_adjoint (r : Fin d) (c : ℝ)
    (u v : WeakSobolevJet d 1 volume univ) :
    weakGradientPairing (reflectCoordinate r c u) v=weakGradientPairing u (reflectCoordinate r c v) := by
  rw [← reflectCoordinate_gradient_pairing r c u (reflectCoordinate r c v),reflectCoordinate_involutive]

end Carleman.WeakSobolevJet
