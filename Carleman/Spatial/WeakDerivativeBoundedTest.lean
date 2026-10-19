module

public import Carleman.Spatial.BoundedTestRepresentation
public import Carleman.Spatial.SpatialTestOperations
public import Carleman.Spatial.DirichletPoincare

/-! A distributional derivative bounded in the actual L² test norm is an
actual L² weak derivative. The output includes the original quantitative
bound and all compactly supported smooth tests. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem exists_weakSpatialDerivative_of_test_bound (hS : IsOpen S)
    (u : Lp ℝ 2 (volume.restrict S)) (i : Fin d) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ φ : SpatialTest S,
      |inner ℝ u (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i))| ≤
        C*‖φ.toLp (volume.restrict S)‖) :
    ∃ v : Lp ℝ 2 (volume.restrict S), ‖v‖ ≤ C ∧
      IsWeakSpatialDerivative (volume.restrict S) S (EuclideanSpace.basisFun (Fin d) ℝ i) u v := by
  let P := Submodule.span ℝ (Set.range (fun φ : SpatialTest S => φ.sobolevJet))
  let J := (WeakSobolevJet.value (d := d) (m := 1) (ν := volume.restrict S) (S := S)).comp P.subtype
  let D := ((derivativeComponent (Sym.cons i Sym.nil)).comp (WeakSobolevJet.field 1)).comp P.subtype
  let L : P →ₗ[ℝ] ℝ :=
    { toFun := fun x => -inner ℝ u (D x)
      map_add' := by intro x y; simp only [map_add,inner_add_right,neg_add]
      map_smul' := by intro c x; simp only [map_smul,real_inner_smul_right,smul_eq_mul,RingHom.id_apply,mul_neg] }
  have hJ : Function.Injective J :=
    (WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)).comp Subtype.val_injective
  have hL (x : P) : |L x| ≤ C*‖J x‖ := by
    obtain ⟨φ,hφ⟩ := exists_test_of_mem_test_span hS x.property
    change |-inner ℝ u (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 (x : WeakSobolevJet d 1 (volume.restrict S) S)))| ≤
      C*‖WeakSobolevJet.value (x : WeakSobolevJet d 1 (volume.restrict S) S)‖
    rw [← hφ,φ.sobolevJet_value,φ.sobolevJet_derivative,abs_neg]
    exact hb φ
  obtain ⟨v,hv,he⟩ := exists_inner_of_bounded_test_functional (V := P)
    (H := Lp ℝ 2 (volume.restrict S)) J hJ L (C := C) hC hL
  refine ⟨v,hv,?_⟩
  intro φ
  have ht := he ⟨φ.sobolevJet,Submodule.subset_span (Set.mem_range_self φ)⟩
  change inner ℝ v (WeakSobolevJet.value φ.sobolevJet) =
    -inner ℝ u (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 φ.sobolevJet)) at ht
  rw [φ.sobolevJet_value,φ.sobolevJet_derivative] at ht
  linarith

theorem exists_weakSpatialDerivative_iff_test_bound (hS : IsOpen S)
    (u : Lp ℝ 2 (volume.restrict S)) (i : Fin d) {C : ℝ} (hC : 0 ≤ C) :
    (∃ v : Lp ℝ 2 (volume.restrict S), ‖v‖ ≤ C ∧
      IsWeakSpatialDerivative (volume.restrict S) S (EuclideanSpace.basisFun (Fin d) ℝ i) u v) ↔
    ∀ φ : SpatialTest S,
      |inner ℝ u (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i))| ≤
        C*‖φ.toLp (volume.restrict S)‖ := by
  constructor
  · rintro ⟨v,hv,hw⟩ φ
    rw [hw φ,abs_neg]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hv (norm_nonneg _))
  · exact exists_weakSpatialDerivative_of_test_bound hS u i hC

end Carleman
