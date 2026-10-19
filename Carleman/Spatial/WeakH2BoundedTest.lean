module

public import Carleman.Spatial.SecondOrderJetAssembly
public import Carleman.Spatial.WeakDerivativeBoundedTest
public import Carleman.Spatial.WeakMixedDerivative
public import Mathlib.Data.Sym.Sym2

/-! Quantitative H² membership from bounds on the distributional
coordinate derivatives of the original weak gradient. The actual mixed
weak derivatives commute and are stored once per unordered multi-index. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem exists_weakH2_of_gradient_test_bounds (hS : IsOpen S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ (i j : Fin d) (φ : SpatialTest S),
      |inner ℝ (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))
        (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ j))| ≤
      C*‖φ.toLp (volume.restrict S)‖) :
    ∃ U : WeakSobolevJet d 2 (volume.restrict S) S,
      WeakSobolevJet.truncate (by omega : 1 ≤ 2) U = u ∧
      ‖WeakSobolevJet.field 2 U‖^2 ≤ (Fintype.card (Sym (Fin d) 2) : ℝ)*C^2 := by
  choose D hnorm hD using fun i j => exists_weakSpatialDerivative_of_test_bound hS
    (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)) j hC (hb i j)
  have hs (i j : Fin d) : D i j = D j i :=
    IsWeakSpatialDerivative.mixed_commute hS (ae_restrict_mem hS.measurableSet)
      (u.property 0 Sym.nil i) (u.property 0 Sym.nil j) (hD i j) (hD j i)
  let v : Sym (Fin d) 2 → Lp ℝ 2 (volume.restrict S) :=
    fun α => Sym2.lift ⟨D,hs⟩ ((Sym2.equivSym (Fin d)).symm α)
  have he (i j : Fin d) : (Sym2.equivSym (Fin d)) (Sym2.mk i j) = Sym.cons i (Sym.cons j Sym.nil) := rfl
  have hv (i j : Fin d) : v (Sym.cons j (Sym.cons i Sym.nil)) = D i j := by
    change Sym2.lift ⟨D,hs⟩ ((Sym2.equivSym (Fin d)).symm (Sym.cons j (Sym.cons i Sym.nil))) = D i j
    rw [← he,Equiv.symm_apply_apply,Sym2.lift_mk]
    exact hs j i
  have hA (i j : Fin d) : IsWeakSpatialDerivative (volume.restrict S) S
      (EuclideanSpace.basisFun (Fin d) ℝ j)
      (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))
      (derivativeComponent (Sym.cons j (Sym.cons i Sym.nil)) (derivativeFieldAssembly v)) := by
    rw [derivativeFieldAssembly_component,hv]
    exact hD i j
  refine ⟨secondOrderJet u (derivativeFieldAssembly v) hA,secondOrderJet_truncate _ _ _,?_⟩
  rw [secondOrderJet_hessian,derivativeFieldAssembly_norm_sq]
  have hn (α : Sym (Fin d) 2) : ‖v α‖ ≤ C := by
    obtain ⟨j,β,rfl⟩ := Sym.exists_eq_cons_of_succ α
    obtain ⟨i,γ,rfl⟩ := Sym.exists_eq_cons_of_succ β
    rw [Sym.eq_nil_of_card_zero γ,hv]
    exact hnorm i j
  calc
    _ ≤ ∑ _α : Sym (Fin d) 2, C^2 := by
      apply Finset.sum_le_sum
      intro α _
      exact pow_le_pow_left₀ (norm_nonneg _) (hn α) 2
    _ = _ := by simp

end Carleman
