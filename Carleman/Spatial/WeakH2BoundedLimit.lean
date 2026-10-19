module

public import Carleman.Spatial.WeakH2BoundedTest

/-! Recover a genuine H² jet from uniformly bounded candidate Hessian
components whose test identities hold eventually. No H² zero extension or
convergence of the candidate Hessians is assumed. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem exists_weakH2_of_gradient_test_limits (hS : IsOpen S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S)
    (G : ℕ → Fin d → Lp ℝ 2 (volume.restrict S))
    (A : ℕ → Fin d → Fin d → Lp ℝ 2 (volume.restrict S)) {C : ℝ} (hC : 0 ≤ C)
    (hlim : ∀ (i j : Fin d) (φ : SpatialTest S), Tendsto
      (fun n => inner ℝ (G n i) (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ j)))
      atTop (𝓝 (inner ℝ (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))
        (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ j)))))
    (hid : ∀ (i j : Fin d) (φ : SpatialTest S), ∀ᶠ n in atTop,
      inner ℝ (G n i) (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ j)) =
        -inner ℝ (A n i j) (φ.toLp (volume.restrict S)))
    (hbound : ∀ i j : Fin d, ∀ᶠ n in atTop, ‖A n i j‖ ≤ C) :
    ∃ U : WeakSobolevJet d 2 (volume.restrict S) S,
      WeakSobolevJet.truncate (by omega : 1 ≤ 2) U = u ∧
      ‖WeakSobolevJet.field 2 U‖^2 ≤ (Fintype.card (Sym (Fin d) 2) : ℝ)*C^2 := by
  apply exists_weakH2_of_gradient_test_bounds hS u hC
  intro i j φ
  apply le_of_tendsto (hlim i j φ).abs
  filter_upwards [hid i j φ,hbound i j] with n hn hb
  rw [hn,abs_neg]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

theorem exists_weakH2_of_strong_H1_limit_bounded (hS : IsOpen S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S)
    (U : ℕ → WeakSobolevJet d 2 (volume.restrict S) S) {C : ℝ} (hC : 0 ≤ C)
    (hlim : Tendsto (fun n => WeakSobolevJet.truncate (by omega : 1 ≤ 2) (U n)) atTop (𝓝 u))
    (hbound : ∀ᶠ n in atTop, ‖WeakSobolevJet.field 2 (U n)‖ ≤ C) :
    ∃ V : WeakSobolevJet d 2 (volume.restrict S) S,
      WeakSobolevJet.truncate (by omega : 1 ≤ 2) V = u ∧
      ‖WeakSobolevJet.field 2 V‖^2 ≤ (Fintype.card (Sym (Fin d) 2) : ℝ)*C^2 := by
  let G := fun n i => derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 (U n))
  let A := fun n i j => derivativeComponent (Sym.cons j (Sym.cons i Sym.nil)) (WeakSobolevJet.field 2 (U n))
  apply exists_weakH2_of_gradient_test_limits hS u G A hC
  · intro i j φ
    have ht := (((derivativeComponentCLM (Sym.cons i Sym.nil)).continuous.comp
      (WeakSobolevJet.fieldCLM (m := 1) 1).continuous).tendsto u).comp hlim
    exact ht.inner tendsto_const_nhds
  · intro i j φ
    exact Eventually.of_forall fun n => (U n).property 1 (Sym.cons i Sym.nil) j φ
  · intro i j
    filter_upwards [hbound] with n hn
    exact (derivativeComponent_norm_le _ _).trans hn

end Carleman
