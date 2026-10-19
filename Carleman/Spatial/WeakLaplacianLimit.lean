module

public import Carleman.Spatial.DirichletDistribution

/-! The actual distributional Laplacian survives weak gradient limits.
Its L² right side is uniquely determined by all original smooth tests. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Carleman.IsWeakNegativeLaplacian
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem unique_rhs (hS : IsOpen S) {u : WeakSobolevJet d 1 (volume.restrict S) S}
    {f g : Lp ℝ 2 (volume.restrict S)} (hf : IsWeakNegativeLaplacian u f)
    (hg : IsWeakNegativeLaplacian u g) : f=g := by
  apply sub_eq_zero.mp
  apply spatial_eq_zero_of_tests hS (ae_restrict_mem hS.measurableSet)
  intro φ
  rw [inner_sub_left]
  rw [← hf φ,← hg φ,sub_self]

theorem of_weak_gradient_limit
    (u : WeakSobolevJet d 1 (volume.restrict S) S)
    (U : ℕ → WeakSobolevJet d 1 (volume.restrict S) S) (f : Lp ℝ 2 (volume.restrict S))
    (hlim : ∀ z : Lp (DerivativeFiber d 1) 2 (volume.restrict S),
      Tendsto (fun n => inner ℝ (WeakSobolevJet.field 1 (U n)) z) atTop
        (𝓝 (inner ℝ (WeakSobolevJet.field 1 u) z)))
    (hid : ∀ φ : SpatialTest S, ∀ᶠ n in atTop,
      weakGradientPairing (U n) φ.sobolevJet = inner ℝ f (φ.toLp (volume.restrict S))) :
    IsWeakNegativeLaplacian u f := by
  intro φ
  have ht : Tendsto (fun n => weakGradientPairing (U n) φ.sobolevJet) atTop
      (𝓝 (weakGradientPairing u φ.sobolevJet)) := hlim (WeakSobolevJet.field 1 φ.sobolevJet)
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm (hid φ)))

end Carleman.IsWeakNegativeLaplacian
