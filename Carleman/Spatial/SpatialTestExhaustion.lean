module

public import Carleman.Spatial.SubdomainRestriction

/-! Every original compactly supported test lies eventually inside an
increasing open exhaustion. The index is allowed to depend on the test. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem SpatialTest.eventually_support_subset (φ : SpatialTest S)
    (T : ℕ → Set (SpatialCoordinates d)) (hT : ∀ n, IsOpen (T n))
    (hm : Monotone T) (hc : S ⊆ ⋃ n, T n) :
    ∀ᶠ n in atTop, tsupport φ.value ⊆ T n := by
  obtain ⟨N,hN⟩ := φ.compact.elim_directed_cover T hT (φ.support.trans hc)
    (fun i j => ⟨max i j,hm (le_max_left i j),hm (le_max_right i j)⟩)
  exact eventually_atTop.mpr ⟨N,fun n hn => hN.trans (hm hn)⟩

end Carleman
