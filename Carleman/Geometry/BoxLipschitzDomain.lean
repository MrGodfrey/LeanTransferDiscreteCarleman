module

public import Carleman.Geometry.FiniteHalfspaceCharts
public import Carleman.Geometry.CoordinateBoxChart

/-! Positive coordinate boxes have genuine local Lipschitz graph charts,
including corners where several faces are simultaneously active. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set
namespace Carleman

theorem openCoordinateBox_bounded_lipschitz {d : ℕ} (lo hi : Fin (d+1) → ℝ)
    (hpos : ∀ i, lo i < hi i) :
    IsBoundedLipschitzDomain (openCoordinateBox lo hi) (SpatialCoordinates d) := by
  let ℓ : Fin (d+1) × Bool → SpatialCoordinates (d+1) →L[ℝ] ℝ :=
    fun i => if i.2 then EuclideanSpace.proj i.1 else -(EuclideanSpace.proj i.1)
  let b : Fin (d+1) × Bool → ℝ := fun i => if i.2 then lo i.1 else -hi i.1
  let x₀ : SpatialCoordinates (d+1) := WithLp.toLp 2 (fun i => (lo i+hi i)/2)
  have hx₀ : ∀ i, b i < ℓ i x₀ := by
    rintro ⟨i,e⟩
    cases e <;> simp [ℓ,b,x₀] <;> linarith [hpos i]
  have hS : {x | ∀ i, b i < ℓ i x}=openCoordinateBox lo hi := by
    ext x
    constructor
    · intro h i
      have hl := h (i,true)
      have hu := h (i,false)
      exact ⟨by simpa [ℓ,b] using hl,by simpa [ℓ,b] using hu⟩
    · intro h
      rintro ⟨i,e⟩
      cases e
      · simpa [ℓ,b] using (h i).2
      · simpa [ℓ,b] using (h i).1
  have hb : Bornology.IsBounded {x | ∀ i, b i < ℓ i x} := by
    rw [hS]
    exact openCoordinateBox_isBounded lo hi
  rw [← hS]
  exact finite_halfspace_bounded_lipschitz ℓ b x₀ hx₀ hb

end Carleman
