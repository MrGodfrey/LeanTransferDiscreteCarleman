module

public import Carleman.Geometry.HalfspaceOutwardNormal
public import Carleman.Geometry.ClosedCoordinateFaces

/-! Coordinate boxes as actual halfspace intersections, with explicit facet witnesses. -/
@[expose] public noncomputable section
open Set
namespace Carleman
variable {d : ℕ}

def coordinateBoxFunctional (j : Fin d × Bool) : SpatialCoordinates d →L[ℝ] ℝ :=
  if j.2 then -(InnerProductSpace.toDual ℝ _ (EuclideanSpace.basisFun (Fin d) ℝ j.1))
  else InnerProductSpace.toDual ℝ _ (EuclideanSpace.basisFun (Fin d) ℝ j.1)

def coordinateBoxThreshold (a b : Fin d → ℝ) (j : Fin d × Bool) : ℝ :=
  if j.2 then -b j.1 else a j.1

theorem coordinateBoxFunctional_apply (j : Fin d × Bool) (x : SpatialCoordinates d) :
    coordinateBoxFunctional j x=if j.2 then -x j.1 else x j.1 := by
  rcases j with ⟨i,e⟩
  have he : InnerProductSpace.toDual ℝ _ (EuclideanSpace.basisFun (Fin d) ℝ i) x=x i :=
    EuclideanSpace.basisFun_inner (Fin d) ℝ x i
  cases e
  · exact he
  · exact congrArg Neg.neg he

theorem openCoordinateBox_halfspaces (a b : Fin d → ℝ) :
    {x | ∀ j, coordinateBoxThreshold a b j < coordinateBoxFunctional j x}=
      openCoordinateBox a b := by
  ext x
  constructor
  · intro h i
    have h0 := h (i,false)
    have h1 := h (i,true)
    exact ⟨by simpa [coordinateBoxThreshold,coordinateBoxFunctional_apply] using h0,
      by simpa [coordinateBoxThreshold,coordinateBoxFunctional_apply] using h1⟩
  · intro h
    rintro ⟨i,e⟩
    cases e
    · simpa [coordinateBoxThreshold,coordinateBoxFunctional_apply] using (h i).1
    · simpa [coordinateBoxThreshold,coordinateBoxFunctional_apply] using (h i).2

theorem closedCoordinateBox_halfspaces (a b : Fin d → ℝ) :
    {x | ∀ j, coordinateBoxThreshold a b j ≤ coordinateBoxFunctional j x}=
      closedCoordinateBox a b := by
  ext x
  constructor
  · intro h i
    have h0 := h (i,false)
    have h1 := h (i,true)
    exact ⟨by simpa [coordinateBoxThreshold,coordinateBoxFunctional_apply] using h0,
      by simpa [coordinateBoxThreshold,coordinateBoxFunctional_apply] using h1⟩
  · intro h
    rintro ⟨i,e⟩
    cases e
    · simpa [coordinateBoxThreshold,coordinateBoxFunctional_apply] using (h i).1
    · simpa [coordinateBoxThreshold,coordinateBoxFunctional_apply] using (h i).2

theorem coordinateBoxFunctional_normal (j : Fin d × Bool) :
    halfspaceOutwardNormal (coordinateBoxFunctional j)=
      if j.2 then EuclideanSpace.basisFun (Fin d) ℝ j.1
      else -(EuclideanSpace.basisFun (Fin d) ℝ j.1) := by
  rcases j with ⟨i,e⟩
  cases e <;> simp [coordinateBoxFunctional,halfspaceOutwardNormal]

theorem coordinateBox_face_witness (a b : Fin d → ℝ) (hpos : ∀ i, a i < b i)
    (j : Fin d × Bool) :
    ∃ w : SpatialCoordinates d,
      coordinateBoxFunctional j w=coordinateBoxThreshold a b j ∧
      ∀ k, k ≠ j → coordinateBoxThreshold a b k < coordinateBoxFunctional k w := by
  classical
  let w : SpatialCoordinates d := WithLp.toLp 2 (Function.update
    (fun i => (a i+b i)/2) j.1 (if j.2 then b j.1 else a j.1))
  refine ⟨w,?_,?_⟩
  · rw [coordinateBoxFunctional_apply]
    cases h : j.2 <;> simp [w,coordinateBoxThreshold,h]
  · rintro ⟨i,e⟩ hne
    rw [coordinateBoxFunctional_apply]
    by_cases hi : i=j.1
    · subst i
      have he : e ≠ j.2 := by
        intro h
        apply hne
        exact Prod.ext rfl h
      cases hj : j.2 <;> cases e <;>
        simp_all [w,coordinateBoxThreshold]
    · have hmid := hpos i
      cases e <;> simp [w,coordinateBoxThreshold,hi] <;> linarith

end Carleman
