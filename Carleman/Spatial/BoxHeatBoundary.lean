module

public import Carleman.Geometry.CoordinateBoxHalfspaces
public import Carleman.Spatial.HalfspaceHeatBoundary

/-! Actual upper and lower coordinate-face flux signs, including all face edges. -/
@[expose] public noncomputable section
open Set
open scoped ContDiff BigOperators
namespace Carleman
variable {d : ℕ}

theorem box_face_gaussian_heat_flux (a b : Fin d → ℝ) (hpos : ∀ i, a i < b i)
    (c : SpatialCoordinates d) (hc : c ∈ openCoordinateBox a b)
    (i : Fin d) (upper : Bool) (x : SpatialCoordinates d)
    (hx : x ∈ closedCoordinateBox a b) (hface : x i=if upper then b i else a i)
    {l : ℝ} (hl : 0 ≤ l) {q : ℝ → ℝ}
    {L u k p : (ℝ × SpatialCoordinates d) → ℝ}
    (hL : ContDiff ℝ ∞ L) (hu : ContDiff ℝ ∞ u)
    (hk : ContDiff ℝ ∞ k) (hp : ContDiff ℝ ∞ p)
    (hformula : ∀ s y, L (s,y)=q s*interiorCarlemanProfile c l y)
    (hboundary : ∀ s : ℝ, ∀ y ∈ frontier (openCoordinateBox a b), u (s,y)=0)
    (t : ℝ) (hq : 0 ≤ q t) :
    let z := fun y => Real.exp (L y)*u y
    (if upper then pointwiseHeatFlux spaceTimeSpatialDirection (1,0) L k p z i (t,x)
     else -pointwiseHeatFlux spaceTimeSpatialDirection (1,0) L k p z i (t,x)) ≤ 0 := by
  have hc' : ∀ j, coordinateBoxThreshold a b j < coordinateBoxFunctional j c := by
    change c ∈ {y | ∀ j, coordinateBoxThreshold a b j < coordinateBoxFunctional j y}
    rwa [openCoordinateBox_halfspaces]
  have hx' : ∀ j, coordinateBoxThreshold a b j ≤ coordinateBoxFunctional j x := by
    change x ∈ {y | ∀ j, coordinateBoxThreshold a b j ≤ coordinateBoxFunctional j y}
    rwa [closedCoordinateBox_halfspaces]
  have he : coordinateBoxFunctional (i,upper) x=coordinateBoxThreshold a b (i,upper) := by
    rw [coordinateBoxFunctional_apply,hface]
    cases upper <;> rfl
  obtain ⟨w,hw,hwi⟩ := coordinateBox_face_witness a b hpos (i,upper)
  have hb : ∀ s : ℝ, ∀ y ∈ frontier
      {x | ∀ j, coordinateBoxThreshold a b j < coordinateBoxFunctional j x}, u (s,y)=0 := by
    rwa [openCoordinateBox_halfspaces]
  have h := finite_halfspace_closed_face_gaussian_heat_flux coordinateBoxFunctional
    (coordinateBoxThreshold a b) c hc' (i,upper) w hw hwi x he hx'
    hl hL hu hk hp hformula hb t hq
  dsimp only at h ⊢
  rw [coordinateBoxFunctional_normal] at h
  cases upper <;> simpa [EuclideanSpace.basisFun_apply] using h

end Carleman
