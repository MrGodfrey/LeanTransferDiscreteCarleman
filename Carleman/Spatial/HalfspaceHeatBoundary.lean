module

public import Carleman.Geometry.HalfspaceOutwardNormal
public import Carleman.Spatial.PlaneHeatFlux

/-! Flat-face heat flux for the actual boundary of a finite halfspace domain.
The unit normal, support condition, and local zero data are supplied internally. -/
@[expose] public noncomputable section
open Set
open scoped ContDiff BigOperators
namespace Carleman
variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem pointwiseHeatFlux_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : ι → E) (t : E) {l k p z : E → ℝ}
    (hl : ContDiff ℝ ∞ l) (hk : ContDiff ℝ ∞ k)
    (hp : ContDiff ℝ ∞ p) (hz : ContDiff ℝ ∞ z) (i : ι) :
    ContDiff ℝ ∞ (pointwiseHeatFlux e t l k p z i) := by
  have h1 := (smoothD_contDiff hz t).mul (smoothD_contDiff hz (e i))
  have h2 := (directionalPair_contDiff e hl hz).mul (smoothD_contDiff hz (e i))
  have h3 := (directionalEnergy_contDiff e hz).mul (smoothD_contDiff hl (e i))
  have h4 := (hp.mul hz).mul (smoothD_contDiff hz (e i))
  have h5 := (hk.mul (hz.pow 2)).mul (smoothD_contDiff hl (e i))
  exact ((((contDiff_const.mul h1).add (contDiff_const.mul h2)).sub
    (contDiff_const.mul h3)).sub (contDiff_const.mul h4)).add (contDiff_const.mul h5)

theorem finite_halfspace_gaussian_heat_flux
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ)
    (c : SpatialCoordinates d) (hc : ∀ i, b i < ℓ i c) (j : ι)
    (x : SpatialCoordinates d) (hj : ℓ j x=b j) (hother : ∀ i, i ≠ j → b i < ℓ i x)
    {l : ℝ} (hl : 0 ≤ l) {q : ℝ → ℝ}
    {L u : (ℝ × SpatialCoordinates d) → ℝ} (hL : ContDiff ℝ ∞ L) (hu : ContDiff ℝ ∞ u)
    (hformula : ∀ s y, L (s,y)=q s*interiorCarlemanProfile c l y)
    (hboundary : ∀ s : ℝ, ∀ y ∈ frontier {z | ∀ i, b i < ℓ i z}, u (s,y)=0)
    (k p : (ℝ × SpatialCoordinates d) → ℝ) (t : ℝ) (hq : 0 ≤ q t) :
    let n := halfspaceOutwardNormal (ℓ j)
    let z := fun y => Real.exp (L y)*u y
    ‖n‖=1 ∧
      (∑ i, pointwiseHeatFlux spaceTimeSpatialDirection (1,0) L k p z i (t,x)*(n i)) ≤ 0 := by
  have hne : ℓ j ≠ 0 := by
    intro he
    have h := hc j
    rw [he,zero_apply] at h hj
    linarith
  obtain ⟨r,hr,hface⟩ := finite_halfspace_face_neighborhood ℓ b c hc j x hj hother
  dsimp only
  refine ⟨halfspaceOutwardNormal_norm hne,?_⟩
  apply gaussian_plane_heat_flux_nonpos
    (S := {y | ∀ i, b i < ℓ i y}) hc hl hL (hL.exp.mul hu) hformula k p t hq x
    (halfspaceOutwardNormal (ℓ j)) (halfspaceOutwardNormal_norm hne)
  · intro y hy
    exact halfspaceOutwardNormal_support hne x hj y (hy j)
  · exact hr
  · intro s y hy hplane
    have hyboundary := hface y hy ((halfspaceOutwardNormal_plane hne (y-x)).mp hplane)
    rw [hboundary s y hyboundary,mul_zero]

theorem finite_halfspace_closed_face_gaussian_heat_flux
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ)
    (c : SpatialCoordinates d) (hc : ∀ i, b i < ℓ i c) (j : ι)
    (w : SpatialCoordinates d) (hw : ℓ j w=b j) (hwi : ∀ i, i ≠ j → b i < ℓ i w)
    (x : SpatialCoordinates d) (hx : ℓ j x=b j) (hxi : ∀ i, b i ≤ ℓ i x)
    {l : ℝ} (hl : 0 ≤ l) {q : ℝ → ℝ}
    {L u k p : (ℝ × SpatialCoordinates d) → ℝ}
    (hL : ContDiff ℝ ∞ L) (hu : ContDiff ℝ ∞ u)
    (hk : ContDiff ℝ ∞ k) (hp : ContDiff ℝ ∞ p)
    (hformula : ∀ s y, L (s,y)=q s*interiorCarlemanProfile c l y)
    (hboundary : ∀ s : ℝ, ∀ y ∈ frontier {z | ∀ i, b i < ℓ i z}, u (s,y)=0)
    (t : ℝ) (hq : 0 ≤ q t) :
    let n := halfspaceOutwardNormal (ℓ j)
    let z := fun y => Real.exp (L y)*u y
    (∑ i, pointwiseHeatFlux spaceTimeSpatialDirection (1,0) L k p z i (t,x)*n i) ≤ 0 := by
  let n := halfspaceOutwardNormal (ℓ j)
  let z := fun y => Real.exp (L y)*u y
  let F : SpatialCoordinates d → ℝ := fun y =>
    ∑ i, pointwiseHeatFlux spaceTimeSpatialDirection (1,0) L k p z i (t,y)*n i
  have hF : Continuous F := by
    apply continuous_finsetSum
    intro i _
    exact (((pointwiseHeatFlux_contDiff _ _ hL hk hp (hL.exp.mul hu) i).continuous.comp
      (continuous_const.prodMk continuous_id)).mul continuous_const)
  have hs : {y | ℓ j y=b j ∧ ∀ i, i ≠ j → b i < ℓ i y} ⊆ {y | F y ≤ 0} := by
    intro y hy
    exact (finite_halfspace_gaussian_heat_flux ℓ b c hc j y hy.1 hy.2 hl hL hu
      hformula hboundary k p t hq).2
  exact closure_minimal hs (isClosed_le hF continuous_const)
    (finite_halfspace_face_mem_closure ℓ b j w hw hwi x hx hxi)

end Carleman
