module

public import Carleman.Spatial.BoxHeatBoundary
public import Carleman.Spatial.SmoothBoxDivergence

/-! Nonpositive integral of the actual smooth heat flux divergence on a box. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff BigOperators
namespace Carleman
variable {d : ℕ}

theorem coordinateFacePoint_mem_closed (a b : Fin (d+1) → ℝ) (hab : ∀ j, a j ≤ b j)
    (i : Fin (d+1)) (upper : Bool) (y : Fin d → ℝ)
    (hy : y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :
    (WithLp.toLp 2 (i.insertNth (if upper then b i else a i) y) : SpatialCoordinates (d+1)) ∈
      closedCoordinateBox a b := by
  intro j
  induction j using Fin.succAboveCases i with
  | x => cases upper <;> simp [hab i]
  | p j => simpa only [Fin.insertNth_apply_succAbove,Function.comp_apply] using ⟨hy.1 j,hy.2 j⟩

theorem box_gaussian_heat_flux_integral (a b : Fin (d+1) → ℝ) (hpos : ∀ i, a i < b i)
    (c : SpatialCoordinates (d+1)) (hc : c ∈ openCoordinateBox a b)
    {l : ℝ} (hl : 0 ≤ l) {q : ℝ → ℝ}
    {L u k p : (ℝ × SpatialCoordinates (d+1)) → ℝ}
    (hL : ContDiff ℝ ∞ L) (hu : ContDiff ℝ ∞ u)
    (hk : ContDiff ℝ ∞ k) (hp : ContDiff ℝ ∞ p)
    (hformula : ∀ s y, L (s,y)=q s*interiorCarlemanProfile c l y)
    (hboundary : ∀ s : ℝ, ∀ y ∈ frontier (openCoordinateBox a b), u (s,y)=0)
    (t : ℝ) (hq : 0 ≤ q t) :
    let z := fun y => Real.exp (L y)*u y
    (∫ x in openCoordinateBox a b,
      ∑ i, smoothD (spaceTimeSpatialDirection i)
        (pointwiseHeatFlux spaceTimeSpatialDirection (1,0) L k p z i) (t,x)) ≤ 0 := by
  let z := fun y => Real.exp (L y)*u y
  let V := pointwiseHeatFlux spaceTimeSpatialDirection (1,0) L k p z
  let F : Fin (d+1) → SpatialCoordinates (d+1) → ℝ := fun i y => V i (t,y)
  have hV i : ContDiff ℝ ∞ (V i) := pointwiseHeatFlux_contDiff _ _ hL hk hp (hL.exp.mul hu) i
  have hF i : ContDiff ℝ ∞ (F i) := (hV i).comp (contDiff_const.prodMk contDiff_id)
  have he x : (∑ i, smoothD (spaceTimeSpatialDirection i) (V i) (t,x))=
      coordinateDivergence F x := by
    apply Finset.sum_congr rfl
    intro i _
    exact spaceTime_spatialD (hV i) t x _
  change (∫ x in openCoordinateBox a b, ∑ i, smoothD (spaceTimeSpatialDirection i) (V i) (t,x)) ≤ 0
  simp_rw [he]
  rw [smooth_open_box_divergence a b (fun i => (hpos i).le) hF]
  apply Finset.sum_nonpos
  intro i _
  have hupp : (∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      F i (WithLp.toLp 2 (i.insertNth (b i) y))) ≤ 0 := by
    apply setIntegral_nonpos measurableSet_Icc
    intro y hy
    exact box_face_gaussian_heat_flux a b hpos c hc i true _
      (coordinateFacePoint_mem_closed a b (fun j => (hpos j).le) i true y hy)
      (by simp) hl hL hu hk hp hformula hboundary t hq
  have hlow : 0 ≤ (∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      F i (WithLp.toLp 2 (i.insertNth (a i) y))) := by
    apply setIntegral_nonneg measurableSet_Icc
    intro y hy
    have h := box_face_gaussian_heat_flux a b hpos c hc i false _
      (coordinateFacePoint_mem_closed a b (fun j => (hpos j).le) i false y hy)
      (by simp) hl hL hu hk hp hformula hboundary t hq
    exact neg_nonpos.mp h
  exact sub_nonpos.mpr (hupp.trans hlow)

end Carleman
