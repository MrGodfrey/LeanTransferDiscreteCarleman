module

public import Carleman.Spatial.SmoothBoxTimeIntegral
public import Carleman.Spatial.HeatIdentityRegularity
public import Carleman.Spatial.BoxHeatFluxIntegral

/-! The genuine integrated heat Carleman inequality for smooth periodic box states.
Time flux cancels by Fubini and periodicity; spatial flux is removed using its proved sign. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff BigOperators
namespace Carleman
variable {d : ℕ}

theorem spaceTimeHeat_contDiff {u : (ℝ × SpatialCoordinates d) → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (spaceTimeHeat u) := by
  have he : spaceTimeHeat u=(fun y => smoothD (1,0) u y-directionalLap spaceTimeSpatialDirection u y) :=
    funext fun y => (spaceTime_heat_directional hu y).symm
  rw [he]
  exact (smoothD_contDiff hu _).sub (directionalLap_contDiff _ hu)

theorem box_smooth_heat_carleman_inequality (a b : Fin (d+1) → ℝ) (hpos : ∀ i, a i < b i)
    (c : SpatialCoordinates (d+1)) (hc : c ∈ openCoordinateBox a b)
    {T l : ℝ} (hT : 0 ≤ T) (hl : 0 ≤ l) {q : ℝ → ℝ}
    {L p u : (ℝ × SpatialCoordinates (d+1)) → ℝ}
    (hL : ContDiff ℝ ∞ L) (hp : ContDiff ℝ ∞ p) (hu : ContDiff ℝ ∞ u)
    (hpl : Function.Periodic L (T,0)) (hpp : Function.Periodic p (T,0))
    (hpu : Function.Periodic u (T,0))
    (hformula : ∀ s y, L (s,y)=q s*interiorCarlemanProfile c l y)
    (hboundary : ∀ s : ℝ, ∀ y ∈ frontier (openCoordinateBox a b), u (s,y)=0)
    (hq : ∀ t ∈ Icc 0 T, 0 ≤ q t) :
    let e := spaceTimeSpatialDirection (d := d+1)
    let z := fun y => Real.exp (L y)*u y
    let k := heatConjugationK e (1,0) L p
    boxTimeIntegral a b T (heatCarlemanBulk e (1,0) L k p z) ≤
      boxTimeIntegral a b T (fun y => (Real.exp (L y)*spaceTimeHeat u y)^2) := by
  let e := spaceTimeSpatialDirection (d := d+1)
  let z := fun y => Real.exp (L y)*u y
  let k := heatConjugationK e (1,0) L p
  let R := fun y => (Real.exp (L y)*spaceTimeHeat u y)^2
  let M := smoothD (1,0) (pointwiseHeatTimeFlux e k z)
  let V := fun x => ∑ i, smoothD (e i) (pointwiseHeatFlux e (1,0) L k p z i) x
  have hz : ContDiff ℝ ∞ z := hL.exp.mul hu
  have hk : ContDiff ℝ ∞ k := heatConjugationK_contDiff e (1,0) hL hp
  have hR : ContDiff ℝ ∞ R := (hL.exp.mul (spaceTimeHeat_contDiff hu)).pow 2
  have hM : ContDiff ℝ ∞ M :=
    smoothD_contDiff (pointwiseHeatTimeFlux_contDiff e hk hz) (1,0)
  have hV : ContDiff ℝ ∞ V := pointwiseHeatDivergence_contDiff e (1,0) hL hk hp hz
  have hzero : boxTimeIntegral a b T M=0 := by
    apply boxTimeIntegral_periodic_derivative a b hT (pointwiseHeatTimeFlux_contDiff e hk hz)
    exact pointwiseHeatTimeFlux_periodic e (heatConjugationK_periodic e (1,0) hpl hpp)
      ((hpl.comp Real.exp).mul hpu)
  have hnonpos : boxTimeIntegral a b T V ≤ 0 := by
    apply boxTimeIntegral_nonpos_of_spatial a b T hV.continuous
    intro t ht
    exact box_gaussian_heat_flux_integral a b hpos c hc hl hL hu hk hp hformula hboundary t (hq t ht)
  have hi : boxTimeIntegral a b T (heatCarlemanBulk e (1,0) L k p z) ≤
      boxTimeIntegral a b T (fun y => R y+M y+V y) :=
    boxTimeIntegral_mono a b T (heatCarlemanBulk_contDiff e (1,0) hL hk hp hz).continuous
      ((hR.add hM).add hV).continuous (fun y => spacetime_heat_carleman_inequality hL hp hu y)
  rw [boxTimeIntegral_add a b T (hR.add hM).continuous hV.continuous,
    boxTimeIntegral_add a b T hR.continuous hM.continuous,hzero,add_zero] at hi
  exact hi.trans (add_le_of_nonpos_right hnonpos)

end Carleman
