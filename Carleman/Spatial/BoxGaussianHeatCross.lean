module

public import Carleman.Spatial.BoxIntegratedHeatIdentity
public import Carleman.Spatial.BoxTimeIntegralOrder
public import Carleman.Weights.InteriorHeatBulkLowerBound

/-! The manuscript's heat-cross estimate on smooth periodic boxes. All coefficients,
integrals, boundary signs and the lambda-independent leading constant are proved. -/
@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace Carleman
variable {d : ℕ}

theorem interiorHeatLeadingCoefficient_continuous (c : SpatialCoordinates d) (l : ℝ)
    {q : ℝ → ℝ} (hq : Continuous q) :
    Continuous (fun tx : ℝ × SpatialCoordinates d => interiorHeatLeadingCoefficient c l (q tx.1) tx.2) := by
  simp only [interiorHeatLeadingCoefficient,interiorQuadratic_gradient_norm_sq]
  have hφ := (interiorGaussian_contDiff c l).continuous
  fun_prop

theorem box_smooth_gaussian_heat_cross (a b : Fin (d+1) → ℝ) (hpos : ∀ i, a i < b i)
    (c : SpatialCoordinates (d+1)) (hc : c ∈ openCoordinateBox a b)
    {l : ℝ} (hl : 0 < l) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 ≤ T → ∀ q : ℝ → ℝ, ContDiff ℝ ∞ q →
      Function.Periodic q T → ∀ β : ℝ, 0 ≤ β →
      (∀ t ∈ Icc 0 T, 1 ≤ q t) →
      (∀ t ∈ Icc 0 T, |deriv q t| ≤ β*(q t)^2) →
      (∀ t ∈ Icc 0 T, |deriv (deriv q) t| ≤ β^2*(q t)^3) →
      ∀ u : (ℝ × SpatialCoordinates (d+1)) → ℝ, ContDiff ℝ ∞ u → Function.Periodic u (T,0) →
      (∀ t : ℝ, ∀ x ∈ frontier (openCoordinateBox a b), u (t,x)=0) →
      let L := interiorGaussianHeatPhase c l q
      let z := fun tx => Real.exp (L tx)*u tx
      boxTimeIntegral a b T (fun tx =>
        q tx.1*l*interiorGaussian c l tx.2*directionalEnergy spaceTimeSpatialDirection z tx)+
      boxTimeIntegral a b T (fun tx =>
        (q tx.1)^3*l^3*(interiorGaussian c l tx.2)^3*‖gradient (interiorQuadratic c) tx.2‖^2*
          (l*‖gradient (interiorQuadratic c) tx.2‖^2-6)*(z tx)^2) ≤
      (1/4:ℝ)*boxTimeIntegral a b T (fun tx => (Real.exp (L tx)*spaceTimeHeat u tx)^2)+
        C*boxTimeIntegral a b T (fun tx => ((q tx.1)^2+(β+β^2)*(q tx.1)^3)*(z tx)^2) := by
  obtain ⟨K,hK,hbulk⟩ := interiorGaussianHeat_bulk_lower_bound (openCoordinateBox_isBounded a b) c hl
  refine ⟨K/4,by positivity,?_⟩
  intro T hT q hq hqp β hβ hq1 hq' hq'' u hu hup hub
  dsimp only
  let L := interiorGaussianHeatPhase c l q
  let p := interiorGaussianHeatPsi c l q
  let k := heatConjugationK spaceTimeSpatialDirection (1,0) L p
  let z := fun tx => Real.exp (L tx)*u tx
  let G := fun tx => q tx.1*l*interiorGaussian c l tx.2*directionalEnergy spaceTimeSpatialDirection z tx
  let A := fun tx => (q tx.1)^3*l^3*(interiorGaussian c l tx.2)^3*
    ‖gradient (interiorQuadratic c) tx.2‖^2*(l*‖gradient (interiorQuadratic c) tx.2‖^2-6)*(z tx)^2
  let W := fun tx => ((q tx.1)^2+(β+β^2)*(q tx.1)^3)*(z tx)^2
  let B := heatCarlemanBulk spaceTimeSpatialDirection (1,0) L k p z
  have hL := interiorGaussianHeatPhase_contDiff c l hq
  have hp := interiorGaussianHeatPsi_contDiff c l hq
  have hz : ContDiff ℝ ∞ z := hL.exp.mul hu
  have hk := heatConjugationK_contDiff spaceTimeSpatialDirection (1,0) hL hp
  have hG : Continuous G := by
    have hφ := (interiorGaussian_contDiff c l).continuous
    have he := (directionalEnergy_contDiff spaceTimeSpatialDirection hz).continuous
    have hqc := hq.continuous
    fun_prop
  have hA : Continuous A := by
    have hφ := (interiorGaussian_contDiff c l).continuous
    have hqc := hq.continuous
    have hzc := hz.continuous
    dsimp only [A]
    simp only [interiorQuadratic_gradient_norm_sq]
    fun_prop
  have hW : Continuous W := by
    have hqc := hq.continuous
    have hzc := hz.continuous
    fun_prop
  have hB : Continuous B := (heatCarlemanBulk_contDiff _ _ hL hk hp hz).continuous
  have hKW : Continuous (fun tx => K*W tx) := continuous_const.mul hW
  have hi : boxTimeIntegral a b T (fun tx => 4*(G tx+A tx)) ≤
      boxTimeIntegral a b T (fun tx => B tx+K*W tx) := by
    apply boxTimeIntegral_mono_on a b T (f := fun tx => 4*(G tx+A tx))
      (g := fun tx => B tx+K*W tx) (continuous_const.mul (hG.add hA)) (hB.add hKW)
    intro t ht x hx
    have hh := hbulk q hq β hβ z t (hq1 t ht) (hq' t ht) (hq'' t ht) x hx
    dsimp only [G,A,B,W,L,k,p,interiorHeatLeadingCoefficient] at hh ⊢
    nlinarith [hh]
  rw [boxTimeIntegral_const_mul,boxTimeIntegral_add a b T hG hA,
    boxTimeIntegral_add a b T hB hKW,boxTimeIntegral_const_mul] at hi
  have hint := box_smooth_heat_carleman_inequality a b hpos c hc hT hl.le hL hp hu
    (interiorGaussianHeatPhase_periodic c l hqp) (interiorGaussianHeatPsi_periodic c l hqp) hup
    (fun _ _ => rfl) hub (fun t ht => le_trans (by norm_num) (hq1 t ht))
  change boxTimeIntegral a b T G+boxTimeIntegral a b T A ≤ _
  change boxTimeIntegral a b T B ≤ _ at hint
  nlinarith

end Carleman
