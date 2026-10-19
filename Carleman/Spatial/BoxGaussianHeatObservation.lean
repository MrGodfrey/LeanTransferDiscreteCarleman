module

public import Carleman.Spatial.BoxGaussianHeatCross
public import Carleman.Spatial.BoxObservationIntegral
public import Carleman.Weights.InteriorHeatAbsorption

/-! Actual observation absorption on smooth periodic boxes, with all geometric and
temporal parameters chosen before the period, weight, and state. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Carleman
variable {d : ℕ}

theorem box_smooth_gaussian_heat_observation (a b : Fin (d+1) → ℝ) (hpos : ∀ i, a i < b i)
    {W : Set (SpatialCoordinates (d+1))} (hW : IsOpen W) (hne : W.Nonempty)
    (hWS : W ⊆ openCoordinateBox a b) :
    ∃ (c : SpatialCoordinates (d+1)) (l β qc A₁ A₀ K : ℝ), c ∈ W ∧ 1 ≤ l ∧
      0 < β ∧ β ≤ 1 ∧ 1 ≤ qc ∧ 0 < A₁ ∧ 0 < A₀ ∧ 0 < K ∧
      ∀ T : ℝ, 0 ≤ T → ∀ q : ℝ → ℝ, ContDiff ℝ ∞ q → Function.Periodic q T →
      (∀ t ∈ Icc 0 T, qc ≤ q t) →
      (∀ t ∈ Icc 0 T, |deriv q t| ≤ β*(q t)^2) →
      (∀ t ∈ Icc 0 T, |deriv (deriv q) t| ≤ β^2*(q t)^3) →
      ∀ u : (ℝ × SpatialCoordinates (d+1)) → ℝ, ContDiff ℝ ∞ u → Function.Periodic u (T,0) →
      (∀ t : ℝ, ∀ x ∈ frontier (openCoordinateBox a b), u (t,x)=0) →
      let L := interiorGaussianHeatPhase c l q
      let z := fun tx => Real.exp (L tx)*u tx
      A₁*boxTimeIntegral a b T (fun tx => q tx.1*directionalEnergy spaceTimeSpatialDirection z tx)+
      A₀*boxTimeIntegral a b T (fun tx => (q tx.1)^3*(z tx)^2) ≤
      (1/4:ℝ)*boxTimeIntegral a b T (fun tx => (Real.exp (L tx)*spaceTimeHeat u tx)^2)+
        K*boxTimeIntegral a b T ((Prod.snd ⁻¹' W).indicator (fun tx => (q tx.1)^3*(z tx)^2)) := by
  classical
  obtain ⟨c,l,A₁,m,K,hc,hl,hA₁,hm,hK,hspace⟩ :=
    exists_interior_heat_observation_coefficients (openCoordinateBox_isBounded a b) hW hne hWS
  have hl0 : 0 < l := lt_of_lt_of_le (by norm_num) hl
  obtain ⟨C,hC,hcross⟩ := box_smooth_gaussian_heat_cross a b hpos c (hWS hc) hl0
  obtain ⟨β,qc,hβ,hβ1,hqc,hsmall⟩ := exists_heat_absorption_parameters hm hC
  refine ⟨c,l,β,qc,A₁,m/2,K,hc,hl,hβ,hβ1,hqc,hA₁,by positivity,hK,?_⟩
  intro T hT q hq hqp hqmin hq' hq'' u hu hup hub
  dsimp only
  let L := interiorGaussianHeatPhase c l q
  let z := fun tx => Real.exp (L tx)*u tx
  let E := fun tx => q tx.1*directionalEnergy spaceTimeSpatialDirection z tx
  let V := fun tx => (q tx.1)^3*(z tx)^2
  let R := fun tx => ((q tx.1)^2+(β+β^2)*(q tx.1)^3)*(z tx)^2
  let G := fun tx => q tx.1*l*interiorGaussian c l tx.2*directionalEnergy spaceTimeSpatialDirection z tx
  let F := fun tx => (q tx.1)^3*l^3*(interiorGaussian c l tx.2)^3*
    ‖gradient (interiorQuadratic c) tx.2‖^2*(l*‖gradient (interiorQuadratic c) tx.2‖^2-6)*(z tx)^2
  let O := (Prod.snd ⁻¹' W).indicator V
  have hL := interiorGaussianHeatPhase_contDiff c l hq
  have hz : ContDiff ℝ ∞ z := hL.exp.mul hu
  have hzc := hz.continuous
  have hqc' := hq.continuous
  have henergy := (directionalEnergy_contDiff spaceTimeSpatialDirection hz).continuous
  have hφ := (interiorGaussian_contDiff c l).continuous
  have hE : Continuous E := by fun_prop
  have hV : Continuous V := by fun_prop
  have hR : Continuous R := by fun_prop
  have hG : Continuous G := by fun_prop
  have hF : Continuous F := by
    dsimp only [F]
    simp only [interiorQuadratic_gradient_norm_sq]
    fun_prop
  have hO : Integrable O ((volume.restrict (Icc 0 T)).prod (volume.restrict (openCoordinateBox a b))) :=
    continuous_box_observation_integrable a b T hW.measurableSet hV
  have hAE : Continuous (fun tx => A₁*E tx) := continuous_const.mul hE
  have hMV : Continuous (fun tx => (m/2)*V tx) := continuous_const.mul hV
  have hCR : Continuous (fun tx => C*R tx) := continuous_const.mul hR
  have hAM : Continuous (fun tx => A₁*E tx+(m/2)*V tx) := hAE.add hMV
  have hGF : Continuous (fun tx => G tx+F tx) := hG.add hF
  have hKO : Integrable (fun tx => K*O tx)
      ((volume.restrict (Icc 0 T)).prod (volume.restrict (openCoordinateBox a b))) := hO.const_mul K
  have hi : boxTimeIntegral a b T (fun tx => A₁*E tx+(m/2)*V tx+C*R tx) ≤
      boxTimeIntegral a b T (fun tx => G tx+F tx+K*O tx) := by
    apply boxTimeIntegral_mono_on_integrable a b T
      (f := fun tx => A₁*E tx+(m/2)*V tx+C*R tx)
      (g := fun tx => G tx+F tx+K*O tx)
      (continuous_box_time_integrable a b T ((hAE.add hMV).add hCR))
      ((continuous_box_time_integrable a b T (hG.add hF)).add hKO)
    intro t ht x hx
    have hq0 : 0 ≤ q t := le_trans (by linarith) (hqmin t ht)
    have hh := interiorHeat_observation_absorption c l W x hq0
      (directionalEnergy_nonneg spaceTimeSpatialDirection z (t,x))
      (hspace x hx).1 (hspace x hx).2 (hsmall (q t) (hqmin t ht)) (Z := z (t,x))
    have hoe : O (t,x)=W.indicator (fun _ => (q t)^3*(z (t,x))^2) x := by
      by_cases hxW : x ∈ W <;> simp [O,V,indicator,hxW]
    dsimp only [E,V,R,G,F]
    rw [hoe]
    dsimp only [interiorHeatPotential] at hh
    nlinarith [hh]
  rw [boxTimeIntegral_add a b T hAM hCR,boxTimeIntegral_add a b T hAE hMV,
    boxTimeIntegral_const_mul,boxTimeIntegral_const_mul,boxTimeIntegral_const_mul,
    boxTimeIntegral_add_integrable a b T (continuous_box_time_integrable a b T hGF) hKO,
    boxTimeIntegral_add a b T hG hF,boxTimeIntegral_const_mul] at hi
  have hcros := hcross T hT q hq hqp β hβ.le (fun t ht => hqc.trans (hqmin t ht)) hq' hq'' u hu hup hub
  change boxTimeIntegral a b T G+boxTimeIntegral a b T F ≤ _ at hcros
  change A₁*boxTimeIntegral a b T E+(m/2)*boxTimeIntegral a b T V ≤ _
  nlinarith

end Carleman
