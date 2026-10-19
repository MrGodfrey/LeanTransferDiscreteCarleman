module

public import Carleman.Spatial.BoxGaussianHeatObservation
public import Carleman.Weights.InteriorHeatGradientReturn

/-! A complete smooth periodic box estimate for the original state u and its actual
spatial gradient. This does not yet assert the paper's C²-weight / weak-state extension. -/
@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace Carleman
variable {d : ℕ}

theorem box_smooth_gaussian_heat_estimate (a b : Fin (d+1) → ℝ) (hpos : ∀ i, a i < b i)
    {W : Set (SpatialCoordinates (d+1))} (hW : IsOpen W) (hne : W.Nonempty)
    (hWS : W ⊆ openCoordinateBox a b) :
    ∃ (c : SpatialCoordinates (d+1)) (l β qc C : ℝ), c ∈ W ∧ 1 ≤ l ∧
      0 < β ∧ β ≤ 1 ∧ 1 ≤ qc ∧ 0 < C ∧
      (∀ x, -2 < interiorCarlemanProfile c l x ∧ interiorCarlemanProfile c l x ≤ -1) ∧
      ∀ T : ℝ, 0 ≤ T → ∀ q : ℝ → ℝ, ContDiff ℝ ∞ q → Function.Periodic q T →
      (∀ t ∈ Icc 0 T, qc ≤ q t) →
      (∀ t ∈ Icc 0 T, |deriv q t| ≤ β*(q t)^2) →
      (∀ t ∈ Icc 0 T, |deriv (deriv q) t| ≤ β^2*(q t)^3) →
      ∀ u : (ℝ × SpatialCoordinates (d+1)) → ℝ, ContDiff ℝ ∞ u → Function.Periodic u (T,0) →
      (∀ t : ℝ, ∀ x ∈ frontier (openCoordinateBox a b), u (t,x)=0) →
      let L := interiorGaussianHeatPhase c l q
      boxTimeIntegral a b T (fun tx => (q tx.1)^3*(Real.exp (L tx))^2*(u tx)^2)+
      boxTimeIntegral a b T (fun tx =>
        q tx.1*(Real.exp (L tx))^2*‖gradient (fun y => u (tx.1,y)) tx.2‖^2) ≤
      C*(boxTimeIntegral a b T (fun tx => (Real.exp (L tx)*spaceTimeHeat u tx)^2)+
        boxTimeIntegral a b T ((Prod.snd ⁻¹' W).indicator
          (fun tx => (q tx.1)^3*(Real.exp (L tx))^2*(u tx)^2))) := by
  classical
  obtain ⟨c,l,β,qc,A₁,A₀,K,hc,hl,hβ,hβ1,hqc,hA₁,hA₀,hK,hobs⟩ :=
    box_smooth_gaussian_heat_observation a b hpos hW hne hWS
  obtain ⟨H,hH,hreturn⟩ := interiorGaussianHeat_return_bound (openCoordinateBox_isBounded a b) c l
  let D := 1/A₁+1/A₀
  have hD : 0 < D := by dsimp only [D]; positivity
  have hD₁ : 1 ≤ D*A₁ := by
    dsimp only [D]
    field_simp
    nlinarith
  have hD₀ : 1 ≤ D*A₀ := by
    dsimp only [D]
    field_simp
    nlinarith
  refine ⟨c,l,β,qc,H*D*(1+K),hc,hl,hβ,hβ1,hqc,by positivity,
    interiorCarlemanProfile_bounds c (by linarith),?_⟩
  intro T hT q hq hqp hqmin hq' hq'' u hu hup hub
  dsimp only
  simp_rw [← spaceTime_directionalEnergy_gradient hu]
  let L := interiorGaussianHeatPhase c l q
  let z := fun tx => Real.exp (L tx)*u tx
  let E := fun tx => q tx.1*directionalEnergy spaceTimeSpatialDirection z tx
  let V := fun tx => (q tx.1)^3*(z tx)^2
  let R := fun tx => (Real.exp (L tx)*spaceTimeHeat u tx)^2
  let O := (Prod.snd ⁻¹' W).indicator V
  let U₀ := fun tx => (q tx.1)^3*(Real.exp (L tx))^2*(u tx)^2
  let U₁ := fun tx => q tx.1*(Real.exp (L tx))^2*directionalEnergy spaceTimeSpatialDirection u tx
  have hL := interiorGaussianHeatPhase_contDiff c l hq
  have hz : ContDiff ℝ ∞ z := hL.exp.mul hu
  have hqc' := hq.continuous
  have hzc := hz.continuous
  have hLc := hL.continuous
  have huc := hu.continuous
  have hzu := (directionalEnergy_contDiff spaceTimeSpatialDirection hz).continuous
  have huu := (directionalEnergy_contDiff spaceTimeSpatialDirection hu).continuous
  have hE : Continuous E := by fun_prop
  have hV : Continuous V := by fun_prop
  have hU₀ : Continuous U₀ := by fun_prop
  have hU₁ : Continuous U₁ := by fun_prop
  have hq0 : ∀ t ∈ Icc 0 T, 0 ≤ q t := fun t ht => (by linarith : (0:ℝ) ≤ qc).trans (hqmin t ht)
  have hEn : 0 ≤ boxTimeIntegral a b T E := by
    apply boxTimeIntegral_nonneg_on a b T
    intro t ht x _
    exact mul_nonneg (hq0 t ht) (directionalEnergy_nonneg _ _ _)
  have hVn : 0 ≤ boxTimeIntegral a b T V := by
    apply boxTimeIntegral_nonneg_on a b T
    intro t ht x _
    dsimp only [V]
    positivity [hq0 t ht]
  have hRn : 0 ≤ boxTimeIntegral a b T R := by
    exact boxTimeIntegral_nonneg_on a b T (fun _ _ _ _ => sq_nonneg _)
  have hOn : 0 ≤ boxTimeIntegral a b T O := by
    apply boxTimeIntegral_nonneg_on a b T
    intro t ht x _
    by_cases hx : x ∈ W
    · simp only [O,indicator_of_mem (show (t,x) ∈ Prod.snd ⁻¹' W from hx),V]
      positivity [hq0 t ht]
    · simp only [O,indicator_of_notMem (show (t,x) ∉ Prod.snd ⁻¹' W from hx),le_refl]
  have hint : boxTimeIntegral a b T (fun tx => U₀ tx+U₁ tx) ≤
      boxTimeIntegral a b T (fun tx => H*(E tx+V tx)) := by
    apply boxTimeIntegral_mono_on a b T (f := fun tx => U₀ tx+U₁ tx)
      (g := fun tx => H*(E tx+V tx)) (hU₀.add hU₁) (continuous_const.mul (hE.add hV))
    intro t ht x hx
    exact hreturn q hq u hu t (hq0 t ht) x hx
  rw [boxTimeIntegral_add a b T hU₀ hU₁,boxTimeIntegral_const_mul,
    boxTimeIntegral_add a b T hE hV] at hint
  have ho := hobs T hT q hq hqp hqmin hq' hq'' u hu hup hub
  change A₁*boxTimeIntegral a b T E+A₀*boxTimeIntegral a b T V ≤
    (1/4:ℝ)*boxTimeIntegral a b T R+K*boxTimeIntegral a b T O at ho
  have hnormal : boxTimeIntegral a b T E+boxTimeIntegral a b T V ≤
      D*(A₁*boxTimeIntegral a b T E+A₀*boxTimeIntegral a b T V) := by
    nlinarith [mul_le_mul_of_nonneg_right hD₁ hEn,mul_le_mul_of_nonneg_right hD₀ hVn]
  have hbound := mul_le_mul_of_nonneg_left ho (show 0 ≤ H*D by positivity)
  have hnormH := mul_le_mul_of_nonneg_left hnormal hH.le
  have hsurplus : 0 ≤ H*D*((K+3/4)*boxTimeIntegral a b T R+boxTimeIntegral a b T O) := by positivity
  have hVU : V=U₀ := by
    funext tx
    dsimp only [V,U₀,z]
    ring
  change boxTimeIntegral a b T U₀+boxTimeIntegral a b T U₁ ≤
    H*D*(1+K)*(boxTimeIntegral a b T R+boxTimeIntegral a b T ((Prod.snd ⁻¹' W).indicator U₀))
  rw [← hVU]
  change boxTimeIntegral a b T V+boxTimeIntegral a b T U₁ ≤
    H*D*(1+K)*(boxTimeIntegral a b T R+boxTimeIntegral a b T O)
  rw [← hVU] at hint
  nlinarith

end Carleman
