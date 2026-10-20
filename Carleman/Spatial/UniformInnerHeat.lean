module
public import Carleman.Spatial.DomainTimeIntegralTools
public import Carleman.Spatial.BoxSmoothHeatBothSigns
/-! Actual inner-domain estimates with constants chosen on the fixed outer domain. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace Carleman
variable {d : ℕ}

theorem halfspaceSmoothInner_uniform_heat_cross {ι : Type*} [Fintype ι]
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ)
    (hbounded : Bornology.IsBounded {x | ∀ i, b i<ℓ i x})
    (c : SpatialCoordinates d)
    {l : ℝ} (hl : 0 < l) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, c ∈ halfspaceSmoothInner ℓ b n → ∀ T : ℝ, 0 ≤ T → ∀ q : ℝ → ℝ, ContDiff ℝ ∞ q →
      Function.Periodic q T → ∀ β : ℝ, 0 ≤ β →
      (∀ t ∈ Icc 0 T, 1 ≤ q t) →
      (∀ t ∈ Icc 0 T, |deriv q t| ≤ β*(q t)^2) →
      (∀ t ∈ Icc 0 T, |deriv (deriv q) t| ≤ β^2*(q t)^3) →
      ∀ u : (ℝ × SpatialCoordinates d) → ℝ, ContDiff ℝ ∞ u → Function.Periodic u (T,0) →
      (∀ t : ℝ, ∀ x ∈ frontier (halfspaceSmoothInner ℓ b n), u (t,x)=0) →
      let L := interiorGaussianHeatPhase c l q
      let z := fun tx => Real.exp (L tx)*u tx
      domainTimeIntegral (halfspaceSmoothInner ℓ b n) T (fun tx =>
        q tx.1*l*interiorGaussian c l tx.2*directionalEnergy spaceTimeSpatialDirection z tx)+
      domainTimeIntegral (halfspaceSmoothInner ℓ b n) T (fun tx =>
        (q tx.1)^3*l^3*(interiorGaussian c l tx.2)^3*‖gradient (interiorQuadratic c) tx.2‖^2*
          (l*‖gradient (interiorQuadratic c) tx.2‖^2-6)*(z tx)^2) ≤
      (1/4:ℝ)*domainTimeIntegral (halfspaceSmoothInner ℓ b n) T (fun tx => (Real.exp (L tx)*spaceTimeHeat u tx)^2)+
        C*domainTimeIntegral (halfspaceSmoothInner ℓ b n) T (fun tx => ((q tx.1)^2+(β+β^2)*(q tx.1)^3)*(z tx)^2) := by
  obtain ⟨K,hK,hbulk⟩ := interiorGaussianHeat_bulk_lower_bound hbounded c hl
  refine ⟨K/4,by positivity,?_⟩
  intro n hc T hT q hq hqp β hβ hq1 hq' hq'' u hu hup hub
  have hb := (halfspaceSmoothInner_compact ℓ b hbounded n).isBounded.subset subset_closure
  have hS := (halfspaceSmoothInner_open ℓ b n).measurableSet
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
  have hi : domainTimeIntegral (halfspaceSmoothInner ℓ b n) T (fun tx => 4*(G tx+A tx)) ≤
      domainTimeIntegral (halfspaceSmoothInner ℓ b n) T (fun tx => B tx+K*W tx) := by
    apply domainTimeIntegral_mono_on _ hS hb T (f := fun tx => 4*(G tx+A tx))
      (g := fun tx => B tx+K*W tx) (continuous_const.mul (hG.add hA)) (hB.add hKW)
    intro t ht x hx
    have hh := hbulk q hq β hβ z t (hq1 t ht) (hq' t ht) (hq'' t ht) x (halfspaceExpSum_le_half_mem ℓ b n (show halfspaceExpSum ℓ b n x≤1/2 from hx.le))
    dsimp only [G,A,B,W,L,k,p,interiorHeatLeadingCoefficient] at hh ⊢
    nlinarith [hh]
  rw [domainTimeIntegral_const_mul,domainTimeIntegral_add _ hb T hG hA,
    domainTimeIntegral_add _ hb T hB hKW,domainTimeIntegral_const_mul] at hi
  have hint := halfspaceSmoothInner_smooth_heat_carleman_inequality ℓ b hbounded n c hc hT hl.le hL hp hu
    (interiorGaussianHeatPhase_periodic c l hqp) (interiorGaussianHeatPsi_periodic c l hqp) hup
    (fun _ _ => rfl) hub (fun t ht => le_trans (by norm_num) (hq1 t ht))
  change domainTimeIntegral (halfspaceSmoothInner ℓ b n) T G+domainTimeIntegral (halfspaceSmoothInner ℓ b n) T A ≤ _
  change domainTimeIntegral (halfspaceSmoothInner ℓ b n) T B ≤ _ at hint
  nlinarith

theorem halfspaceSmoothInner_uniform_heat_observation {ι : Type*} [Fintype ι]
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ)
    (hbounded : Bornology.IsBounded {x | ∀ i, b i<ℓ i x})
    {W : Set (SpatialCoordinates d)} (hW : IsOpen W) (hne : W.Nonempty)
    (hWS : W ⊆ {x | ∀ i, b i<ℓ i x}) :
    ∃ (c : SpatialCoordinates d) (l β qc A₁ A₀ K : ℝ), c ∈ W ∧ 1 ≤ l ∧
      0 < β ∧ β ≤ 1 ∧ 1 ≤ qc ∧ 0 < A₁ ∧ 0 < A₀ ∧ 0 < K ∧
      ∀ n : ℕ, c ∈ halfspaceSmoothInner ℓ b n → ∀ T : ℝ, 0 ≤ T → ∀ q : ℝ → ℝ, ContDiff ℝ ∞ q → Function.Periodic q T →
      (∀ t ∈ Icc 0 T, qc ≤ q t) →
      (∀ t ∈ Icc 0 T, |deriv q t| ≤ β*(q t)^2) →
      (∀ t ∈ Icc 0 T, |deriv (deriv q) t| ≤ β^2*(q t)^3) →
      ∀ u : (ℝ × SpatialCoordinates d) → ℝ, ContDiff ℝ ∞ u → Function.Periodic u (T,0) →
      (∀ t : ℝ, ∀ x ∈ frontier (halfspaceSmoothInner ℓ b n), u (t,x)=0) →
      let L := interiorGaussianHeatPhase c l q
      let z := fun tx => Real.exp (L tx)*u tx
      A₁*domainTimeIntegral (halfspaceSmoothInner ℓ b n) T (fun tx => q tx.1*directionalEnergy spaceTimeSpatialDirection z tx)+
      A₀*domainTimeIntegral (halfspaceSmoothInner ℓ b n) T (fun tx => (q tx.1)^3*(z tx)^2) ≤
      (1/4:ℝ)*domainTimeIntegral (halfspaceSmoothInner ℓ b n) T (fun tx => (Real.exp (L tx)*spaceTimeHeat u tx)^2)+
        K*domainTimeIntegral (halfspaceSmoothInner ℓ b n) T ((Prod.snd ⁻¹' W).indicator (fun tx => (q tx.1)^3*(z tx)^2)) := by
  classical
  obtain ⟨c,l,A₁,m,K,hc,hl,hA₁,hm,hK,hspace⟩ :=
    exists_interior_heat_observation_coefficients hbounded hW hne hWS
  have hl0 : 0 < l := lt_of_lt_of_le (by norm_num) hl
  obtain ⟨C,hC,hcross⟩ := halfspaceSmoothInner_uniform_heat_cross ℓ b hbounded c hl0
  obtain ⟨β,qc,hβ,hβ1,hqc,hsmall⟩ := exists_heat_absorption_parameters hm hC
  refine ⟨c,l,β,qc,A₁,m/2,K,hc,hl,hβ,hβ1,hqc,hA₁,by positivity,hK,?_⟩
  intro n hcn T hT q hq hqp hqmin hq' hq'' u hu hup hub
  have hb := (halfspaceSmoothInner_compact ℓ b hbounded n).isBounded.subset subset_closure
  have hS := (halfspaceSmoothInner_open ℓ b n).measurableSet
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
  have hO : Integrable O ((volume.restrict (Icc 0 T)).prod (volume.restrict (halfspaceSmoothInner ℓ b n))) :=
    continuous_domain_observation_integrable _ hb T hW.measurableSet hV
  have hAE : Continuous (fun tx => A₁*E tx) := continuous_const.mul hE
  have hMV : Continuous (fun tx => (m/2)*V tx) := continuous_const.mul hV
  have hCR : Continuous (fun tx => C*R tx) := continuous_const.mul hR
  have hAM : Continuous (fun tx => A₁*E tx+(m/2)*V tx) := hAE.add hMV
  have hGF : Continuous (fun tx => G tx+F tx) := hG.add hF
  have hKO : Integrable (fun tx => K*O tx)
      ((volume.restrict (Icc 0 T)).prod (volume.restrict (halfspaceSmoothInner ℓ b n))) := hO.const_mul K
  have hi : domainTimeIntegral (halfspaceSmoothInner ℓ b n) T (fun tx => A₁*E tx+(m/2)*V tx+C*R tx) ≤
      domainTimeIntegral (halfspaceSmoothInner ℓ b n) T (fun tx => G tx+F tx+K*O tx) := by
    apply domainTimeIntegral_mono_on_integrable _ hS T
      (f := fun tx => A₁*E tx+(m/2)*V tx+C*R tx)
      (g := fun tx => G tx+F tx+K*O tx)
      (continuous_domain_time_integrable _ hb T ((hAE.add hMV).add hCR))
      ((continuous_domain_time_integrable _ hb T (hG.add hF)).add hKO)
    intro t ht x hx
    have hq0 : 0 ≤ q t := le_trans (by linarith) (hqmin t ht)
    have hh := interiorHeat_observation_absorption c l W x hq0
      (directionalEnergy_nonneg spaceTimeSpatialDirection z (t,x))
      (hspace x (halfspaceExpSum_le_half_mem ℓ b n (show halfspaceExpSum ℓ b n x≤1/2 from hx.le))).1 (hspace x (halfspaceExpSum_le_half_mem ℓ b n (show halfspaceExpSum ℓ b n x≤1/2 from hx.le))).2 (hsmall (q t) (hqmin t ht)) (Z := z (t,x))
    have hoe : O (t,x)=W.indicator (fun _ => (q t)^3*(z (t,x))^2) x := by
      by_cases hxW : x ∈ W <;> simp [O,V,indicator,hxW]
    dsimp only [E,V,R,G,F]
    rw [hoe]
    dsimp only [interiorHeatPotential] at hh
    nlinarith [hh]
  rw [domainTimeIntegral_add _ hb T hAM hCR,domainTimeIntegral_add _ hb T hAE hMV,
    domainTimeIntegral_const_mul,domainTimeIntegral_const_mul,domainTimeIntegral_const_mul,
    domainTimeIntegral_add_integrable _ T (continuous_domain_time_integrable _ hb T hGF) hKO,
    domainTimeIntegral_add _ hb T hG hF,domainTimeIntegral_const_mul] at hi
  have hcros := hcross n hcn T hT q hq hqp β hβ.le (fun t ht => hqc.trans (hqmin t ht)) hq' hq'' u hu hup hub
  change domainTimeIntegral (halfspaceSmoothInner ℓ b n) T G+domainTimeIntegral (halfspaceSmoothInner ℓ b n) T F ≤ _ at hcros
  change A₁*domainTimeIntegral (halfspaceSmoothInner ℓ b n) T E+(m/2)*domainTimeIntegral (halfspaceSmoothInner ℓ b n) T V ≤ _
  nlinarith

theorem halfspaceSmoothInner_uniform_heat_estimate {ι : Type*} [Fintype ι]
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ)
    (hbounded : Bornology.IsBounded {x | ∀ i, b i<ℓ i x})
    {W : Set (SpatialCoordinates d)} (hW : IsOpen W) (hne : W.Nonempty)
    (hWS : W ⊆ {x | ∀ i, b i<ℓ i x}) :
    ∃ (c : SpatialCoordinates d) (l β qc C : ℝ), c ∈ W ∧ 1 ≤ l ∧
      0 < β ∧ β ≤ 1 ∧ 1 ≤ qc ∧ 0 < C ∧
      (∀ x, -2 < interiorCarlemanProfile c l x ∧ interiorCarlemanProfile c l x ≤ -1) ∧
      ∀ n : ℕ, c ∈ halfspaceSmoothInner ℓ b n → ∀ T : ℝ, 0 ≤ T → ∀ q : ℝ → ℝ, ContDiff ℝ ∞ q → Function.Periodic q T →
      (∀ t ∈ Icc 0 T, qc ≤ q t) →
      (∀ t ∈ Icc 0 T, |deriv q t| ≤ β*(q t)^2) →
      (∀ t ∈ Icc 0 T, |deriv (deriv q) t| ≤ β^2*(q t)^3) →
      ∀ u : (ℝ × SpatialCoordinates d) → ℝ, ContDiff ℝ ∞ u → Function.Periodic u (T,0) →
      (∀ t : ℝ, ∀ x ∈ frontier (halfspaceSmoothInner ℓ b n), u (t,x)=0) →
      let L := interiorGaussianHeatPhase c l q
      domainTimeIntegral (halfspaceSmoothInner ℓ b n) T (fun tx => (q tx.1)^3*(Real.exp (L tx))^2*(u tx)^2)+
      domainTimeIntegral (halfspaceSmoothInner ℓ b n) T (fun tx =>
        q tx.1*(Real.exp (L tx))^2*‖gradient (fun y => u (tx.1,y)) tx.2‖^2) ≤
      C*(domainTimeIntegral (halfspaceSmoothInner ℓ b n) T (fun tx => (Real.exp (L tx)*spaceTimeHeat u tx)^2)+
        domainTimeIntegral (halfspaceSmoothInner ℓ b n) T ((Prod.snd ⁻¹' W).indicator
          (fun tx => (q tx.1)^3*(Real.exp (L tx))^2*(u tx)^2))) := by
  classical
  obtain ⟨c,l,β,qc,A₁,A₀,K,hc,hl,hβ,hβ1,hqc,hA₁,hA₀,hK,hobs⟩ :=
    halfspaceSmoothInner_uniform_heat_observation ℓ b hbounded hW hne hWS
  obtain ⟨H,hH,hreturn⟩ := interiorGaussianHeat_return_bound hbounded c l
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
  intro n hcn T hT q hq hqp hqmin hq' hq'' u hu hup hub
  have hb := (halfspaceSmoothInner_compact ℓ b hbounded n).isBounded.subset subset_closure
  have hS := (halfspaceSmoothInner_open ℓ b n).measurableSet
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
  have hEn : 0 ≤ domainTimeIntegral (halfspaceSmoothInner ℓ b n) T E := by
    apply domainTimeIntegral_nonneg_on _ hS T
    intro t ht x _
    exact mul_nonneg (hq0 t ht) (directionalEnergy_nonneg _ _ _)
  have hVn : 0 ≤ domainTimeIntegral (halfspaceSmoothInner ℓ b n) T V := by
    apply domainTimeIntegral_nonneg_on _ hS T
    intro t ht x _
    dsimp only [V]
    positivity [hq0 t ht]
  have hRn : 0 ≤ domainTimeIntegral (halfspaceSmoothInner ℓ b n) T R := by
    exact domainTimeIntegral_nonneg_on _ hS T (fun _ _ _ _ => sq_nonneg _)
  have hOn : 0 ≤ domainTimeIntegral (halfspaceSmoothInner ℓ b n) T O := by
    apply domainTimeIntegral_nonneg_on _ hS T
    intro t ht x _
    by_cases hx : x ∈ W
    · simp only [O,indicator_of_mem (show (t,x) ∈ Prod.snd ⁻¹' W from hx),V]
      positivity [hq0 t ht]
    · simp only [O,indicator_of_notMem (show (t,x) ∉ Prod.snd ⁻¹' W from hx),le_refl]
  have hint : domainTimeIntegral (halfspaceSmoothInner ℓ b n) T (fun tx => U₀ tx+U₁ tx) ≤
      domainTimeIntegral (halfspaceSmoothInner ℓ b n) T (fun tx => H*(E tx+V tx)) := by
    apply domainTimeIntegral_mono_on _ hS hb T (f := fun tx => U₀ tx+U₁ tx)
      (g := fun tx => H*(E tx+V tx)) (hU₀.add hU₁) (continuous_const.mul (hE.add hV))
    intro t ht x hx
    exact hreturn q hq u hu t (hq0 t ht) x (halfspaceExpSum_le_half_mem ℓ b n (show halfspaceExpSum ℓ b n x≤1/2 from hx.le))
  rw [domainTimeIntegral_add _ hb T hU₀ hU₁,domainTimeIntegral_const_mul,
    domainTimeIntegral_add _ hb T hE hV] at hint
  have ho := hobs n hcn T hT q hq hqp hqmin hq' hq'' u hu hup hub
  change A₁*domainTimeIntegral (halfspaceSmoothInner ℓ b n) T E+A₀*domainTimeIntegral (halfspaceSmoothInner ℓ b n) T V ≤
    (1/4:ℝ)*domainTimeIntegral (halfspaceSmoothInner ℓ b n) T R+K*domainTimeIntegral (halfspaceSmoothInner ℓ b n) T O at ho
  have hnormal : domainTimeIntegral (halfspaceSmoothInner ℓ b n) T E+domainTimeIntegral (halfspaceSmoothInner ℓ b n) T V ≤
      D*(A₁*domainTimeIntegral (halfspaceSmoothInner ℓ b n) T E+A₀*domainTimeIntegral (halfspaceSmoothInner ℓ b n) T V) := by
    nlinarith [mul_le_mul_of_nonneg_right hD₁ hEn,mul_le_mul_of_nonneg_right hD₀ hVn]
  have hbound := mul_le_mul_of_nonneg_left ho (show 0 ≤ H*D by positivity)
  have hnormH := mul_le_mul_of_nonneg_left hnormal hH.le
  have hsurplus : 0 ≤ H*D*((K+3/4)*domainTimeIntegral (halfspaceSmoothInner ℓ b n) T R+domainTimeIntegral (halfspaceSmoothInner ℓ b n) T O) := by positivity
  have hVU : V=U₀ := by
    funext tx
    dsimp only [V,U₀,z]
    ring
  change domainTimeIntegral (halfspaceSmoothInner ℓ b n) T U₀+domainTimeIntegral (halfspaceSmoothInner ℓ b n) T U₁ ≤
    H*D*(1+K)*(domainTimeIntegral (halfspaceSmoothInner ℓ b n) T R+domainTimeIntegral (halfspaceSmoothInner ℓ b n) T ((Prod.snd ⁻¹' W).indicator U₀))
  rw [← hVU]
  change domainTimeIntegral (halfspaceSmoothInner ℓ b n) T V+domainTimeIntegral (halfspaceSmoothInner ℓ b n) T U₁ ≤
    H*D*(1+K)*(domainTimeIntegral (halfspaceSmoothInner ℓ b n) T R+domainTimeIntegral (halfspaceSmoothInner ℓ b n) T O)
  rw [← hVU] at hint
  nlinarith

theorem halfspaceSmoothInner_uniform_heat_both_signs {ι : Type*} [Fintype ι]
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ)
    (hbounded : Bornology.IsBounded {x | ∀ i, b i<ℓ i x})
    {W : Set (SpatialCoordinates d)} (hW : IsOpen W) (hne : W.Nonempty)
    (hWS : W ⊆ {x | ∀ i, b i<ℓ i x}) :
    ∃ (c : SpatialCoordinates d) (l β qc C : ℝ), c ∈ W ∧ 1 ≤ l ∧
      0 < β ∧ β ≤ 1 ∧ 1 ≤ qc ∧ 0 < C ∧
      (∀ x, -2 < interiorCarlemanProfile c l x ∧ interiorCarlemanProfile c l x ≤ -1) ∧
      ∀ kidx : ℕ, c ∈ halfspaceSmoothInner ℓ b kidx → ∀ T : ℝ, 0 ≤ T → ∀ q : ℝ → ℝ, ContDiff ℝ ∞ q → Function.Periodic q T →
      (∀ t ∈ Icc 0 T, qc ≤ q t) →
      (∀ t ∈ Icc 0 T, |deriv q t| ≤ β*(q t)^2) →
      (∀ t ∈ Icc 0 T, |deriv (deriv q) t| ≤ β^2*(q t)^3) →
      ∀ ε : ℝ, (ε=1 ∨ ε=-1) →
      ∀ u : (ℝ × SpatialCoordinates d) → ℝ, ContDiff ℝ ∞ u → Function.Periodic u (T,0) →
      (∀ t : ℝ, ∀ x ∈ frontier (halfspaceSmoothInner ℓ b kidx), u (t,x)=0) →
      let L := interiorGaussianHeatPhase c l q
      domainTimeIntegral (halfspaceSmoothInner ℓ b kidx) T (fun tx => (q tx.1)^3*(Real.exp (L tx))^2*(u tx)^2)+
      domainTimeIntegral (halfspaceSmoothInner ℓ b kidx) T (fun tx =>
        q tx.1*(Real.exp (L tx))^2*‖gradient (fun y => u (tx.1,y)) tx.2‖^2) ≤
      C*(domainTimeIntegral (halfspaceSmoothInner ℓ b kidx) T (fun tx => (Real.exp (L tx)*spaceTimeOrientedHeat ε u tx)^2)+
        domainTimeIntegral (halfspaceSmoothInner ℓ b kidx) T ((Prod.snd ⁻¹' W).indicator
          (fun tx => (q tx.1)^3*(Real.exp (L tx))^2*(u tx)^2))) := by
  obtain ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,hforward⟩ :=
    halfspaceSmoothInner_uniform_heat_estimate ℓ b hbounded hW hne hWS
  refine ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,?_⟩
  intro kidx hck T hT q hq hqp hqmin hq' hq'' ε hε u hu hup hub
  rcases hε with rfl | rfl
  · simpa only [spaceTimeOrientedHeat,one_mul,spaceTimeHeat] using
      hforward kidx hck T hT q hq hqp hqmin hq' hq'' u hu hup hub
  · have hqr : ContDiff ℝ ∞ (fun t => q (T-t)) := hq.comp (contDiff_const.sub contDiff_id)
    have hur : ContDiff ℝ ∞ (fun tx => u (heatTimeReflection T tx)) :=
      hu.comp (heatTimeReflection_contDiff T)
    have hminr : ∀ t ∈ Icc 0 T, qc ≤ q (T-t) := fun t ht => hqmin (T-t) (time_reflection_mem_interval ht)
    have hq1r : ∀ t ∈ Icc 0 T, |deriv (fun s => q (T-s)) t| ≤ β*(q (T-t))^2 := by
      intro t ht
      rw [deriv_time_reflection hq,abs_neg]
      exact hq' (T-t) (time_reflection_mem_interval ht)
    have hq2r : ∀ t ∈ Icc 0 T, |deriv (deriv (fun s => q (T-s))) t| ≤ β^2*(q (T-t))^3 := by
      intro t ht
      rw [deriv_deriv_time_reflection hq]
      exact hq'' (T-t) (time_reflection_mem_interval ht)
    have hback := hforward kidx hck T hT (fun t => q (T-t)) hqr (hqp.const_sub T) hminr hq1r hq2r
      (fun tx => u (heatTimeReflection T tx)) hur (heatTimeReflection_periodic hup)
      (fun t x hx => hub (T-t) x hx)
    dsimp only at hback ⊢
    rw [spaceTimeHeat_time_reflection_eq hu T] at hback
    let L := interiorGaussianHeatPhase c l q
    let F₀ := fun tx => (q tx.1)^3*(Real.exp (L tx))^2*(u tx)^2
    let F₁ := fun tx => q tx.1*(Real.exp (L tx))^2*‖gradient (fun y => u (tx.1,y)) tx.2‖^2
    let R := fun tx => (Real.exp (L tx)*spaceTimeOrientedHeat (-1) u tx)^2
    let O := (Prod.snd ⁻¹' W).indicator F₀
    change domainTimeIntegral (halfspaceSmoothInner ℓ b kidx) T (fun tx => F₀ (heatTimeReflection T tx))+
      domainTimeIntegral (halfspaceSmoothInner ℓ b kidx) T (fun tx => F₁ (heatTimeReflection T tx)) ≤
      C*(domainTimeIntegral (halfspaceSmoothInner ℓ b kidx) T (fun tx => R (heatTimeReflection T tx))+
        domainTimeIntegral (halfspaceSmoothInner ℓ b kidx) T (fun tx => O (heatTimeReflection T tx))) at hback
    simp only [domainTimeIntegral_reflection] at hback
    exact hback

end Carleman
